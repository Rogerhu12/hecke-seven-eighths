#!/usr/bin/env python3
"""Reproduce HIGHBIN's individual-module and public-axiom checks.

Run from a checkout with the pinned toolchain and Mathlib cache installed:
    python scripts/highbin_verify.py core
    python scripts/highbin_verify.py actual
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.highbin-verification'


def run(command, log):
    print('+ ' + ' '.join(command), flush=True)
    with log.open('w') as stream:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in proc.stdout:
            print(line, end='', flush=True)
            stream.write(line)
            stream.flush()
        code = proc.wait()
    if code:
        raise SystemExit(code)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('group', choices=['core', 'actual'])
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    if args.group == 'actual':
        run(['lake', 'build', 'HeckeSkeleton.HighBinSupport', 'HeckeSkeleton.HighBin'],
            OUT / 'actual-build.log')
        return
    modules = json.loads((ROOT / 'docs/highbin/core_modules.json').read_text())
    run(['lake', 'build', *modules], OUT / 'core-build.log')
    declarations = json.loads((ROOT / 'docs/highbin/core_public_declarations.json').read_text())
    lines = ['import ' + m for m in modules]
    lines += ['', 'set_option pp.universes true', 'set_option pp.width 120',
              'set_option pp.maxDepth 1000', 'set_option pp.maxSteps 1000000']
    for declaration in declarations:
        lines += ['#check @' + declaration['name'], '#print axioms ' + declaration['name']]
    audit = OUT / 'PublicCoreAudit.lean'
    audit.write_text('\n'.join(lines) + '\n')
    run(['lake', 'env', 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', str(audit)],
        OUT / 'core-public-types-and-axioms.log')
    text = (OUT / 'core-public-types-and-axioms.log').read_text()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for axioms in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text):
        actual = {a.strip() for a in axioms.split(',') if a.strip()}
        if not actual <= allowed:
            raise SystemExit('Unexpected transitive axioms: ' + repr(actual - allowed))
    print(f'Checked {len(modules)} individual modules and {len(declarations)} public declarations.')


if __name__ == '__main__':
    main()
