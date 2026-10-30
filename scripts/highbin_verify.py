#!/usr/bin/env python3
"""Reproduce HIGHBIN's individual-module and public-axiom checks.

Run from a checkout with the pinned toolchain and Mathlib cache installed:
    python scripts/highbin_verify.py core
    python scripts/highbin_verify.py mellin
    python scripts/highbin_verify.py actual
"""
import argparse
import hashlib
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


def audit(group, modules, declarations):
    for declaration in declarations:
        source = ROOT / declaration['source']
        if hashlib.sha256(source.read_bytes()).hexdigest() != declaration['source_sha256']:
            raise SystemExit('Stale declaration inventory: ' + str(source))
    lines = ['import ' + m for m in modules]
    lines += ['', 'set_option pp.universes true', 'set_option format.width 120',
              'set_option pp.maxSteps 1000000']
    for declaration in declarations:
        lines += ['#check @' + declaration['name'], '#print axioms ' + declaration['name']]
    source = OUT / f'Public{group.title()}Audit.lean'
    source.write_text('\n'.join(lines) + '\n')
    log = OUT / f'{group}-public-types-and-axioms.log'
    run(['lake', 'env', 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false', str(source)], log)
    text = log.read_text()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    rows = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        clean = re.sub(r'\.\{[^}]*\}', '', axioms)
        rows[name] = sorted({a.strip() for a in clean.split(',') if a.strip()})
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        rows[name] = []
    missing = {d['name'] for d in declarations} - rows.keys()
    if missing:
        raise SystemExit('Missing axiom reports: ' + repr(sorted(missing)))
    extra = {name: sorted(set(axioms) - allowed) for name, axioms in rows.items()
             if not set(axioms) <= allowed}
    (OUT / f'{group}-axioms.json').write_text(json.dumps(
        {'group': group, 'declarations': rows, 'beyond_standard_axioms': extra}, indent=2) + '\n')
    if group != 'actual' and extra:
        raise SystemExit(f'Unexpected transitive {group} axioms: ' + repr(extra))
    print(f'Checked {len(modules)} individual {group} modules and {len(declarations)} public declarations.')
    if extra:
        print(f'{len(extra)} actual declarations depend on additional upstream axioms/admissions; '
              f'see {group}-axioms.json. They are not admission-free proofs.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('group', choices=['core', 'mellin', 'actual'])
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    modules = json.loads((ROOT / f'docs/highbin/{args.group}_modules.json').read_text())
    declarations = json.loads(
        (ROOT / f'docs/highbin/{args.group}_public_declarations.json').read_text())
    targets = modules if args.group != 'actual' else [
        'HeckeSkeleton.HighBinSupport', 'HeckeSkeleton.HighBin']
    if args.group == 'actual':
        # A failure in a small analytic/algebraic prerequisite should not
        # wait behind the complete class-field-theory dependency build.
        core = json.loads((ROOT / 'docs/highbin/core_modules.json').read_text())
        run(['lake', '--fail-fast', 'build', *core], OUT / 'actual-core-build.log')
    # Once the small prerequisites pass, retain independent arithmetic
    # diagnostics in one build. The workflow's subprocess timeout still
    # preserves its log and all completed dependency builds.
    run(['lake', 'build', *targets], OUT / f'{args.group}-build.log')
    audit(args.group, modules, declarations)


if __name__ == '__main__':
    main()
