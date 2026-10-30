#!/usr/bin/env python3
"""Compile the LOW-REFLECTED-ENERGY sources sequentially and preserve an audit.

Run from the repository root after `lake exe cache get`:
    python3 scripts/low_energy_verify.py core
    python3 scripts/low_energy_verify.py actual
No synthetic modules, replacement declarations, or admitted dependencies are
created. The source roots are the roots declared by this repository's Lake files.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'
LOG = ROOT / '.low-energy-verification'
SOURCE_ROOTS = [ROOT, ROOT / 'vendor/class-field-theory/Lean4',
    ROOT / 'vendor/flt', ROOT / 'vendor/tauceti', ROOT / 'vendor/zeta23',
    ROOT / 'vendor/openai', ROOT / 'SkeletonInputs', ROOT / 'GramCoreInputs',
    ROOT / 'GramAssemblyInputs', ROOT / 'Challenge', ROOT / 'Solution']

CORE = ['RawIdealHybrid', 'HybridScaling', 'MellinHybrid',
    'FiniteHybridIntegral', 'LocalWeylTableCore', 'FrozenChargeCore',
    'IdealRows', 'IdealRankin', 'IdealSupportPowers', 'PowerfulRowAssembly',
    'PhysicalBlockPolynomial', 'PhysicalDyadicBudget', 'GaussianEnergyAssembly',
    'DyadicReindex', 'SlotTuples', 'InactiveCore']
ACTUAL = ['ActualSymbols', 'ActualRawHybrid', 'ActualFrozenCharges',
    'ActualReflectionReindex', 'ActualCommonMellinTail', 'ActualBlockEnergy',
    'ActualBlockReindex', 'ActualSourceReindex', 'ActualDyadicReflection',
    'ActualRows', 'ActualRowFibres', 'ActualFrozenStateCount',
    'WindowTuples', 'InactiveWindows', 'TargetDictionary', 'TargetGaussian',
    'TargetSieveDictionary']


def imports(source):
    """Read Lean's import header, respecting nested comments."""
    text = source.read_text()
    depth = 0
    lines = []
    for line in text.splitlines():
        clean = []
        i = 0
        while i < len(line):
            if line.startswith('/-', i):
                depth += 1
                i += 2
            elif depth and line.startswith('-/', i):
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif line.startswith('--', i):
                break
            else:
                clean.append(line[i])
                i += 1
        s = ''.join(clean).strip()
        if not s or s == 'module' or s.startswith('prelude'):
            continue
        m = re.match(r'^(?:(?:public|private|meta)\s+)*import\s+(.+)$', s)
        if not m:
            break
        lines.extend(m.group(1).split())
    return lines


def resolve(module):
    rel = Path(*module.split('.')).with_suffix('.lean')
    for root in SOURCE_ROOTS:
        path = root / rel
        if path.is_file():
            return path, root
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('phase', choices=['core', 'actual'])
    args = ap.parse_args()
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        raise SystemExit('Unexpected Lean toolchain; refusing an incomparable audit.')
    OUT.mkdir(parents=True, exist_ok=True)
    LOG.mkdir(exist_ok=True)
    selected = CORE if args.phase == 'core' else ACTUAL
    optional = ['PhysicalGaussianEnergy'] if args.phase == 'core' else ['ActualAnnularBlockEnergy']
    selected += [m for m in optional if resolve('HeckeSkeleton.LowEnergy.' + m)]
    targets = ['HeckeSkeleton.LowEnergy.' + m for m in selected]
    env = os.environ.copy()
    lake_env = json.loads(subprocess.check_output([
        'lake', 'env', 'python3', '-c',
        'import os,json;print(json.dumps({k:os.environ.get(k, "") for k in ["PATH","LEAN_PATH","LEAN_SRC_PATH"]}))'
    ], cwd=ROOT, text=True).strip().splitlines()[-1])
    env.update(lake_env)
    env['LEAN_PATH'] = str(OUT) + os.pathsep + env.get('LEAN_PATH', '')
    paths = [Path(p) if Path(p).is_absolute() else ROOT / p
        for p in env['LEAN_PATH'].split(os.pathsep) if p]
    seen = set()
    order = []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        found = resolve(module)
        if found is None:
            if module in {'Init', 'Lean', 'Std'} or module.startswith(('Init.', 'Lean.', 'Std.')):
                return
            rel = Path(*module.split('.')).with_suffix('.olean')
            if any((p / rel).is_file() for p in paths):
                return
            raise RuntimeError('Missing real source or compiled dependency: ' + module)
        source, source_root = found
        for dependency in imports(source):
            visit(dependency)
        order.append((module, source, source_root))

    for target in targets:
        visit(target)
    version = subprocess.check_output(['lean', '--version'], env=env, cwd=ROOT, text=True).strip()
    flags = ['-j1', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
    records = []
    for module, source, source_root in order:
        target = OUT / Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        print('BUILD ' + module, flush=True)
        started = time.monotonic()
        proc = subprocess.run(['lean', *flags, '-R', str(source_root),
            '-o', str(target), str(source)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        record = {'module': module, 'source': str(source.relative_to(ROOT)),
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'exit_code': proc.returncode, 'seconds': round(time.monotonic()-started, 3),
            'lean': version, 'flags': flags,
            'mathlib': '0493595ecd5da8ef14742febab99728f98e948e8'}
        (LOG / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        (LOG / (module + '.log')).write_text(proc.stdout)
        records.append(record)
        (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
        print(proc.stdout, flush=True)
        if proc.returncode:
            return proc.returncode
        if module.startswith(('HeckeSkeleton.LowEnergy.', 'HeckeSkeleton.LowFrozenCube.')):
            if 'sorryAx' in proc.stdout or "declaration uses 'sorry'" in proc.stdout:
                raise RuntimeError('An admitted dependency appeared in a new proof audit: ' + module)
    print(f'PASS: {len(order)} real source modules in {args.phase}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
