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
from lean_imports import imports as lean_imports, strip_comments

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'
LOG = ROOT / '.low-energy-verification'
CACHE_SCHEMA = 2
MATHLIB_REV = '0493595ecd5da8ef14742febab99728f98e948e8'
ARTIFACT_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')
SOURCE_ROOTS = [ROOT, ROOT / 'vendor/class-field-theory/Lean4',
    ROOT / 'vendor/flt', ROOT / 'vendor/tauceti', ROOT / 'vendor/zeta23',
    ROOT / 'vendor/openai', ROOT / 'SkeletonInputs', ROOT / 'GramCoreInputs',
    ROOT / 'GramAssemblyInputs', ROOT / 'Challenge', ROOT / 'Solution']

CORE = ['RawIdealHybrid', 'HybridScaling', 'MellinHybrid',
    'FiniteHybridIntegral', 'LocalWeylTableCore', 'FrozenChargeCore',
    'IdealRows', 'IdealRankin', 'IdealSupportPowers', 'PowerfulRowAssembly',
    'PhysicalBlockPolynomial', 'PhysicalDyadicBudget', 'GaussianEnergyAssembly',
    'DyadicReindex', 'SlotTuples', 'InactiveCore', 'PhysicalGaussianEnergy']
ACTUAL = ['ActualSymbols', 'ActualRawHybrid', 'ActualFrozenCharges',
    'ActualReflectionReindex', 'ActualCommonMellinTail', 'ActualBlockEnergy',
    'ActualBlockReindex', 'ActualSourceReindex', 'ActualDyadicReflection',
    'ActualRows', 'ActualRowFibres', 'ActualFrozenStateCount',
    'WindowTuples', 'InactiveWindows', 'TargetDictionary', 'TargetGaussian',
    'TargetSieveDictionary', 'ActualAnnularBlockEnergy',
    'ActualFrozenAggregation', 'ActualFrozenReconstruction',
    'ActualMarkedTupleEnergy', 'ActualTupleReconstruction',
    'ActualResidualDyadicEnergy', 'ActualCompleteIdealEnergy',
    'ActualCompletedMarkedEnergy']


def imports(source):
    """Read Lean's import header, respecting nested comments."""
    return lean_imports(source.read_text())


def resolve(module):
    rel = Path(*module.split('.')).with_suffix('.lean')
    for root in SOURCE_ROOTS:
        path = root / rel
        if path.is_file():
            return path, root
    return None


def artifact_hashes(module):
    base = OUT / Path(*module.split('.'))
    result = {}
    for suffix in ARTIFACT_SUFFIXES:
        path = base.with_name(base.name + suffix)
        if path.is_file():
            result[suffix] = hashlib.sha256(path.read_bytes()).hexdigest()
    if '.olean' not in result:
        raise RuntimeError('Missing compiled local dependency: ' + module)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('phase', choices=['core', 'actual'])
    args = ap.parse_args()
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        raise SystemExit('Unexpected Lean toolchain; refusing an incomparable audit.')
    OUT.mkdir(parents=True, exist_ok=True)
    LOG.mkdir(exist_ok=True)
    selected = CORE if args.phase == 'core' else ACTUAL
    targets = ['HeckeSkeleton.LowEnergy.' + m for m in selected]
    if args.phase == 'core':
        targets += ['HeckeSkeleton.LowFrozenCube.Valuations',
            'HeckeSkeleton.LowFrozenCube.LocalCoefficients']
    if args.phase == 'actual':
        # The original file is an integration gate. Its pre-existing unrelated
        # admissions are not treated as new-source admissions; the particular
        # replacement theorem receives a separate transitive axiom audit below.
        targets.append('HeckeSkeleton.Principal')
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
    lake_manifest = ROOT / 'lake-manifest.json'
    package_lock = hashlib.sha256(lake_manifest.read_bytes()).hexdigest()
    packages = json.loads(lake_manifest.read_text()).get('packages', [])
    mathlib = next((p for p in packages if p.get('name') == 'mathlib'), None)
    if not mathlib or mathlib.get('rev') != MATHLIB_REV:
        raise RuntimeError('Unexpected Mathlib revision in lake-manifest.json.')
    manifest = json.loads((ROOT / 'docs/low-energy/source_manifest.json').read_text())
    new_sources = {entry['path'] for entry in manifest['files']}
    records = []
    for module, source, source_root in order:
        target = OUT / Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        relative_source = str(source.relative_to(ROOT))
        is_new_source = relative_source in new_sources
        if is_new_source:
            forbidden = sorted(set(re.findall(
                r'\b(sorry|axiom|admit|native_decide)\b', strip_comments(source.read_text()))))
            if forbidden:
                raise RuntimeError('Forbidden new-source declaration in ' + module + ': ' +
                    ', '.join(forbidden))
        source_digest = hashlib.sha256(source.read_bytes()).hexdigest()
        dependency_artifacts = {dependency: artifact_hashes(dependency)
            for dependency in imports(source) if resolve(dependency) is not None}
        stamp = LOG / (module + '.json')
        log_path = LOG / (module + '.log')
        previous = None
        if stamp.is_file() and target.is_file() and log_path.is_file():
            try:
                previous = json.loads(stamp.read_text())
            except (ValueError, OSError):
                previous = None
        if (previous is not None and previous.get('cache_schema') == CACHE_SCHEMA
            and previous.get('source_sha256') == source_digest
            and previous.get('exit_code') == 0 and previous.get('audit_ok') is True
            and previous.get('lean') == version and previous.get('flags') == flags
            and previous.get('mathlib') == MATHLIB_REV
            and previous.get('package_lock_sha256') == package_lock
            and previous.get('new_source') == is_new_source
            and previous.get('local_dependency_artifact_hashes') == dependency_artifacts
            and previous.get('output_artifact_hashes') == artifact_hashes(module)
            and previous.get('log_sha256') == hashlib.sha256(log_path.read_bytes()).hexdigest()):
            print('CACHED EXACT ' + module, flush=True)
            print(log_path.read_text(), flush=True)
            records.append({**previous, 'reused_exact_cache': True})
            (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
            continue
        if module == 'HeckeSkeleton.Principal':
            print('INTEGRATION GATE HeckeSkeleton.Principal', flush=True)
        print('BUILD ' + module, flush=True)
        started = time.monotonic()
        proc = subprocess.run(['lean', *flags, '-R', str(source_root),
            '-o', str(target), str(source)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        record = {'module': module, 'source': relative_source,
            'cache_schema': CACHE_SCHEMA, 'source_sha256': source_digest,
            'exit_code': proc.returncode, 'seconds': round(time.monotonic()-started, 3),
            'lean': version, 'flags': flags,
            'new_source': is_new_source,
            'package_lock_sha256': package_lock,
            'local_dependency_artifact_hashes': dependency_artifacts,
            'output_artifact_hashes': artifact_hashes(module) if proc.returncode == 0 else {},
            'audit_ok': proc.returncode == 0 and not (is_new_source and
                ('sorryAx' in proc.stdout or "declaration uses 'sorry'" in proc.stdout)),
            'log_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
            'local_dependency_hashes': {
                dependency: hashlib.sha256(artifact.read_bytes()).hexdigest()
                for dependency in imports(source)
                if (artifact := OUT / Path(*dependency.split('.')).with_suffix('.olean')).is_file()
            },
            'mathlib': MATHLIB_REV}
        (LOG / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        (LOG / (module + '.log')).write_text(proc.stdout)
        records.append(record)
        (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
        print(proc.stdout, flush=True)
        if proc.returncode:
            return proc.returncode
        if is_new_source:
            if 'sorryAx' in proc.stdout or "declaration uses 'sorry'" in proc.stdout:
                raise RuntimeError('An admitted dependency appeared in a new proof audit: ' + module)
    if args.phase == 'actual':
        audit = LOG / 'CompletedMarkedEnergyAudit.lean'
        audit.write_text('import HeckeSkeleton.Principal\n\n' +
            '#print axioms HeckeSkeleton.completedMarkedEnergy\n')
        print('AXIOM GATE HeckeSkeleton.completedMarkedEnergy', flush=True)
        started = time.monotonic()
        proc = subprocess.run(['lean', *flags, '-R', str(LOG), str(audit)],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        audit_record = {'declaration': 'HeckeSkeleton.completedMarkedEnergy',
            'source_sha256': hashlib.sha256(audit.read_bytes()).hexdigest(),
            'principal_source_sha256': hashlib.sha256(
                (ROOT / 'HeckeSkeleton/Principal.lean').read_bytes()).hexdigest(),
            'exit_code': proc.returncode, 'seconds': round(time.monotonic()-started, 3),
            'lean': version, 'flags': flags, 'mentions_sorryAx': 'sorryAx' in proc.stdout,
            'scope': 'The conditional completedMarkedEnergy theorem, with the original two sieves.'}
        (LOG / 'CompletedMarkedEnergyAudit.json').write_text(
            json.dumps(audit_record, indent=2) + '\n')
        (LOG / 'CompletedMarkedEnergyAudit.log').write_text(proc.stdout)
        print(proc.stdout, flush=True)
        if proc.returncode:
            return proc.returncode
        if 'sorryAx' in proc.stdout:
            raise RuntimeError('The replacement completedMarkedEnergy still has an admitted dependency.')
    print(f'PASS: {len(order)} real source modules in {args.phase}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
