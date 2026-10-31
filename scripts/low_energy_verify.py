#!/usr/bin/env python3
"""Compile the LOW-REFLECTED-ENERGY sources sequentially and preserve an audit.

Run from the repository root after `lake exe cache get`:
    python3 scripts/low_energy_verify.py core
    python3 scripts/low_energy_verify.py actual
No synthetic modules, replacement declarations, or admitted dependencies are
created. The source roots are the roots declared by this repository's Lake files.
After an actual-phase failure, independent modules receive a bounded diagnostic
window. Failed dependencies and timeouts remain failures, never proof evidence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time
from lean_imports import imports as lean_imports, strip_comments
from low_energy_axioms import inspect_axiom_output

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'
LOG = ROOT / '.low-energy-verification'
CACHE_SCHEMA = 2
NATIVE_SCHEMA = 'native-lake-foundation-v1'
NATIVE_CATALOG_SHA256 = 'bc9f033a972d4133ce3ff3ffb9c0328cae42eafdc8d9e147d36e6a0166d5cf0c'
NATIVE_CONFIG_PATHS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
    'vendor/class-field-theory/lakefile.toml')
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
ACTUAL = ['ActualSymbols', 'WindowTuples', 'ActualRows', 'ActualReflection',
    'ActualRawHybrid', 'ActualFrozenCharges',
    'ActualReflectionReindex', 'ActualCommonMellinTail', 'ActualBlockEnergy',
    'ActualBlockReindex', 'ActualSourceReindex', 'ActualDyadicReflection',
    'ActualRowFibres', 'ActualFrozenStateCount',
    'ActualAnnularBlockEnergy',
    'ActualFrozenAggregation', 'ActualFrozenReconstruction',
    'TargetDictionary', 'TargetGaussian', 'TargetSieveDictionary',
    'ActualMarkedTupleEnergy', 'ActualTupleReconstruction',
    'ActualResidualDyadicEnergy', 'ActualCompleteIdealEnergy',
    'ActualCompletedMarkedEnergy', 'InactiveWindows']


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


def discard_artifacts(module):
    """A failed or skipped module must never leave a usable stale output."""
    base = OUT / Path(*module.split('.'))
    for suffix in ARTIFACT_SUFFIXES:
        base.with_name(base.name + suffix).unlink(missing_ok=True)


def load_native_foundation(version):
    """Load a separate, fail-closed receipt for revalidated old dependencies.

    This is not a direct-compiler schema-2 record. The original native Lake
    traces must have passed a rehashing, no-build validation before this receipt
    can exist. Each module's current bytes and dependency bytes are checked
    again below; new proof sources and Principal are never admitted this way.
    """
    receipt = LOG / 'native_foundation.json'
    if not receipt.is_file():
        return None
    try:
        data = json.loads(receipt.read_text())
        if not isinstance(data, dict):
            return None
        catalog_bytes = (ROOT / 'docs/low-energy/native_foundation_catalog.json').read_bytes()
        catalog = json.loads(catalog_bytes)
        if not isinstance(catalog, dict):
            return None
        validation = data['validation']
        command = validation['command']
        if not (data.get('schema') == NATIVE_SCHEMA
                and data.get('status') == 'validated_native_dependencies'
                and data.get('lean') == version and data.get('mathlib') == MATHLIB_REV
                and set(data['config_sha256']) == set(NATIVE_CONFIG_PATHS)
                and all(data['config_sha256'][path] == hashlib.sha256(
                    (ROOT / path).read_bytes()).hexdigest() for path in NATIVE_CONFIG_PATHS)
                and data['catalog_sha256'] == hashlib.sha256(catalog_bytes).hexdigest()
                    == NATIVE_CATALOG_SHA256
                and catalog.get('schema') == 'native-lake-foundation-catalog-v1'
                and catalog.get('lean') == data['lean']
                and catalog.get('mathlib') == data['mathlib']
                and catalog.get('config_sha256') == data['config_sha256']
                and isinstance(catalog.get('modules'), dict)
                and type(validation['exit_code']) is int and validation['exit_code'] == 0
                and validation['log_file'] == 'native_foundation_validation.log'
                and validation['log_sha256'] == hashlib.sha256(
                    (LOG / validation['log_file']).read_bytes()).hexdigest()
                and isinstance(command, list) and len(command) > 5
                and command[:5] == ['lake', '--rehash', '--no-cache', '--no-build', 'build']
                and all(isinstance(arg, str) and re.fullmatch(
                    r'\+[A-Za-z_][A-Za-z0-9_.]*:olean', arg) for arg in command[5:])
                and isinstance(data['modules'], dict)):
            return None
        covered, visiting = set(), set()

        def covered_by_validation(module):
            if module in covered:
                return True
            if module in visiting:
                return False
            entry = data['modules'][module]
            pinned = catalog['modules'][module]
            found = resolve(module)
            if found is None:
                return False
            source, _ = found
            if (str(source.relative_to(ROOT)) != entry['source'] or
                    entry['source'] != pinned['source'] or
                    hashlib.sha256(source.read_bytes()).hexdigest() != entry['source_sha256'] or
                    entry['source_sha256'] != pinned['source_sha256']):
                return False
            visiting.add(module)
            for dependency in imports(source):
                if resolve(dependency) is not None and not covered_by_validation(dependency):
                    return False
            visiting.remove(module)
            covered.add(module)
            return True

        if (not all(covered_by_validation(arg[1:-len(':olean')]) for arg in command[5:]) or
                covered != set(data['modules'])):
            return None
        return {**data, '_catalog_modules': catalog['modules']}
    except (KeyError, TypeError, ValueError, OSError):
        return None


def native_module_record(data, module, relative_source, source_digest,
        dependency_artifacts, is_new_source):
    """Validate current observations without relabelling a native build."""
    if data is None or is_new_source or module == 'HeckeSkeleton.Principal':
        return None
    try:
        entry = data['modules'][module]
        pinned = data['_catalog_modules'][module]
        if not isinstance(pinned['artifacts'], dict):
            return None
        expected_outputs = {suffix: artifact['sha256']
            for suffix, artifact in pinned['artifacts'].items() if suffix in ARTIFACT_SUFFIXES}
        if not (entry['source'] == relative_source == pinned['source']
                and entry['source_sha256'] == source_digest == pinned['source_sha256']
                and entry['artifact_id'] == pinned['artifact_id']
                and '.olean' in expected_outputs
                and entry['validated_dependency_artifact_hashes'] == dependency_artifacts
                and entry['output_artifact_hashes'] == expected_outputs == artifact_hashes(module)):
            return None
        return {'module': module, 'source': relative_source,
            'source_sha256': source_digest, 'new_source': False,
            'status': 'validated_native_dependency', 'reused_native_foundation': True,
            'native_schema': NATIVE_SCHEMA, 'native_artifact_id': entry['artifact_id'],
            'lean': data['lean'], 'mathlib': data['mathlib'],
            'config_sha256': data['config_sha256'],
            'catalog_sha256': data['catalog_sha256'],
            'native_validation': {
                'receipt': 'native_foundation.json',
                'log_file': data['validation']['log_file'],
                'log_sha256': data['validation']['log_sha256'],
                'command_sha256': hashlib.sha256(json.dumps(
                    data['validation']['command'], separators=(',', ':')).encode()).hexdigest()},
            'validated_dependency_artifact_hashes': dependency_artifacts,
            'output_artifact_hashes': entry['output_artifact_hashes']}
    except (KeyError, TypeError, ValueError, OSError, RuntimeError):
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('phase', choices=['core', 'actual'])
    ap.add_argument('--direct-env', action='store_true',
        help='Use the explicitly supplied PATH and LEAN_PATH instead of asking Lake for them.')
    ap.add_argument('--target', action='append', default=[],
        help='Compile this exact module closure only; does not claim the full phase passed.')
    ap.add_argument('--diagnostic-seconds', type=float, default=120.0,
        help='Actual phase only: continue independent modules this long after the first failure.')
    args = ap.parse_args()
    if not math.isfinite(args.diagnostic_seconds) or args.diagnostic_seconds < 0:
        ap.error('--diagnostic-seconds must be a finite nonnegative number')
    diagnostic_seconds = args.diagnostic_seconds if args.phase == 'actual' else 0.0
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        raise SystemExit('Unexpected Lean toolchain; refusing an incomparable audit.')
    OUT.mkdir(parents=True, exist_ok=True)
    LOG.mkdir(exist_ok=True)
    if args.phase == 'actual':
        # A prior target audit must not survive an interrupted or failed replay
        # as though it belonged to the current verification attempt.
        for suffix in ('.lean', '.json', '.log'):
            (LOG / ('CompletedMarkedEnergyAudit' + suffix)).unlink(missing_ok=True)
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
    if args.target:
        targets = args.target
    env = os.environ.copy()
    if args.direct_env:
        if not env.get('LEAN_PATH'):
            ap.error('--direct-env requires a nonempty LEAN_PATH')
    else:
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
    if 'version 4.35.0-rc3,' not in version:
        raise RuntimeError('Unexpected Lean executable version: ' + version)
    flags = ['-j1', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
    lake_manifest = ROOT / 'lake-manifest.json'
    package_lock = hashlib.sha256(lake_manifest.read_bytes()).hexdigest()
    packages = json.loads(lake_manifest.read_text()).get('packages', [])
    mathlib = next((p for p in packages if p.get('name') == 'mathlib'), None)
    if not mathlib or mathlib.get('rev') != MATHLIB_REV:
        raise RuntimeError('Unexpected Mathlib revision in lake-manifest.json.')
    manifest = json.loads((ROOT / 'docs/low-energy/source_manifest.json').read_text())
    new_sources = {entry['path'] for entry in manifest['files']}
    native_foundation = load_native_foundation(version)
    records = []
    blocked = set()
    failures = []
    skipped = []
    diagnostic_deadline = None
    failure_code = 0

    def save_diagnostics(gate_status=None):
        (LOG / (args.phase + '_diagnostics.json')).write_text(json.dumps({
            'phase': args.phase, 'diagnostic_seconds': diagnostic_seconds,
            'first_failure': failures[0] if failures else None,
            'failed_modules': failures, 'skipped_modules': skipped,
            'budget_exhausted': diagnostic_deadline is not None and
                time.monotonic() >= diagnostic_deadline,
            'final_axiom_gate': gate_status or (
                'not_run_due_to_failed_or_skipped_modules'
                if failures or skipped else 'not_reached'),
        }, indent=2) + '\n')

    save_diagnostics(gate_status='not_started')

    def record_skip(module, source, reason, dependencies):
        discard_artifacts(module)
        blocked.add(module)
        entry = {'module': module, 'reason': reason,
            'blocked_dependencies': dependencies}
        skipped.append(entry)
        output = 'SKIPPED ' + module + ': ' + reason
        if dependencies:
            output += ': ' + ', '.join(dependencies)
        output += '\n'
        record = {'module': module, 'source': str(source.relative_to(ROOT)),
            'cache_schema': CACHE_SCHEMA,
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'lean': version, 'flags': flags, 'mathlib': MATHLIB_REV,
            'new_source': str(source.relative_to(ROOT)) in new_sources,
            'package_lock_sha256': package_lock,
            'status': 'skipped', 'skip_reason': reason,
            'blocked_dependencies': dependencies,
            'exit_code': None, 'audit_ok': False,
            'output_artifact_hashes': {},
            'log_sha256': hashlib.sha256(output.encode()).hexdigest()}
        (LOG / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        (LOG / (module + '.log')).write_text(output)
        records.append(record)

    for module, source, source_root in order:
        dependencies = imports(source)
        blocked_dependencies = [dependency for dependency in dependencies if dependency in blocked]
        if blocked_dependencies:
            record_skip(module, source, 'failed_or_skipped_dependency', blocked_dependencies)
            continue
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
            for dependency in dependencies if resolve(dependency) is not None}
        stamp = LOG / (module + '.json')
        log_path = LOG / (module + '.log')
        previous = None
        if stamp.is_file() and target.is_file() and log_path.is_file():
            try:
                previous = json.loads(stamp.read_text())
            except (ValueError, OSError):
                previous = None
        cached_axiom_audit = (inspect_axiom_output(log_path.read_text())
            if is_new_source and previous is not None else None)
        if (previous is not None and previous.get('cache_schema') == CACHE_SCHEMA
            and previous.get('source_sha256') == source_digest
            and previous.get('exit_code') == 0 and previous.get('audit_ok') is True
            and previous.get('lean') == version and previous.get('flags') == flags
            and previous.get('mathlib') == MATHLIB_REV
            and previous.get('package_lock_sha256') == package_lock
            and previous.get('new_source') == is_new_source
            and previous.get('local_dependency_artifact_hashes') == dependency_artifacts
            and previous.get('output_artifact_hashes') == artifact_hashes(module)
            and previous.get('log_sha256') == hashlib.sha256(log_path.read_bytes()).hexdigest()
            and (not is_new_source or cached_axiom_audit['ok'])):
            print('CACHED EXACT ' + module, flush=True)
            print(log_path.read_text(), flush=True)
            records.append({**previous, 'reused_exact_cache': True,
                'printed_axiom_audit': cached_axiom_audit})
            (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
            continue
        native = native_module_record(native_foundation, module, relative_source,
            source_digest, dependency_artifacts, is_new_source)
        if native is not None:
            print('NATIVE VALIDATED DEPENDENCY ' + module, flush=True)
            # Keep the native provenance visibly distinct from a compiler exit
            # record; no fabricated flags, exit code or axiom audit is supplied.
            records.append(native)
            (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
            continue
        # The budget limits new compiler work.  An independent, exact cache
        # remains valid after it expires and must not be erased merely because
        # another module failed.  Failed dependencies were rejected above.
        if diagnostic_deadline is not None and time.monotonic() >= diagnostic_deadline:
            record_skip(module, source, 'diagnostic_budget_exhausted', [])
            continue
        if module == 'HeckeSkeleton.Principal':
            print('INTEGRATION GATE HeckeSkeleton.Principal', flush=True)
        print('BUILD ' + module, flush=True)
        discard_artifacts(module)
        started = time.monotonic()
        command = ['lean', *flags, '-R', str(source_root),
            '-o', str(target), str(source)]
        timed_out = False
        try:
            proc = subprocess.run(command, cwd=ROOT, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                timeout=None if diagnostic_deadline is None else
                    max(0.001, diagnostic_deadline - started))
        except subprocess.TimeoutExpired as error:
            timed_out = True
            output = error.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
            proc = subprocess.CompletedProcess(command, 124, stdout=output +
                '\nDIAGNOSTIC BUDGET EXPIRED: compilation was stopped; no proof result.\n')
        printed_axiom_audit = inspect_axiom_output(proc.stdout) if is_new_source else None
        audit_ok = proc.returncode == 0 and not (is_new_source and
            ('sorryAx' in proc.stdout or "declaration uses 'sorry'" in proc.stdout
                or not printed_axiom_audit['ok']))
        if not audit_ok:
            discard_artifacts(module)
        record = {'module': module, 'source': relative_source,
            'cache_schema': CACHE_SCHEMA, 'source_sha256': source_digest,
            'exit_code': proc.returncode, 'seconds': round(time.monotonic()-started, 3),
            'lean': version, 'flags': flags,
            'new_source': is_new_source,
            'package_lock_sha256': package_lock,
            'local_dependency_artifact_hashes': dependency_artifacts,
            'output_artifact_hashes': artifact_hashes(module) if audit_ok else {},
            'audit_ok': audit_ok, 'diagnostic_timeout': timed_out,
            'printed_axiom_audit': printed_axiom_audit,
            'log_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
            'local_dependency_hashes': {
                dependency: hashlib.sha256(artifact.read_bytes()).hexdigest()
                for dependency in dependencies
                if (artifact := OUT / Path(*dependency.split('.')).with_suffix('.olean')).is_file()
            },
            'mathlib': MATHLIB_REV}
        (LOG / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        (LOG / (module + '.log')).write_text(proc.stdout)
        records.append(record)
        (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
        print(proc.stdout, flush=True)
        if not audit_ok:
            blocked.add(module)
            reason = ('diagnostic_timeout' if timed_out else
                'compiler_error' if proc.returncode else 'disallowed_or_malformed_axiom_audit')
            failures.append({'module': module, 'exit_code': proc.returncode or 1,
                'reason': reason})
            if not failure_code:
                failure_code = proc.returncode or 1
                diagnostic_deadline = time.monotonic() + diagnostic_seconds
            save_diagnostics()
            if args.phase == 'core' or diagnostic_seconds == 0:
                return failure_code
            print('FAILED ' + module + '; continuing only independent modules within ' +
                'the diagnostic budget.', flush=True)
    (LOG / (args.phase + '.json')).write_text(json.dumps(records, indent=2) + '\n')
    if failures or skipped:
        save_diagnostics()
        print(f'FAIL: {len(failures)} failed, {len(skipped)} skipped; ' +
            'the final axiom gate was not run.', flush=True)
        return failure_code or 1
    if args.phase == 'actual' and not args.target:
        audit = LOG / 'CompletedMarkedEnergyAudit.lean'
        audit.write_text('import HeckeSkeleton.Principal\n\n' +
            '#print axioms HeckeSkeleton.completedMarkedEnergy\n')
        print('AXIOM GATE HeckeSkeleton.completedMarkedEnergy', flush=True)
        save_diagnostics(gate_status='running')
        started = time.monotonic()
        proc = subprocess.run(['lean', *flags, '-R', str(LOG), str(audit)],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        axiom_audit = inspect_axiom_output(proc.stdout,
            required=['HeckeSkeleton.completedMarkedEnergy'])
        audit_record = {'declaration': 'HeckeSkeleton.completedMarkedEnergy',
            'source_sha256': hashlib.sha256(audit.read_bytes()).hexdigest(),
            'principal_source_sha256': hashlib.sha256(
                (ROOT / 'HeckeSkeleton/Principal.lean').read_bytes()).hexdigest(),
            'exit_code': proc.returncode, 'seconds': round(time.monotonic()-started, 3),
            'lean': version, 'flags': flags, 'mentions_sorryAx': 'sorryAx' in proc.stdout,
            'printed_axiom_audit': axiom_audit,
            'audit_ok': proc.returncode == 0 and axiom_audit['ok'],
            'log_sha256': hashlib.sha256(proc.stdout.encode()).hexdigest(),
            'scope': 'The conditional completedMarkedEnergy theorem, with the original two sieves.'}
        (LOG / 'CompletedMarkedEnergyAudit.json').write_text(
            json.dumps(audit_record, indent=2) + '\n')
        (LOG / 'CompletedMarkedEnergyAudit.log').write_text(proc.stdout)
        print(proc.stdout, flush=True)
        if proc.returncode:
            save_diagnostics(gate_status='failed_compiler')
            return proc.returncode
        if not axiom_audit['ok']:
            save_diagnostics(gate_status='failed_axiom_audit')
            raise RuntimeError('The replacement completedMarkedEnergy failed its strict axiom audit: ' +
                '; '.join(axiom_audit['errors']))
        save_diagnostics(gate_status='passed')
    else:
        save_diagnostics(gate_status='not_run_targeted_closure' if args.target else
            'not_applicable_core_phase')
    scope = 'targeted closure ' + ', '.join(args.target) if args.target else args.phase
    print(f'PASS: {len(order)} real source modules in {scope}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
