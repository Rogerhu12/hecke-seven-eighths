#!/usr/bin/env python3
"""Fresh LOW-REFLECTED-ENERGY builds using a pinned native Lake dependency cache.

This lane emits its own aggregate evidence. It never creates schema-2 module
receipts, accepts manual compiled checkpoints, or infers per-module exit codes.
Run ``prepare`` before toolchain/cache setup, then ``verify`` after the pinned
restore action. All declared new sources and Principal must build from source;
only old dependencies may replay their rehashed native Lake traces.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import signal
import subprocess
import sys
import threading
import time

from lean_imports import strip_comments
from low_energy_axioms import ALLOWED_AXIOMS, inspect_axiom_output

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / '.low-energy-lake-verification'
SCHEMA = 'low-energy-native-lake-verification-v1'
SOURCE_MANIFEST = 'docs/low-energy/source_manifest.json'
PRINCIPAL = 'HeckeSkeleton.Principal'
REQUIRED_AXIOMS = (
    'HeckeSkeleton.completedMarkedEnergy',
    'HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy.completedMarkedEnergy',
)
EXPECTED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
TOOLCHAIN = 'leanprover/lean4:v4.35.0-rc3'
LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
MATHLIB_REV = '0493595ecd5da8ef14742febab99728f98e948e8'
CACHE_TAG = 'lake-cache-76c696e'
CACHE_COMMIT = '76c696e20ee1f201a6507dde8b1d832a928ac71a'
CACHE_ACTION = '5f3c782680be2c74365b4d8e5760fc16f1f222c5'
CACHE_MANIFEST_SHA256 = '825bd312958ffe69c779a8f674d1d380a5cc3323049ec2d3fe31ba04a2113328'
CACHE_SUMS_SHA256 = 'cb851052b6f06e8799ed75fd1ce0b270dc888f9d43a509f081845ae9f56aaa2e'
CACHE_PART = 'lake-cache.tar.zst.part-000'
CACHE_PART_SHA256 = '2fcc28ecb8224ecd69e656692d79e976ce932bd5a5dd9135ed3ae5721aee636e'
CACHE_PART_BYTES = 1146434516
CACHE_BUILD_ROOTS = (
    '.lake/build', 'vendor/class-field-theory/.lake/build',
    '.lake/packages/TauCeti/.lake/build',
)
CONFIG_PATHS = (
    'lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
    'vendor/class-field-theory/lakefile.toml',
)
FORBIDDEN = re.compile(r'\b(sorry|axiom|admit|native_decide)\b')
RUNTIME_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def regular_bytes(path: Path) -> bytes:
    if path.is_symlink() or not path.is_file():
        raise RuntimeError('Expected a regular file: ' + str(path))
    return path.read_bytes()


def source_snapshot(root: Path) -> dict:
    """Check the reviewed manifest's current fields, never its history."""
    manifest_bytes = regular_bytes(root / SOURCE_MANIFEST)
    manifest = json.loads(manifest_bytes)
    entries = manifest.get('files')
    if not isinstance(entries, list) or not entries:
        raise RuntimeError('The reviewed source manifest has no file list.')
    sources, seen = [], set()
    for entry in entries:
        rel = entry.get('path')
        if not isinstance(rel, str):
            raise RuntimeError('Invalid source manifest path.')
        path = PurePosixPath(rel)
        if (path.is_absolute() or '..' in path.parts or str(path) != rel
                or len(path.parts) < 2 or path.parts[0] != 'HeckeSkeleton'
                or path.suffix != '.lean'):
            raise RuntimeError('New source must be under HeckeSkeleton: ' + rel)
        module = '.'.join(path.with_suffix('').parts)
        if entry.get('module') != module or rel in seen:
            raise RuntimeError('Duplicate or inconsistent source manifest entry: ' + rel)
        seen.add(rel)
        source = root / rel
        if not source.resolve().is_relative_to(root.resolve()):
            raise RuntimeError('Source escapes checkout: ' + rel)
        raw = regular_bytes(source)
        digest = sha256(raw)
        if digest != entry.get('source_sha256'):
            raise RuntimeError('Current source_sha256 differs from source bytes: ' + rel)
        tokens = sorted(set(FORBIDDEN.findall(strip_comments(raw.decode('utf-8')))))
        if tokens:
            raise RuntimeError('Forbidden new-source token in ' + rel + ': ' + ', '.join(tokens))
        sources.append({'path': rel, 'module': module, 'source_sha256': digest,
                        'bytes': len(raw)})
    if 'HeckeSkeleton/LowEnergy/ActualCompletedMarkedEnergy.lean' not in seen:
        raise RuntimeError('The manifest omits the required actual energy module.')
    principal = regular_bytes(root / 'HeckeSkeleton/Principal.lean')
    return {
        'manifest_sha256': sha256(manifest_bytes),
        'source_count': len(sources), 'sources': sorted(sources, key=lambda x: x['module']),
        'principal_source_sha256': sha256(principal),
        'config_sha256': {name: sha256(regular_bytes(root / name)) for name in CONFIG_PATHS},
    }


def clean_environment() -> dict[str, str]:
    env = os.environ.copy()
    # Lake supplies the dependency paths; no manual replay directory may shadow them.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    return env


def checked_output(command: list[str]) -> str:
    return subprocess.check_output(command, cwd=ROOT, env=clean_environment(),
                                   text=True, stderr=subprocess.STDOUT).strip()


def checkout_identity(expected_head: str) -> dict:
    if not re.fullmatch(r'[0-9a-f]{40}', expected_head):
        raise RuntimeError('An exact expected checkout commit is required.')
    head = checked_output(['git', 'rev-parse', 'HEAD'])
    if head != expected_head:
        raise RuntimeError('Checkout does not match the expected source commit.')
    dirty = checked_output(['git', 'status', '--porcelain', '--untracked-files=no'])
    if dirty:
        raise RuntimeError('Tracked checkout files changed:\n' + dirty)
    return {'head': head, 'tree': checked_output(['git', 'rev-parse', 'HEAD^{tree}'])}


def cache_metadata(directory: Path) -> dict:
    manifest_raw = regular_bytes(directory / 'lake-cache-manifest.json')
    sums_raw = regular_bytes(directory / 'SHA256SUMS')
    if sha256(manifest_raw) != CACHE_MANIFEST_SHA256 or sha256(sums_raw) != CACHE_SUMS_SHA256:
        raise RuntimeError('Restored cache metadata does not match the pinned release assets.')
    manifest = json.loads(manifest_raw)
    if (manifest.get('tag') != CACHE_TAG or manifest.get('commit') != CACHE_COMMIT
            or manifest.get('lean_toolchain') != TOOLCHAIN
            or 'HeckeSkeleton' not in manifest.get('excluded_module_prefixes', [])
            or set(manifest.get('build_roots', {})) != set(CACHE_BUILD_ROOTS)
            or manifest.get('parts') != [{'name': CACHE_PART, 'bytes': CACHE_PART_BYTES,
                                          'sha256': CACHE_PART_SHA256}]
            or sums_raw.decode().strip() != CACHE_PART_SHA256 + '  ' + CACHE_PART):
        raise RuntimeError('Pinned cache manifest has an unexpected shape.')
    # The immutable restore action checked this exact SHA256SUMS before extracting.
    return {'release_tag': CACHE_TAG, 'producer_commit': CACHE_COMMIT,
            'restore_action_commit': CACHE_ACTION,
            'manifest_sha256': CACHE_MANIFEST_SHA256, 'sums_sha256': CACHE_SUMS_SHA256,
            'part_sha256': CACHE_PART_SHA256, 'manifest': manifest}


def assert_no_proof_outputs(root: Path) -> list[str]:
    """Reject proof outputs in every candidate native build root, not only .olean."""
    roots = {root / rel for rel in CACHE_BUILD_ROOTS}
    roots.update((root / '.lake/packages').glob('*/.lake/build'))
    roots.update((root / 'vendor').glob('*/.lake/build'))
    found = []
    for build in sorted(roots):
        for area in ('lib/lean', 'ir'):
            directory = build / area
            for path in directory.glob('HeckeSkeleton*'):
                if path.name == 'HeckeSkeleton' or path.name.startswith('HeckeSkeleton.'):
                    if path.is_symlink() or path.is_file():
                        found.append(str(path.relative_to(root)))
                    elif path.is_dir():
                        found.extend(str(p.relative_to(root)) for p in path.rglob('*')
                                     if p.is_file() or p.is_symlink())
    if found:
        raise RuntimeError('Pre-existing HeckeSkeleton outputs forbid a fresh proof build: ' +
                           ', '.join(found[:12]))
    return sorted(str(path.relative_to(root)) for path in roots)


def run_logged(command: list[str], log: Path, timeout: float) -> dict:
    """Record one real process exit; do not manufacture per-module outcomes."""
    started = time.time()
    timed_out = False
    copy_errors = []
    with log.open('wb') as output:
        proc = subprocess.Popen(command, cwd=ROOT, env=clean_environment(),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                start_new_session=True)

        def copy_output() -> None:
            try:
                assert proc.stdout is not None
                while chunk := proc.stdout.read1(65536):
                    output.write(chunk)
                    output.flush()
                    sys.stdout.buffer.write(chunk)
                    sys.stdout.buffer.flush()
            except Exception as error:
                copy_errors.append(str(error))
                os.killpg(proc.pid, signal.SIGTERM)

        copier = threading.Thread(target=copy_output, daemon=True)
        copier.start()
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        finally:
            copier.join()
    if copy_errors:
        raise RuntimeError('Could not preserve compiler output: ' + '; '.join(copy_errors))
    return {'command': command, 'exit_code': proc.returncode, 'timed_out': timed_out,
            'started_unix': started, 'seconds': round(time.time() - started, 3),
            'log': log.name, 'log_sha256': sha256(log.read_bytes())}


def output_inventory(modules: list[str]) -> dict:
    inventory = {}
    for module in modules:
        stem = ROOT / '.lake/build/lib/lean' / Path(*module.split('.'))
        bundle = {}
        for suffix in (*RUNTIME_SUFFIXES, '.ilean', '.trace'):
            path = stem.with_name(stem.name + suffix)
            if path.is_file():
                bundle[suffix] = sha256(regular_bytes(path))
        if '.olean' not in bundle or '.trace' not in bundle:
            raise RuntimeError('Lake succeeded without the required target outputs: ' + module)
        inventory[module] = bundle
    return inventory


def inspect_final_audit(output: str) -> dict:
    if ALLOWED_AXIOMS != EXPECTED_AXIOMS:
        raise RuntimeError('The strict three-axiom policy changed.')
    return inspect_axiom_output(output, required=REQUIRED_AXIOMS)


def save(report: dict) -> None:
    report['updated_unix'] = time.time()
    write_json(EVIDENCE / 'report.json', report)


def prepare(expected_head: str) -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    # A failed setup or interrupted invocation must not inherit an old target audit.
    for name in ('lake-build.log', 'final-audit.lean', 'final-audit.log', 'final-audit.json',
                 'outputs.json', 'prepared.json'):
        (EVIDENCE / name).unlink(missing_ok=True)
    report = {'schema': SCHEMA, 'status': 'initializing', 'stage': 'source_preflight',
              'final_axiom_gate': 'not_started', 'expected_head': expected_head,
              'github_run_id': os.environ.get('GITHUB_RUN_ID'),
              'github_run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
              'github_event_sha': os.environ.get('GITHUB_SHA'),
              'evidence_kind': 'native Lake build and fresh required-name axiom audit',
              'per_module_schema2_receipts_created': False}
    save(report)
    try:
        report['checkout'] = checkout_identity(expected_head)
        report['source_snapshot'] = source_snapshot(ROOT)
        report.update(status='prepared', stage='awaiting_toolchain_and_pinned_release_restore')
        write_json(EVIDENCE / 'prepared.json', report)
        save(report)
    except Exception as error:
        report.update(status='failed', error=str(error))
        save(report)
        raise


def verify(expected_head: str, metadata_dir: Path, build_timeout: float) -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    report = {'schema': SCHEMA, 'status': 'running', 'stage': 'restore_preflight',
              'final_axiom_gate': 'not_started', 'expected_head': expected_head,
              'per_module_schema2_receipts_created': False}
    # Clear stale success evidence even when a malformed/missing prepare record fails.
    for name in ('lake-build.log', 'final-audit.lean', 'final-audit.log', 'final-audit.json', 'outputs.json'):
        (EVIDENCE / name).unlink(missing_ok=True)
    save(report)
    try:
        prepared = json.loads(regular_bytes(EVIDENCE / 'prepared.json'))
        if (prepared.get('schema') != SCHEMA or prepared.get('status') != 'prepared'
                or prepared.get('expected_head') != expected_head):
            raise RuntimeError('Missing or incompatible fresh source-preparation evidence.')
        report = {**prepared, 'status': 'running', 'stage': 'restore_preflight'}
        report['checkout'] = checkout_identity(expected_head)
        if source_snapshot(ROOT) != prepared['source_snapshot']:
            raise RuntimeError('Sources or configuration changed during cache setup.')
        report['cache'] = cache_metadata(metadata_dir)
        for name in ('lake-cache-manifest.json', 'SHA256SUMS'):
            (EVIDENCE / name).write_bytes(regular_bytes(metadata_dir / name))
        report['checked_empty_proof_build_roots'] = assert_no_proof_outputs(ROOT)
        if (ROOT / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
            raise RuntimeError('Unexpected Lean toolchain.')
        packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
        mathlib = next((p for p in packages if p.get('name') == 'mathlib'), {})
        if mathlib.get('rev') != MATHLIB_REV:
            raise RuntimeError('Unexpected Mathlib revision.')
        version = checked_output(['lake', 'env', 'lean', '--version'])
        if 'version 4.35.0-rc3,' not in version or LEAN_COMMIT not in version:
            raise RuntimeError('Unexpected Lean executable: ' + version)
        report['lean'] = version
        modules = sorted({PRINCIPAL, *(e['module'] for e in prepared['source_snapshot']['sources'])})
        command = ['lake', '--rehash', '--no-cache', 'build', *('+' + m + ':olean' for m in modules)]
        report.update(stage='building', requested_modules=modules)
        save(report)
        report['lake_build'] = run_logged(command, EVIDENCE / 'lake-build.log', build_timeout)
        save(report)
        if report['lake_build']['exit_code'] != 0 or report['lake_build']['timed_out']:
            raise RuntimeError('The native Lake build did not succeed.')
        checkout_identity(expected_head)
        if source_snapshot(ROOT) != prepared['source_snapshot']:
            raise RuntimeError('Sources or configuration changed during the build.')
        write_json(EVIDENCE / 'outputs.json', output_inventory(modules))
        report['output_inventory_sha256'] = sha256((EVIDENCE / 'outputs.json').read_bytes())
        report.update(stage='final_axiom_audit', final_axiom_gate='running')
        save(report)
        audit_source = 'import HeckeSkeleton.Principal\n' + ''.join(
            '#print axioms ' + name + '\n' for name in REQUIRED_AXIOMS)
        audit_file = EVIDENCE / 'final-audit.lean'
        audit_file.write_text(audit_source)
        command = ['lake', 'env', 'lean', '-j1', '-DautoImplicit=false',
                   '-DrelaxedAutoImplicit=false', '-DwarningAsError=true', str(audit_file)]
        report['final_audit'] = run_logged(command, EVIDENCE / 'final-audit.log', 600)
        audit = inspect_final_audit((EVIDENCE / 'final-audit.log').read_text(errors='replace'))
        write_json(EVIDENCE / 'final-audit.json', audit)
        report['final_audit']['printed_axiom_audit'] = audit
        if (report['final_audit']['exit_code'] != 0 or report['final_audit']['timed_out']
                or not audit['ok']):
            report['final_axiom_gate'] = 'failed'
            raise RuntimeError('The two required completedMarkedEnergy declarations failed the strict axiom gate.')
        checkout_identity(expected_head)
        if source_snapshot(ROOT) != prepared['source_snapshot']:
            raise RuntimeError('Sources or configuration changed during the final audit.')
        report.update(status='passed', stage='complete', final_axiom_gate='passed')
        save(report)
    except Exception as error:
        report.update(status='failed', error=str(error))
        if report.get('final_axiom_gate') == 'running':
            report['final_axiom_gate'] = 'failed'
        save(report)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('prepare', 'verify'))
    parser.add_argument('--expected-head', required=True)
    parser.add_argument('--cache-metadata-dir', type=Path)
    parser.add_argument('--build-timeout', type=float, default=9000)
    args = parser.parse_args()
    if not math.isfinite(args.build_timeout) or args.build_timeout <= 0 or args.build_timeout > 9000:
        parser.error('--build-timeout must be between 0 and 9000 seconds.')
    if args.phase == 'verify' and args.cache_metadata_dir is None:
        parser.error('verify requires --cache-metadata-dir from the pinned restore action.')
    try:
        if args.phase == 'prepare':
            prepare(args.expected_head)
        else:
            verify(args.expected_head, args.cache_metadata_dir, args.build_timeout)
    except Exception as error:
        print('LOW-REFLECTED-ENERGY Lake lane failed: ' + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
