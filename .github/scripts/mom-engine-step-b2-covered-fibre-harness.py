#!/usr/bin/env python3
"""Observe the complete frozen ActualCoveredFibre source; never acceptance.

The reviewed A2 own-child GDB driver is reused with identity changes only.
All original source lines survive both marker inverses. The 62 markers record
arrival, not proof/kernel completion; inspect every source error and raw stack.
No tracked Lean source, proof budget, linter, or async option is changed.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

MANIFEST_NAME = 'mom-engine-step-b2-covered-fibre-manifest.json'
MANIFEST_SHA = 'fddc67a9234ac6b920c4b37effb301542314f3257ef62e8b822fa27e29e28a03'
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False,
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)


def load_manifest() -> tuple[dict, Path]:
    assets = Path(__file__).resolve().parent
    path = assets / MANIFEST_NAME
    assert digest(path) == MANIFEST_SHA, 'Frozen diagnostic manifest changed'
    manifest = json.loads(path.read_text())
    driver = assets / Path(manifest['paths']['driver']).name
    assert digest(driver) == manifest['driver_sha256'], 'Frozen GDB driver changed'
    return manifest, driver


def check_pins(repo: Path, manifest: dict) -> None:
    for path, expected in manifest['production_pins'].items():
        assert digest(repo / path) == expected, 'Frozen production input changed: ' + path


def load_watch(repo: Path, manifest: dict):
    relative = 'scripts/mom_engine_b2_native_watch.py'
    assert digest(repo / relative) == manifest['production_pins'][relative]
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('b2_covered_frozen_group_watch', repo / relative)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def instrument(original: bytes, manifest: dict) -> tuple[bytes, dict]:
    assert len(original) == manifest['source_bytes']
    assert hashlib.sha256(original).hexdigest() == manifest['source_sha256']
    assert hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest() == manifest['source_git_blob']
    lines = original.splitlines(keepends=True)
    assert len(lines) == manifest['source_lines'] and all(line.endswith(b'\n') for line in lines)
    assert manifest['prefix'].encode() not in original
    assert [line.decode() for line in lines if line.startswith(b'import ')] == manifest['imports']
    assert [line.decode() for line in lines if line.startswith(b'#print axioms ')] == manifest['original_prints']
    assert len(manifest['imports']) == 3 and len(manifest['original_prints']) == 4
    assert b'set_option ' not in original and b'as_aux_lemma' not in original
    assert not re.search(rb'\b(?:sorry|admit)\b', original)
    events = manifest['markers']
    assert len(events) == 62 and len({e['label'] for e in events}) == 62
    assert sum(e['kind'] == 'command' for e in events) == 44
    assert sum(e['kind'] == 'tactic' for e in events) == 18
    assert events == sorted(events, key=lambda e: (e['original_insert_before_line'], e['priority']))
    for event in events:
        assert event['kind'] in ('command', 'tactic')
        assert event['indent'] == (0 if event['kind'] == 'command' else 2)
        assert re.fullmatch(r'[A-Za-z0-9_]+', event['label'])
        expected = (' ' * event['indent'] + ('run_cmd' if event['kind'] == 'command' else 'run_tac') +
                    ' IO.eprintln "' + manifest['prefix'] + ' ' + event['label'] + '"\n')
        assert event['inserted_line'] == expected
    output = []
    for number in range(1, len(lines) + 2):
        for event in events:
            if event['original_insert_before_line'] == number:
                assert event['instrumented_line'] == len(output) + 1
                output.append(event['inserted_line'].encode())
        if number <= len(lines):
            output.append(lines[number - 1])
    marked = b''.join(output)
    assert len(marked) == manifest['marked_bytes']
    assert hashlib.sha256(marked).hexdigest() == manifest['marked_sha256']
    markers = {event['inserted_line'].encode() for event in events}
    assert len(markers) == 62 and all(marked.count(marker) == 1 for marker in markers)
    assert b''.join(line for line in output if line not in markers) == original
    reverse = marked
    for event in reversed(events):
        reverse = reverse.replace(event['inserted_line'].encode(), b'', 1)
    assert reverse == original
    assert [line for line in output if line not in markers] == lines
    assert len(manifest['declarations']) == 17
    assert sum(d['kind'] == 'theorem' for d in manifest['declarations']) == 9
    for declaration in manifest['declarations']:
        start, header = declaration['doc_header_start_line'], declaration['header_line']
        assert declaration['name'].encode() in lines[header - 1]
        assert marked.count(b''.join(lines[start - 1:header])) == 1
        assert not any(start < e['original_insert_before_line'] <= header for e in events)
        if declaration['kind'] == 'theorem':
            first = declaration['proof_body_first_line']
            assert lines[first - 2].rstrip().endswith(b':= by')
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in output if line.startswith(prefix)] == [line for line in lines if line.startswith(prefix)]
    assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
    return marked, {
        'byte_reversal_verified': True, 'individual_removal_reversal_verified': True,
        'all_original_lines_preserved_in_order': True, 'all_original_headers_and_proofs_preserved': True,
        'doccomment_associations_verified': True, 'declaration_count': 17,
        'marker_count': 62, 'command_marker_count': 44, 'tactic_marker_count': 18,
        'original_import_count': 3, 'original_print_axioms_count': 4,
        'proof_transformations_added': 0, 'new_warning_scope_count': 0,
    }


def provenance(repo: Path, evidence: Path, phase: str, manifest: dict, watch) -> int:
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()
    check_pins(repo, manifest)
    base = manifest['source_base']
    assert git('rev-parse', base + '^{tree}') == manifest['source_base_tree']
    assert git('rev-parse', 'HEAD^') == manifest['expected_parent'], 'Diagnostic must extend the reviewed auxiliary parent'
    assert git('rev-parse', manifest['expected_parent'] + '^{tree}') == manifest['expected_parent_tree']
    assert len(git('rev-list', '--parents', '-n', '1', 'HEAD').split()) == 2
    changed = git('diff', '--name-only', base, 'HEAD').splitlines()
    additions = git('diff', '--name-only', '--diff-filter=A', base, 'HEAD').splitlines()
    assert set(changed) == set(additions) == set(manifest['paths'].values()), 'Only four new diagnostic auxiliary files may differ'
    assert Path(__file__).resolve() == (repo / manifest['paths']['harness']).resolve()
    assert digest(repo / manifest['paths']['manifest']) == MANIFEST_SHA
    assert digest(repo / manifest['paths']['driver']) == manifest['driver_sha256']
    record = watch.source_identity(repo)
    assert record['head'] == os.environ['EXPECTED_SHA'], 'Unexpected checkout SHA'
    record.update(source_base=base, source_base_tree=manifest['source_base_tree'],
                  expected_parent=manifest['expected_parent'], expected_parent_tree=manifest['expected_parent_tree'],
                  changed_paths_from_base=changed, manifest_sha256=MANIFEST_SHA,
                  source_and_script_pins=manifest['production_pins'], **FALSE_FLAGS)
    write_json(evidence / (phase + '-source.json'), record)
    if phase == 'after':
        assert json.loads((evidence / 'before-source.json').read_text()) == record, 'Complete tracked source identity changed'
        write_json(evidence / 'source-integrity.json', {
            'unchanged': True, 'head': record['head'], 'tree': record['tree'],
            'tracked_files': len(record['tracked_sha256']), 'task_modules': 1009,
            'interface_imports': 1008, 'libraries': 20, **FALSE_FLAGS,
        })
    print(f"{phase}: complete tracked identity, 1009 modules, 1008 exact imports, 20 libraries preserved", flush=True)
    return 0


def run(repo: Path, evidence: Path, prepare_only: bool, manifest: dict, driver: Path, watch) -> int:
    assert '.lake' not in evidence.parts
    assert not (evidence / 'harness-result.json').exists(), 'Use a fresh diagnostic evidence directory'
    result = {
        **FALSE_FLAGS, 'status': 'preflight', 'driver_started': False,
        'scope': 'Complete frozen ActualCoveredFibre source with 62 reversible markers and own-child GDB',
        'source_sha256': manifest['source_sha256'], 'source_bytes': manifest['source_bytes'],
        'marked_sha256': manifest['marked_sha256'], 'marked_bytes': manifest['marked_bytes'],
        'manifest_sha256': MANIFEST_SHA, 'driver_sha256': manifest['driver_sha256'],
        'sampling': manifest['sampling'], 'prepare_only': prepare_only,
        'marker_times_are_observed_arrival_only': True,
        'all_original_linters_default': True, 'heartbeat_override': None,
        'lean_async_override': None, 'profiler_override': None,
        'source_unchanged': False,
    }
    write_json(evidence / 'harness-result.json', result)
    started = time.monotonic()
    original = None
    compile_input = None
    temporary = None
    process = None
    group = None
    handlers = {}
    code = 1
    launching = False
    pending_signal = None

    def interrupted(signum, _frame):
        nonlocal pending_signal
        if launching:
            # Do not raise between Popen creating a child and registering its
            # owned group. Signals are not blocked or inherited as blocked.
            pending_signal = signum
            return
        raise InterruptedError('Stack harness interrupted by signal ' + str(signum))

    try:
        check_pins(repo, manifest)
        original = (repo / manifest['source']).read_bytes()
        marked, checks = instrument(original, manifest)
        result.update(checks)
        (evidence / 'ActualCoveredFibre.original.lean').write_bytes(original)
        (evidence / 'ActualCoveredFibre.marked.lean').write_bytes(marked)
        (evidence / MANIFEST_NAME).write_bytes((Path(__file__).resolve().parent / MANIFEST_NAME).read_bytes())
        (evidence / 'lean-gdb-parent-driver.py').write_bytes(driver.read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest['markers'])
        if prepare_only:
            code = 0
            result.update(status='prepared_only', no_process_started=True,
                          temporary_input_removed=True, temporary_output_removed=True)
        else:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True)
            assert '4.35.0-rc3' in version and '470d5ce1400764999581fd26d5d72b00d990b0f4' in version
            mathlib = subprocess.check_output(['git', '-C', str(repo / '.lake/packages/mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
            assert mathlib == '0493595ecd5da8ef14742febab99728f98e948e8'
            result.update(lean_version=version.strip(), mathlib_commit=mathlib)
            for line in manifest['imports']:
                module = line.strip().removeprefix('import ')
                assert (repo / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')).is_file(), 'Run the original Lake :deps first: ' + module
            fd, name = tempfile.mkstemp(prefix='MomEngineCoveredFibreDiag_', suffix='.lean', dir=repo)
            compile_input = Path(name)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(marked)
            temporary = tempfile.TemporaryDirectory(prefix='mom-engine-b2-covered-gdb-', dir='/tmp')
            output = Path(temporary.name) / 'compiler'
            driver_evidence = evidence / 'driver'
            driver_evidence.mkdir()
            command = ['timeout', '--signal=TERM', '--kill-after=10s', '150s',
                       'lake', 'env', 'python3', str(driver), '--input', str(compile_input),
                       '--output', str(output), '--evidence', str(driver_evidence)]
            result.update(command=command, compile_input=str(compile_input),
                          compiler_output_directory=str(output), driver_started=True, status='running')
            write_json(evidence / 'harness-result.json', result)
            for sig in (signal.SIGINT, signal.SIGTERM):
                handlers[sig] = signal.signal(sig, interrupted)
            with (evidence / 'driver-console.log').open('w') as log:
                log.write(json.dumps({'command': command, 'cwd': str(repo)}) + '\n')
                log.flush()
                launching = True
                try:
                    process = subprocess.Popen(command, cwd=repo, stdin=subprocess.DEVNULL,
                                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                               text=True, start_new_session=True)
                    state = watch.process_state(process.pid)
                    assert state is not None and state[2:] == (process.pid, process.pid)
                    group = {'pid': process.pid, 'start_ticks': state[1]}
                finally:
                    launching = False
                if pending_signal is not None:
                    raise InterruptedError('Signal received while registering owned process: ' + str(pending_signal))
                result['owned_wrapper_group'] = group
                write_json(evidence / 'owned-wrapper-group.json', group)
                assert process.stdout is not None
                for line in process.stdout:
                    log.write(line)
                    log.flush()
                    print(line, end='', flush=True)
                code = process.wait()
            result.update(status='diagnostic_finished', driver_wrapper_exit_code=code)
    except BaseException as exc:
        result.update(status='harness_error', error=repr(exc))
        code = 1
    finally:
        for sig in handlers:
            signal.signal(sig, signal.SIG_IGN)
        try:
            # The pinned B2 helper rechecks PID/start time, session and group,
            # including remaining descendants after the leader has exited.
            if process is not None and group is None:
                # Recover before wait/reap, so the created child PID cannot be
                # reused while we establish its original session identity.
                state = watch.process_state(process.pid)
                assert state is not None and state[2:] == (process.pid, process.pid)
                group = {'pid': process.pid, 'start_ticks': state[1]}
                result['owned_wrapper_group_recovered'] = group
            if group is not None:
                watch.stop_group(group)
                result['owned_wrapper_group_empty'] = not watch.group_members(group)
            if process is not None:
                process.wait(timeout=2)
        except BaseException as exc:
            code = 1
            result.update(status='diagnostic_cleanup_failed', cleanup_error=repr(exc))
        report = evidence / 'driver/stack-result.json'
        if report.exists():
            try:
                driver_result = json.loads(report.read_text())
                result['driver_result'] = driver_result
                result['snapshot_boundary_observations'] = []
                for sample in driver_result.get('snapshots', []):
                    observed = {event['text'] for event in driver_result.get('phase_markers', [])
                                if event['elapsed_seconds'] <= sample['elapsed_seconds']}
                    prefix = manifest['prefix'] + ' '
                    boundaries = []
                    for declaration in manifest['declarations']:
                        name = declaration['name']
                        boundaries.append({'name': name,
                            'header_marker_observed': prefix + 'BEFORE_HEADER_' + name in observed,
                            'proof_begin_observed': prefix + 'PROOF_BEGIN_' + name in observed,
                            'proof_return_observed': prefix + 'PROOF_RETURNED_' + name in observed,
                            'command_continued_observed': prefix + 'COMMAND_CONTINUED_AFTER_' + name in observed})
                    result['snapshot_boundary_observations'].append({'snapshot_number': sample['number'],
                        'declarations': boundaries, 'interpretation': 'Marker arrivals only; inspect complete raw MI, including warning-tail joined events and all source errors, before any inference.'})
                if not driver_result.get('cleanup_complete', False):
                    code = 1
                    result['status'] = 'diagnostic_cleanup_failed'
            except (OSError, ValueError, KeyError, TypeError) as exc:
                code = 1
                result.update(status='unreadable_driver_result', report_error=repr(exc))
        elif result['driver_started']:
            code = 1
            result['status'] = 'missing_driver_result'
        try:
            check_pins(repo, manifest)
            load_manifest()
            result['all_pins_unchanged'] = True
            result['source_unchanged'] = original is not None and (repo / manifest['source']).read_bytes() == original
            assert result['source_unchanged']
        except BaseException as exc:
            code = 1
            result.update(source_unchanged=False, pin_error=repr(exc))
        if compile_input is not None:
            try:
                result['diagnostic_input_unchanged'] = digest(compile_input) == manifest['marked_sha256']
                if not result['diagnostic_input_unchanged']:
                    code = 1
                compile_input.unlink()
                result['temporary_input_removed'] = not compile_input.exists()
            except OSError as exc:
                code = 1
                result['temporary_input_cleanup_error'] = repr(exc)
        if temporary is not None:
            try:
                output_path = Path(temporary.name)
                temporary.cleanup()
                result['temporary_output_removed'] = not output_path.exists()
            except OSError as exc:
                code = 1
                result['temporary_output_cleanup_error'] = repr(exc)
        for sig, previous in handlers.items():
            signal.signal(sig, previous)
        result.update(FALSE_FLAGS)
        result.update(elapsed_seconds=time.monotonic() - started, harness_exit_code=code)
        write_json(evidence / 'harness-result.json', result)
        print(json.dumps({key: result[key] for key in ['status', 'driver_started', 'source_unchanged',
              'harness_exit_code', 'elapsed_seconds', 'acceptance_evidence', 'production_approval']}), flush=True)
    return code if code >= 0 else 128 - code


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--provenance', choices=['before', 'after'])
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    manifest, driver = load_manifest()
    check_pins(repo, manifest)
    watch = load_watch(repo, manifest)
    if args.provenance:
        assert not args.prepare_only
        return provenance(repo, evidence, args.provenance, manifest, watch)
    return run(repo, evidence, args.prepare_only, manifest, driver, watch)


if __name__ == '__main__':
    raise SystemExit(main())
