#!/usr/bin/env python3
"""Sample the complete D-owned f499 source with all 46 reversible markers.

Every original declaration, proof, data object, import and axiom print is
preserved. All source linters, Lean async and heartbeat remain at defaults.
The driver is independently frozen from the reviewed terminal driver; this
harness requires no Actual scripts to exist in the D auxiliary source tree.
All results are diagnostic only and never native/fresh/production acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryLiteralExceptionalLeaf.lean')
SOURCE_SHA = 'f49992a4d96d0e86c404cb0e0138d613d30100b8405e1964b9258349ad4daee0'
SOURCE_BYTES = 21240
WRAPPER = Path('.github/scripts/mom-engine-step-a2-d-literal-diagnostic.py')
WRAPPER_SHA = '266a512fec83c659fc03186e46980eca1a698e22c8b8bd9fc36ec0032592f48a'
DRIVER = Path('.github/scripts/mom-engine-step-a2-d-literal-stack-driver.py')
DRIVER_SHA = 'fa48c184762acbf619ee3b499c444acb0ee4157753441d5a6bcb11edd21b1b77'
MARKED_SHA = '681461a728f500718a1557fe523721a1dd91d6645d95509d21946c7af76ccd4e'
MARKED_BYTES = 25235
PREFIX = 'A2_D_LITERAL_F499_DIAGNOSTIC '
TARGET = 'ordinary_exceptional_cost_from_original_atoms'
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'candidate_equivalence_claimed': False, 'fresh_axiom_audit_performed': False,
}
PINNED_FILES = {
    'source': (SOURCE, SOURCE_SHA),
    'wrapper_script': (WRAPPER, WRAPPER_SHA),
    'driver_script': (DRIVER, DRIVER_SHA),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--prepare-only', action='store_true',
                        help='Verify all pins and full-source reversal without starting Lake, Lean or GDB')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'harness-result.json').exists(), 'Use a fresh evidence directory'
    result = {
        **FALSE_FLAGS,
        'scope': 'All-thread GDB diagnostic of the frozen complete D f499 source with 46 reversible markers',
        'source_sha256': SOURCE_SHA, 'source_bytes': SOURCE_BYTES,
        'wrapper_sha256': WRAPPER_SHA, 'driver_sha256': DRIVER_SHA,
        'diagnostic_source_sha256': MARKED_SHA, 'diagnostic_source_bytes': MARKED_BYTES,
        'driver_provenance_base_sha256': '34034444bb81a2eb1df32550cd948876075f952d14e6e7bdc353a1c76288f0ec',
        'driver_provenance': 'Offline seven identity-only replacements; no Actual script dependency at runtime',
        'original_production_and_proof_owner': 'D',
        'warning_option_override': None, 'target_warning_option_override': None,
        'other_warning_option_override': None, 'global_warning_option_override': None,
        'all_original_linters_default': True,
        'stderr_option_override': False,
        'stderr_option_reason': 'Diagnostic marker transport only; original normal verifier is unchanged',
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'outer_timeout_seconds': 150, 'outer_kill_after_seconds': 10,
        'driver_main_timeout_seconds': 150, 'driver_cleanup_seconds': 10,
        'sample_offsets_after_imports_seconds': [60.0, 100.0],
        'stack_frame_limit_per_thread': 256,
        'marker_times_are_observed_arrival_only': True,
        'snapshot_boundary_interpretation': 'Use exact observed markers and full stacks; elapsed time alone does not establish proof return or command completion',
        'prepare_only': args.prepare_only,
        'driver_started': False, 'status': 'preflight', 'source_unchanged': False,
    }
    write_json(evidence / 'harness-result.json', result)
    original = None
    temporary = None
    compile_input = None
    process = None
    handlers = {}
    code = 1
    started = time.monotonic()

    def interrupted(signum, _frame):
        raise InterruptedError('Stack harness interrupted by signal ' + str(signum))

    try:
        for label, (path, expected) in PINNED_FILES.items():
            assert digest(repo / path) == expected, 'Frozen input changed: ' + label
        result['driver_identity_verified'] = True
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location('a2_frozen_d_literal46_wrapper', repo / WRAPPER)
        assert spec is not None and spec.loader is not None
        wrapper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(wrapper)
        assert wrapper.EXPECTED_SOURCE == SOURCE_SHA and wrapper.EXPECTED_BYTES == SOURCE_BYTES
        assert wrapper.SOURCE == SOURCE and wrapper.PREFIX + ' ' == PREFIX
        assert wrapper.EXPECTED_MARKED_SHA256 == MARKED_SHA and wrapper.EXPECTED_MARKED_BYTES == MARKED_BYTES
        assert wrapper.TIMEOUT_SECONDS == 150 and wrapper.KILL_AFTER_SECONDS == 10
        original = (repo / SOURCE).read_bytes()
        marked, manifest, checks = wrapper.instrument(original)
        assert len(original) == SOURCE_BYTES
        assert hashlib.sha256(marked).hexdigest() == MARKED_SHA and len(marked) == MARKED_BYTES
        assert len(manifest) == checks['marker_count'] == 46
        assert checks['declaration_count'] == 8
        assert checks['command_marker_count'] == 18 and checks['tactic_marker_count'] == 28
        assert checks['original_import_count'] == 2 and checks['original_print_axioms_count'] == 5
        assert checks['byte_reversal_verified'] and checks['all_original_lines_preserved_in_order']
        assert checks['all_original_data_headers_and_proofs_preserved_after_marker_removal']
        assert checks['doccomment_associations_verified'] and checks['direct_term_frames_proof_unchanged']
        assert checks['new_warning_scope_count'] == checks['warning_scope_count'] == 0
        assert checks['all_original_linters_default'] and checks['full_original_module_copy_used']
        marker_lines = {entry['inserted_line'].encode() for entry in manifest}
        assert len(marker_lines) == 46
        assert b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines) == original
        assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
        labels = [entry['label'] for entry in manifest]
        for label in ['ATOMS_FINAL_CALC_RETURNED', 'COMMAND_CONTINUED_AFTER_' + TARGET, 'AFTER_ALL_ORIGINAL_PRINTS']:
            assert labels.count(label) == 1
        (evidence / 'OrdinaryLiteralExceptionalLeaf.original.lean').write_bytes(original)
        (evidence / 'MomEngineLiteralDiagF49992a4.lean').write_bytes(marked)
        (evidence / 'literal_wrapper.py').write_bytes((repo / WRAPPER).read_bytes())
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / DRIVER).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        result.update(checks)
        result.update(complete_frozen_f499_source_with_46_markers=True,
                      target_default_warning_verified=True, marker_removal_recovers_original_bytes=True)
        if args.prepare_only:
            result.update(status='prepared_only', temporary_input_removed=True,
                          temporary_output_removed=True, no_process_started=True)
            code = 0
        else:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:
                assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                        (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
            # Keep the proven package-root input behavior; every compiler
            # product is redirected to a unique /tmp directory, never .lake.
            fd, name = tempfile.mkstemp(prefix='MomEngineDLiteralStackF499_', suffix='.lean', dir=repo)
            compile_input = Path(name)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(marked)
            temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-d-literal-stack-', dir='/tmp')
            output = Path(temporary.name)
            driver_evidence = evidence / 'driver'
            driver_evidence.mkdir()
            command = ['timeout', '--signal=TERM', '--kill-after=10s', '150s',
                       'lake', 'env', 'python3', str(repo / DRIVER),
                       '--input', str(compile_input), '--output', str(output / 'compiler'),
                       '--evidence', str(driver_evidence)]
            result.update(command=command, compile_input=str(compile_input),
                          compiler_output_directory=str(output / 'compiler'),
                          driver_started=True, status='running')
            write_json(evidence / 'harness-result.json', result)
            for sig in (signal.SIGINT, signal.SIGTERM):
                handlers[sig] = signal.signal(sig, interrupted)
            with (evidence / 'driver-console.log').open('w') as log:
                log.write(json.dumps({'command': command, 'cwd': str(repo)}) + '\n')
                log.flush()
                process = subprocess.Popen(command, cwd=repo, stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT, text=True, start_new_session=True)
                result['owned_wrapper_process_group'] = process.pid
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
        # The verified driver cleans only its same-user direct-child inferior.
        # This fallback signals only the new outer timeout process group.
        if process is not None and process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait(timeout=12)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=3)
            except ProcessLookupError:
                pass
        for sig, previous in handlers.items():
            signal.signal(sig, previous)
        report = evidence / 'driver/stack-result.json'
        if report.exists():
            try:
                driver_result = json.loads(report.read_text())
                result['driver_result'] = driver_result
                result['snapshot_boundary_observations'] = []
                events = driver_result.get('phase_markers', [])
                for sample in driver_result.get('snapshots', []):
                    prior_events = [event for event in events
                                    if event['elapsed_seconds'] <= sample['elapsed_seconds']]
                    observed = {event['text'] for event in prior_events}
                    result['snapshot_boundary_observations'].append({
                        'snapshot_number': sample['number'],
                        'atoms_final_calc_returned_marker_observed':
                            'A2_D_LITERAL_F499_DIAGNOSTIC ATOMS_FINAL_CALC_RETURNED' in observed,
                        'atoms_command_continued_marker_observed':
                            'A2_D_LITERAL_F499_DIAGNOSTIC COMMAND_CONTINUED_AFTER_ordinary_exceptional_cost_from_original_atoms' in observed,
                        'interpretation': 'Exact parsed marker arrival only; inspect full raw MI log for joined warning-tail events before interpreting an absent marker',
                    })
                if not driver_result.get('cleanup_complete', False):
                    code = 1
                    result['status'] = 'diagnostic_cleanup_failed'
            except (OSError, ValueError, KeyError, TypeError) as exc:
                code = 1
                result.update(status='unreadable_driver_result', report_error=repr(exc))
        elif result['driver_started']:
            code = 1
            result['status'] = 'missing_driver_result'
        for label, (path, expected) in PINNED_FILES.items():
            try:
                result[label + '_unchanged'] = digest(repo / path) == expected
            except OSError:
                result[label + '_unchanged'] = False
        if original is not None:
            result['source_unchanged'] = result['source_unchanged'] and (repo / SOURCE).read_bytes() == original
        if compile_input is not None:
            result['diagnostic_input_unchanged'] = digest(compile_input) == MARKED_SHA
            compile_input.unlink()
            result['temporary_input_removed'] = not compile_input.exists()
            if not result['diagnostic_input_unchanged']:
                code = 1
        if temporary is not None:
            output_path = Path(temporary.name)
            temporary.cleanup()
            result['temporary_output_removed'] = not output_path.exists()
        if not all(result.get(label + '_unchanged', False) for label in PINNED_FILES):
            code = 1
        result.update(FALSE_FLAGS)
        result.update(elapsed_seconds=time.monotonic() - started, harness_exit_code=code)
        write_json(evidence / 'harness-result.json', result)
        print(json.dumps({key: result[key] for key in [
            'status', 'driver_started', 'source_unchanged', 'harness_exit_code',
            'elapsed_seconds', 'acceptance_evidence', 'production_approval']}, ensure_ascii=False), flush=True)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
