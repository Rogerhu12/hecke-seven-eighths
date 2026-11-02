#!/usr/bin/env python3
"""Sample the complete Direct7e9 candidate with all 23 reversible markers.

The existing candidate separates the original producer application from its
unchanged obtain pattern. This diagnostic adds no proof edit or warning scope.
All source linters, Lean async and heartbeat remain at their original defaults.
The complete source and its exact inverse to owner243ed are preserved.
Command continuation may follow error recovery; inspect all raw MI and threads.
These diagnostic results do not grant native, fresh, or whole-task acceptance.
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

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectCoveredStage.lean')
SOURCE_SHA = '7e9ef16662ac3d88c9823480d2a052b05a1b920b2b9d306485e1fbb80b42eff9'
SOURCE_BYTES = 5247
WRAPPER = Path('.github/scripts/mom-engine-step-a2-direct-obtain-diagnostic.py')
WRAPPER_SHA = '559d3b822e2e304fad8c9c5c0a91937263b4c424057228954f9435753adb568b'
DRIVER = Path('.github/scripts/mom-engine-step-a2-direct-obtain-stack-driver.py')
DRIVER_SHA = 'ff0b37c87f949047ac69aa7e588a797bbe96e81976798ddfabdeeeeb26d0ce77'
MARKED_SHA = '9472a00a64ce4486271ba549cd1d4c9e2e800530e1e7977f68c68d1f5e90a13f'
MARKED_BYTES = 7079
PREFIX = 'A2_OWNER_DIRECT_DIAGNOSTIC '
TARGET = 'actual_direct_fourier_covered_terminal_bound'
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
        'scope': 'All-thread GDB diagnostic of the frozen complete Direct7e9 candidate with 23 reversible markers',
        'source_candidate_head': '61658c18f1dd6fe967f9abd39966fd5f62b7308c',
        'source_candidate_tree': 'd26b9f9648c595ec4ba446ee236e6740c139bb9d',
        'base_owner_head': 'fcc8dd6a84f709c6666da23b761f1b63643eaffb',
        'base_owner_tree': 'e4456fff025aa62aa900503e789af0e190371f8e',
        'candidate_source_not_adopted_as_owner_production': True,
        'owner_adoption_performed_by_this_diagnostic': False,
        'cause_of_after_proof_stall_confirmed': False,
        'source_sha256': SOURCE_SHA, 'source_bytes': SOURCE_BYTES,
        'wrapper_sha256': WRAPPER_SHA, 'driver_sha256': DRIVER_SHA,
        'diagnostic_source_sha256': MARKED_SHA, 'diagnostic_source_bytes': MARKED_BYTES,
        'driver_provenance_base_sha256': '08a51bf300f3c7327d9ac3a4cbebd6b94a5d59baea08217cedde4224728cb2b9',
        'driver_provenance': 'Offline seven identity-only replacements from Gated08a; no prior driver required at runtime',
        'original_production_and_proof_owner': 'A2/owner',
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
        'snapshot_boundary_interpretation': 'Use exact marker arrivals, complete raw MI and all-thread stacks; command continuation can follow error recovery and no marker proves source acceptance',
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
        spec = importlib.util.spec_from_file_location('a2_frozen_direct23_wrapper', repo / WRAPPER)
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
        assert len(manifest) == checks['marker_count'] == 23
        assert checks['declaration_count'] == 1
        assert checks['command_marker_count'] == 5 and checks['tactic_marker_count'] == 18
        assert checks['original_import_count'] == 2 and checks['original_print_axioms_count'] == 1
        assert checks['byte_reversal_verified'] and checks['all_original_lines_preserved_in_order']
        assert checks['all_original_data_headers_and_proofs_preserved_after_marker_removal']
        assert checks['doccomment_associations_verified'] and checks['include_doc_header_blocks_preserved']
        assert checks['new_warning_scope_count'] == checks['warning_scope_count'] == 0
        assert checks['all_original_linters_default'] and checks['full_original_module_copy_used']
        marker_lines = {entry['inserted_line'].encode() for entry in manifest}
        assert len(marker_lines) == 23
        assert b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines) == original
        assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
        labels = [entry['label'] for entry in manifest]
        for label in ['DIRECT_AFTER_UPSTREAM_APPLICATION', 'DIRECT_AFTER_OBTAIN', 'DIRECT_AFTER_CALC',
                      'COMMAND_CONTINUED_AFTER_' + TARGET, 'AFTER_ALL_ORIGINAL_COMMANDS']:
            assert labels.count(label) == 1
        owner_source = wrapper.restore_owner_source(original)
        assert len(owner_source) == 5217
        assert hashlib.sha256(owner_source).hexdigest() == '243ed35cc7230b41cd4dbaae596b1332e98da6707253d08ba7de58c4650f8372'
        assert checks['candidate_proof_transformation_count'] == 1
        assert checks['candidate_to_owner_proof_inverse_verified']
        assert checks['application_and_obtain_boundaries_separated']
        (evidence / 'DirectCoveredStage.candidate.lean').write_bytes(original)
        (evidence / 'DirectCoveredStage.owner-original.lean').write_bytes(owner_source)
        (evidence / 'MomEngineDirectCoveredStageSplitApplication.lean').write_bytes(marked)
        (evidence / 'direct_wrapper.py').write_bytes((repo / WRAPPER).read_bytes())
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / DRIVER).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        result.update(checks)
        result.update(complete_frozen_direct_candidate_with_23_markers=True,
                      target_default_warning_verified=True, marker_removal_recovers_original_bytes=True)
        if args.prepare_only:
            result.update(status='prepared_only', temporary_input_removed=True,
                          temporary_output_removed=True, no_process_started=True)
            code = 0
        else:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            for name in ['DirectGaussSource', 'ActualGaussFiniteLeaves']:
                assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                        (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
            # Keep the proven package-root input behavior; every compiler
            # product is redirected to a unique /tmp directory, never .lake.
            fd, name = tempfile.mkstemp(prefix='MomEngineDirectStack7e9_', suffix='.lean', dir=repo)
            compile_input = Path(name)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(marked)
            temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-direct-obtain-stack-', dir='/tmp')
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
                        'direct_upstream_application_returned_marker_observed':
                            'A2_OWNER_DIRECT_DIAGNOSTIC DIRECT_AFTER_UPSTREAM_APPLICATION' in observed,
                        'direct_obtain_returned_marker_observed':
                            'A2_OWNER_DIRECT_DIAGNOSTIC DIRECT_AFTER_OBTAIN' in observed,
                        'direct_complete_proof_returned_marker_observed':
                            'A2_OWNER_DIRECT_DIAGNOSTIC DIRECT_AFTER_CALC' in observed,
                        'direct_command_continued_marker_observed':
                            'A2_OWNER_DIRECT_DIAGNOSTIC COMMAND_CONTINUED_AFTER_actual_direct_fourier_covered_terminal_bound' in observed,
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
