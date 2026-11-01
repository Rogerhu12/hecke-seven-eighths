#!/usr/bin/env python3
"""Sample the frozen full 1ee terminal-sum candidate with 61 reversible markers.

The existing provider/public-phase/public-sum warning scopes and private
phase omit are unchanged. Both terminal theorems retain their default linters.
All results are diagnostic only; this script grants no production acceptance.
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

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
MARKER_SCRIPT = Path('.github/scripts/mom-engine-step-a2-diagnostic.py')
MARKER_SCRIPT_SHA = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
PRIOR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-public-phase-after.py')
PRIOR_SCRIPT_SHA = 'bc1a8cbab78e8c713e8bada7c97be38336d1c02bff92c82025a0d832b2cb31f8'
CONTROL_SCRIPT = Path('.github/scripts/mom-engine-step-a2-provider-public-warning-control.py')
CONTROL_SCRIPT_SHA = '91a373aaadf02897e9fafb803bffc4b11290c6a3bdc3a042ea38e9a331cb281f'
SCALAR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-scalar-sum-diagnostic.py')
SCALAR_SCRIPT_SHA = 'a9354aea9c276159ecdcee82761fa33c39d48baba2924118bb419e6786a4de09'
WARNING_SCRIPT = Path('.github/scripts/mom-engine-step-a2-scalar-sum-warning-control.py')
WARNING_SCRIPT_SHA = '283752262162f6935370110ed0bd613a6cc41ebf5de805799b5749d37c69b5df'
WRAPPER = Path('.github/scripts/mom-engine-step-a2-terminal-sum-diagnostic.py')
WRAPPER_SHA = '9fa475faf51b11596747dbfa5dcd496d76d0b28a27f77fb1e356ecb8bbaeed6b'
BASE_DRIVER = Path('.github/scripts/mom-engine-step-a2-scalar-sum-stack-driver.py')
BASE_DRIVER_SHA = 'fb965fed446d990a2c9f75b6a8353e026f0c17b095a264a868b2b9bc0fc8763e'
BASE_DRIVER_INPUT_SHA = '34f437b0532881d27cfd0eb07fa2f6450ce70e3cb524193876e6b16f006bef73'
DRIVER = Path('.github/scripts/mom-engine-step-a2-terminal-sum-stack-driver.py')
DRIVER_SHA = '34034444bb81a2eb1df32550cd948876075f952d14e6e7bdc353a1c76288f0ec'
BASELINE_MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
CANDIDATE_SHA = '1ee270ad098598dc83ac7ec2c8eef4fcb8fd3a88530958b14e32d955463f480e'
MARKED_SHA = 'c652bc5bcd47053a57b64bdd1f8b0b17324a229875aed7106c85eae01fd6e1a6'
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
    'marker_script': (MARKER_SCRIPT, MARKER_SCRIPT_SHA),
    'prior_script': (PRIOR_SCRIPT, PRIOR_SCRIPT_SHA),
    'control_script': (CONTROL_SCRIPT, CONTROL_SCRIPT_SHA),
    'scalar_script': (SCALAR_SCRIPT, SCALAR_SCRIPT_SHA),
    'warning_script': (WARNING_SCRIPT, WARNING_SCRIPT_SHA),
    'wrapper_script': (WRAPPER, WRAPPER_SHA),
    'base_driver_script': (BASE_DRIVER, BASE_DRIVER_SHA),
    'driver_script': (DRIVER, DRIVER_SHA),
}
DRIVER_REPLACEMENTS = [
    ('EXPECTED_INPUT_SHA256 = "' + BASE_DRIVER_INPUT_SHA + '"',
     'EXPECTED_INPUT_SHA256 = "' + MARKED_SHA + '"'),
    ('Input is not the frozen full 505 candidate plus 60 reversible markers',
     'Input is not the frozen full 1ee candidate plus 61 reversible markers'),
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--prepare-only', action='store_true',
                        help='Verify all pins and reversals without starting Lake, Lean or GDB')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'harness-result.json').exists(), 'Use a fresh evidence directory'
    result = {
        **FALSE_FLAGS,
        'scope': 'All-thread GDB diagnostic of the frozen complete 1ee terminal-sum candidate with 61 markers',
        'source_sha256': SOURCE_SHA, 'marker_script_sha256': MARKER_SCRIPT_SHA,
        'prior_script_sha256': PRIOR_SCRIPT_SHA, 'control_script_sha256': CONTROL_SCRIPT_SHA,
        'scalar_script_sha256': SCALAR_SCRIPT_SHA, 'warning_script_sha256': WARNING_SCRIPT_SHA,
        'wrapper_sha256': WRAPPER_SHA, 'driver_sha256': DRIVER_SHA,
        'base_driver_sha256': BASE_DRIVER_SHA,
        'driver_static_replacements': DRIVER_REPLACEMENTS,
        'owner_warning_scope_approval_comments': [6563548652, 6563834756],
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'same owner-approved provider/public-phase/public-sum controls as frozen 9fa4',
            'declarations': [
                'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.fixed_fullCorrelation_eq_leaf_sum',
                'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.phase_class_eq_leaf_sum',
                'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.coverHybridPhaseNonzeroCost_eq_leaf_sum'],
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 135, 'new_scopes': 0},
        'terminal_sum_warning_option_override': None,
        'terminal_integral_warning_option_override': None,
        'other_warning_option_override': None, 'global_warning_option_override': None,
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
        base_driver_bytes = (repo / BASE_DRIVER).read_bytes()
        transformed = base_driver_bytes
        for old, new in DRIVER_REPLACEMENTS:
            old_bytes, new_bytes = old.encode(), new.encode()
            assert transformed.count(old_bytes) == 1, old
            transformed = transformed.replace(old_bytes, new_bytes, 1)
        assert transformed == (repo / DRIVER).read_bytes(), 'New driver has an unreviewed change'
        result['driver_static_diff_verified'] = True
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location('a2_frozen_terminal_sum_wrapper', repo / WRAPPER)
        assert spec is not None and spec.loader is not None
        wrapper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(wrapper)
        warning_module = wrapper.load_warning_script(repo / WARNING_SCRIPT)
        scalar_module = warning_module.load_scalar_script(repo / SCALAR_SCRIPT)
        control_module = scalar_module.load_control_script(repo / CONTROL_SCRIPT)
        prior_module = control_module.load_prior_script(repo / PRIOR_SCRIPT)
        marker_module = prior_module.load_marker_script(repo / MARKER_SCRIPT)
        original = (repo / SOURCE).read_bytes()
        baseline, candidate, marked, manifest, checks = wrapper.prepare(
            original, marker_module, prior_module, control_module, scalar_module, warning_module)
        assert len(original) == 40282
        assert hashlib.sha256(baseline).hexdigest() == BASELINE_MARKED_SHA and len(baseline) == 45595
        assert hashlib.sha256(candidate).hexdigest() == CANDIDATE_SHA and len(candidate) == 41552
        assert hashlib.sha256(marked).hexdigest() == MARKED_SHA and len(marked) == 47047
        assert len(manifest) == 61 and checks['marker_count'] == 61
        assert checks['two_way_reversal_verified'] and checks['full_61_marker_control_reverse_verified']
        assert checks['candidate_reverse_to_base03c62_and_cc98_verified']
        assert checks['all_55_previous_headers_unchanged'] and checks['terminal_integral_full_suffix_unchanged']
        assert checks['new_warning_scope_count'] == 0 and checks['warning_scope_count'] == 3
        assert checks['terminal_sum_warning_uses_default'] and checks['terminal_integral_warning_uses_default']
        assert checks['no_global_warning_override'] and checks['full_warning60_marked_inverse_verified']
        assert checks['no_alias_or_as_aux_lemma_change']
        assert [scope['declaration'] for scope in checks['warning_scopes']] == control_module.WARNING_TARGETS + [
            'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.coverHybridPhaseNonzeroCost_eq_leaf_sum']
        target = 'phase_cost_eq_budgets_leaves'
        assert all(not scope['declaration'].endswith('.' + target) for scope in checks['warning_scopes'])
        labels = [entry['label'] for entry in manifest]
        for label in ['TERMINAL_SUM_BEFORE_EXACT', 'TERMINAL_SUM_AFTER_EXACT', 'COMMAND_CONTINUED_AFTER_' + target]:
            assert labels.count(label) == 1
        (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
        (evidence / 'ActualGaussFiniteLeaves.terminal-scalar-candidate.lean').write_bytes(candidate)
        (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
        (evidence / 'MomEngineActualDiagCc98c8a2.lean').write_bytes(marked)
        (evidence / 'terminal_sum_wrapper.py').write_bytes((repo / WRAPPER).read_bytes())
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / DRIVER).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        write_json(evidence / 'source-edits.json', wrapper.EDITS)
        result.update(checks)
        result.update(diagnostic_source_sha256=MARKED_SHA, diagnostic_source_bytes=len(marked),
                      scoped_candidate_sha256=CANDIDATE_SHA, scoped_candidate_bytes=len(candidate),
                      baseline_marked_source_sha256=BASELINE_MARKED_SHA,
                      complete_frozen_1ee_candidate_with_61_markers=True,
                      terminal_sum_default_warning_verified=True, terminal_integral_default_warning_verified=True)
        if args.prepare_only:
            result.update(status='prepared_only', temporary_input_removed=True,
                          temporary_output_removed=True, no_process_started=True)
            code = 0
        else:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            for name in ['CoverHybridPhaseIntegral', 'HybridFiniteLeaf']:
                assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                        (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
            # Keep the proven package-root input behavior; every compiler
            # product is redirected to a unique /tmp directory, never .lake.
            fd, name = tempfile.mkstemp(prefix='MomEngineActualTerminalSumStack1ee_', suffix='.lean', dir=repo)
            compile_input = Path(name)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(marked)
            temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-terminal-sum-stack-', dir='/tmp')
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
                        'terminal_sum_after_exact_marker_observed':
                            'A2_ACTUAL_CC98_DIAGNOSTIC TERMINAL_SUM_AFTER_EXACT' in observed,
                        'terminal_sum_command_continued_marker_observed':
                            'A2_ACTUAL_CC98_DIAGNOSTIC COMMAND_CONTINUED_AFTER_phase_cost_eq_budgets_leaves' in observed,
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
