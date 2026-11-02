#!/usr/bin/env python3
"""Compare two complete corrected Dual copies using identical own-child GDB.

Both variants apply the same explicit integral_add function arguments to the
private raw helper. Only the control scopes unusedSectionVars off for the
public phase sum declaration. No tracked proof or imported guard is changed.
Every result remains diagnostic, including a temporary compiler exit zero.
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

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualGaussHybridTerminal.lean')
SOURCE_SHA = 'e3e2453aff96995252298f97c9ee85074252d4cb937a118e40411f5e760eb6ac'
SOURCE_BYTES = 17905
BASE_MARKER = Path('.github/scripts/mom-engine-step-a2-dual-candidate-diagnostic.py')
BASE_MARKER_SHA = '3d736c13349b589ac227c69260fad27ec872d772dbfa9cff2b86d36deb24cd81'
WRAPPER = Path('.github/scripts/mom-engine-step-a2-dual-corrected-phase-diagnostic.py')
WRAPPER_SHA = '51b8183178360253b9d5291ec411e1a11d289b35a000f9b5ed4f74bd27b5e612'
PREFIX = 'A2_DUAL_E3E2453_DIAGNOSTIC '
TARGET = 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.DualTerminalCalibration.phase_cost_eq_budgets_leaves'
VARIANTS = {
    'default': {
        'driver': Path('.github/scripts/mom-engine-step-a2-dual-corrected-default-stack-driver.py'),
        'driver_sha256': '484fe7629fcbbc926aaa1c6cf612519a232e1c1e2e2677f124ead6b3d6a07bd9',
        'candidate_sha256': '770bf81e8c634ac7a49c5eb00f179eec0ebf87fd764ccfbf115ed84d441ddac2',
        'candidate_bytes': 18019,
        'marked_sha256': '4a4fcf23ae76a9933c61bb76c45f94738dd75cf0a0a5461a37cec81e4f507538',
        'marked_bytes': 26964,
        'module': 'MomEngineDualCorrectedDefault',
        'warning_scope_count': 0,
    },
    'phase_warning_control': {
        'driver': Path('.github/scripts/mom-engine-step-a2-dual-corrected-control-stack-driver.py'),
        'driver_sha256': '81564f94574715a0e68713bc1e7416281f15a55916e6abcc8a8fa46f7b827777',
        'candidate_sha256': '21118c1b1c69084e625ba068b4501ab76997c11967a468fc0d9c46124e14157e',
        'candidate_bytes': 18064,
        'marked_sha256': 'c11c76f0fb7b2f2b2fa4b36441338121efe18c09241f98081938dd8375ac49a9',
        'marked_bytes': 27009,
        'module': 'MomEngineDualCorrectedPhaseWarning',
        'warning_scope_count': 1,
    },
}
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
    'base_marker_script': (BASE_MARKER, BASE_MARKER_SHA),
    'wrapper_script': (WRAPPER, WRAPPER_SHA),
    'default_driver_script': (VARIANTS['default']['driver'], VARIANTS['default']['driver_sha256']),
    'control_driver_script': (VARIANTS['phase_warning_control']['driver'], VARIANTS['phase_warning_control']['driver_sha256']),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--variant', required=True, choices=tuple(VARIANTS))
    parser.add_argument('--prepare-only', action='store_true',
                        help='Verify both static driver pins and all source reversals without starting a process')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    info = VARIANTS[args.variant]
    selected_driver = info['driver']
    marked_sha = info['marked_sha256']
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'harness-result.json').exists(), 'Use a fresh evidence directory'
    result = {
        **FALSE_FLAGS,
        'scope': 'Complete corrected Dual full108 GDB comparison; selected control differs only by one scoped 45-byte option',
        'variant': args.variant,
        'source_base': '1d8375a7b6c05f6c30c2b1523b195dc072d574b2',
        'source_base_tree': 'b5bddfe7f9bb663212dd9d459e14322b46e9b48c',
        'source_sha256': SOURCE_SHA, 'source_bytes': SOURCE_BYTES,
        'source_is_frozen_tracked_e3e': True,
        'temporary_source_candidate_sha256': info['candidate_sha256'],
        'temporary_source_candidate_bytes': info['candidate_bytes'],
        'temporary_source_contains_shared_raw_helper_fix': True,
        'raw_helper_fix_delta_bytes': 114,
        'raw_helper_fix_native_success_not_assumed': True,
        'candidate_source_not_adopted_as_owner_production': True,
        'owner_adoption_performed_by_this_diagnostic': False,
        'base_marker_sha256': BASE_MARKER_SHA, 'wrapper_sha256': WRAPPER_SHA,
        'driver_sha256': info['driver_sha256'], 'selected_driver_path': str(selected_driver),
        'diagnostic_source_sha256': marked_sha, 'diagnostic_source_bytes': info['marked_bytes'],
        'driver_provenance_base_sha256': '30620e6b480e26fe6143dfa1498027fa465ace8a1b05a406f0fa867bdeffc8dd',
        'driver_provenance': 'Each frozen driver differs from 30620 only in its static full-input hash and descriptive input-error string',
        'new_warning_scope_count': info['warning_scope_count'],
        'warning_option_override': None,
        'target_warning_option_override': None if args.variant == 'default' else {'option': 'linter.unusedSectionVars', 'value': False, 'declaration': TARGET, 'bytes': 45},
        'other_warning_option_override': None, 'global_warning_option_override': None,
        'all_original_linters_default': args.variant == 'default',
        'all_other_declarations_linters_default': True,
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
        spec = importlib.util.spec_from_file_location('a2_dual_corrected108_preparer', repo / WRAPPER)
        assert spec is not None and spec.loader is not None
        wrapper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(wrapper)
        assert wrapper.SOURCE == SOURCE and wrapper.TRACKED_SOURCE_SHA == SOURCE_SHA
        assert wrapper.TRACKED_SOURCE_BYTES == SOURCE_BYTES and wrapper.PREFIX == PREFIX
        assert wrapper.BASE_MARKER == BASE_MARKER and wrapper.BASE_MARKER_SHA == BASE_MARKER_SHA
        assert wrapper.PARENT_HEAD == result['source_base'] and wrapper.PARENT_TREE == result['source_base_tree']
        for key in ['candidate_sha256', 'candidate_bytes', 'marked_sha256', 'marked_bytes', 'module', 'warning_scope_count']:
            assert wrapper.VARIANTS[args.variant][key] == info[key]
        marker = wrapper.load_marker_script(repo / BASE_MARKER)
        original = (repo / SOURCE).read_bytes()
        baseline, candidate, marked, manifest, checks = wrapper.prepare(original, marker, args.variant)
        assert len(original) == SOURCE_BYTES and hashlib.sha256(original).hexdigest() == SOURCE_SHA
        assert len(candidate) == info['candidate_bytes'] and hashlib.sha256(candidate).hexdigest() == info['candidate_sha256']
        assert len(marked) == info['marked_bytes'] and hashlib.sha256(marked).hexdigest() == marked_sha
        assert len(manifest) == checks['marker_count'] == 108
        assert checks['declaration_count'] == 17 and checks['command_marker_count'] == 41 and checks['tactic_marker_count'] == 67
        assert checks['original_import_count'] == 3 and checks['original_print_axioms_count'] == 5
        assert checks['all108_marker_lines_labels_order_byte_preserved']
        assert checks['candidate_recovered_after_marker_removal_both_ways']
        assert checks['corrected770bf_recovered_after_optional45_removal']
        assert checks['tracked_e3e_recovered_after_all_reversals']
        assert checks['public_heads_data_instances_imports_prints_unchanged']
        assert checks['doccomment_association_preserved']
        assert checks['warning_scope_count'] == info['warning_scope_count']
        assert checks['all_original_linters_default'] == (args.variant == 'default')
        assert checks['all_other_declarations_linters_default']
        marker_lines = {entry['inserted_line'].encode() for entry in manifest}
        assert len(marker_lines) == 108
        assert b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines) == candidate
        labels = [entry['label'] for entry in manifest]
        for label in ['SUM_AFTER_EXACT', 'COMMAND_CONTINUED_AFTER_phase_cost_eq_budgets_leaves', 'AFTER_ALL_ORIGINAL_COMMANDS']:
            assert labels.count(label) == 1
        (evidence / 'DualGaussHybridTerminal.tracked-e3e.lean').write_bytes(original)
        (evidence / 'DualGaussHybridTerminal.temporary-candidate.lean').write_bytes(candidate)
        (evidence / 'baseline-e3e.marked108.lean').write_bytes(baseline)
        (evidence / (info['module'] + '.lean')).write_bytes(marked)
        (evidence / 'corrected_wrapper.py').write_bytes((repo / WRAPPER).read_bytes())
        (evidence / 'base_marker.py').write_bytes((repo / BASE_MARKER).read_bytes())
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / selected_driver).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        result.update(checks)
        result.update(complete_frozen_dual_temporary_source_with_108_markers=True,
                      exact_variant_source_verified=True, marker_removal_recovers_candidate_bytes=True)
        if args.prepare_only:
            result.update(status='prepared_only', temporary_input_removed=True,
                          temporary_output_removed=True, no_process_started=True)
            code = 0
        else:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            for name in ['ActualGaussDualRawTerminal', 'ActualGaussHybridTerminal', 'ActualGaussFiniteLeaves']:
                assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                        (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
            # Keep the proven package-root input behavior; every compiler
            # product is redirected to a unique /tmp directory, never .lake.
            fd, name = tempfile.mkstemp(prefix='MomEngineDualCorrectedStack_', suffix='.lean', dir=repo)
            compile_input = Path(name)
            with os.fdopen(fd, 'wb') as stream:
                stream.write(marked)
            temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-dual-corrected-stack-', dir='/tmp')
            output = Path(temporary.name)
            driver_evidence = evidence / 'driver'
            driver_evidence.mkdir()
            command = ['timeout', '--signal=TERM', '--kill-after=10s', '150s',
                       'lake', 'env', 'python3', str(repo / selected_driver),
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
                        'dual_phase_sum_after_exact_marker_observed':
                            'A2_DUAL_E3E2453_DIAGNOSTIC SUM_AFTER_EXACT' in observed,
                        'dual_phase_sum_command_continued_marker_observed':
                            'A2_DUAL_E3E2453_DIAGNOSTIC COMMAND_CONTINUED_AFTER_phase_cost_eq_budgets_leaves' in observed,
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
            result['diagnostic_input_unchanged'] = digest(compile_input) == marked_sha
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
