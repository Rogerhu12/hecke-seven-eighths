#!/usr/bin/env python3
"""Sample the full cc98 two-private-warning copy with 61 markers and public linters unchanged."""
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
WRAPPER = Path('.github/scripts/mom-engine-step-a2-public-phase-after.py')
WRAPPER_SHA = 'bc1a8cbab78e8c713e8bada7c97be38336d1c02bff92c82025a0d832b2cb31f8'
BASE_DRIVER = Path('.github/scripts/mom-engine-step-a2-provider-stack-driver.py')
BASE_DRIVER_SHA = '4049a48e8e3bd8c3e9a1ce27cd7f8286237e15d0938616fcc8435e88ab18ba4b'
BASE_DRIVER_INPUT_SHA = 'dae6ab7725794a2f2f2fdbf5fc370b78e4a5e717b502a3cf640d5fc2c5c8a7ca'
DRIVER = Path('.github/scripts/mom-engine-step-a2-public-phase-stack-driver.py')
DRIVER_SHA = 'c9dcdca396a05167492d3f8ab80f95cc487ddd66730a94bea001f18ddd15540d'
BASELINE_MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
CANDIDATE_SHA = '5518a6523e94b3b14be8292579cdaa7459c80b7ca4b6f06868618f3e41e4915c'
MARKED_SHA = 'fcbe6a79c67e550de2d340846ceb4b563fe3ce857d55441b1c97050dc8d27692'
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'harness-result.json').exists(), 'Use a fresh evidence directory'
    result = {**FALSE_FLAGS, 'scope': 'Deep stack diagnostic of the full cc98 two-private-warning copy with 61 markers; public linter unchanged',
              'source_sha256': SOURCE_SHA, 'marker_script_sha256': MARKER_SCRIPT_SHA,
              'driver_sha256': DRIVER_SHA, 'base_driver_sha256': BASE_DRIVER_SHA,
              'wrapper_sha256': WRAPPER_SHA,
              'driver_change_from_base': 'Only EXPECTED_INPUT_SHA256 changes to the statically pinned 61-marker full-copy hash',
              'warning_option_override': {'option': 'linter.unusedSectionVars', 'value': False,
                                          'scope': 'two private declarations',
                                          'declarations': [
                                              'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.phase_class_eq_fixed_fullCorrelation',
                                              'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.fixed_fullCorrelation_eq_leaf_sum'],
                                          'inserted_bytes_per_declaration': 45,
                                          'total_inserted_bytes': 90},
              'public_warning_option_override': None, 'production_approval': False,
              'other_warning_option_override': None, 'stderr_option_override': False,
              'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
              'outer_timeout_seconds': 195, 'outer_kill_after_seconds': 10,
              'driver_started': False, 'status': 'preflight', 'source_unchanged': False}
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
        assert digest(repo / SOURCE) == SOURCE_SHA
        assert digest(repo / MARKER_SCRIPT) == MARKER_SCRIPT_SHA
        assert digest(repo / WRAPPER) == WRAPPER_SHA
        assert digest(repo / BASE_DRIVER) == BASE_DRIVER_SHA
        assert digest(repo / DRIVER) == DRIVER_SHA
        base_driver_bytes = (repo / BASE_DRIVER).read_bytes()
        old_pin = ('EXPECTED_INPUT_SHA256 = "' + BASE_DRIVER_INPUT_SHA + '"').encode()
        new_pin = ('EXPECTED_INPUT_SHA256 = "' + MARKED_SHA + '"').encode()
        assert base_driver_bytes.count(old_pin) == 1
        assert base_driver_bytes.replace(old_pin, new_pin, 1) == (repo / DRIVER).read_bytes(), \
            'New driver must differ only by its static full-copy input hash'
        assert os.environ.get('LEAN_NUM_THREADS') == '2'
        for name in ['CoverHybridPhaseIntegral', 'HybridFiniteLeaf']:
            assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                    (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location('a2_frozen_public_phase_after_wrapper', repo / WRAPPER)
        assert spec is not None and spec.loader is not None
        wrapper = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(wrapper)
        marker_module = wrapper.load_marker_script(repo / MARKER_SCRIPT)
        original = (repo / SOURCE).read_bytes()
        baseline, candidate, marked, manifest, checks = wrapper.prepare(original, marker_module)
        assert hashlib.sha256(baseline).hexdigest() == BASELINE_MARKED_SHA
        assert hashlib.sha256(candidate).hexdigest() == CANDIDATE_SHA
        assert hashlib.sha256(marked).hexdigest() == MARKED_SHA and len(marked) == 45831
        assert len(manifest) == 61 and checks['marker_count'] == 61
        assert checks['two_way_reversal_verified']
        assert checks['public_warning_option_unchanged']
        assert checks['public_marker_removal_recovers_prior_60_marker_bytes']
        (evidence / 'ActualGaussFiniteLeaves.scoped-candidate.lean').write_bytes(candidate)
        (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
        (evidence / 'two_private_public_phase_wrapper.py').write_bytes((repo / WRAPPER).read_bytes())
        (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
        (evidence / 'MomEngineActualDiagCc98c8a2.lean').write_bytes(marked)
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / DRIVER).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        result.update(checks)
        result.update(diagnostic_source_sha256=MARKED_SHA, diagnostic_source_bytes=len(marked),
                      scoped_candidate_sha256=CANDIDATE_SHA, scoped_candidate_bytes=len(candidate),
                      baseline_marked_source_sha256=BASELINE_MARKED_SHA,
                      two_private_options_provider_and_public_after_markers_only=True)
        # A unique untracked input in the checkout preserves the proven Lean
        # package-root behavior. All emitted compiler products stay in /tmp.
        fd, name = tempfile.mkstemp(prefix='MomEngineActualPublicPhaseStackCc98_', suffix='.lean', dir=repo)
        compile_input = Path(name)
        with os.fdopen(fd, 'wb') as stream:
            stream.write(marked)
        temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-public-phase-stack-', dir='/tmp')
        output = Path(temporary.name)
        driver_evidence = evidence / 'driver'
        driver_evidence.mkdir()
        command = ['timeout', '--signal=TERM', '--kill-after=10s', '195s',
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
        # The established driver separately verifies and cleans up only its
        # same-user direct-child inferior. This fallback signals only our own
        # new outer timeout session; it never selects an existing process.
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
                if not driver_result.get('cleanup_complete', False):
                    code = 1
                    result['status'] = 'diagnostic_cleanup_failed'
            except (OSError, ValueError) as exc:
                code = 1
                result.update(status='unreadable_driver_result', report_error=repr(exc))
        elif result['driver_started']:
            code = 1
            result['status'] = 'missing_driver_result'
        result['source_unchanged'] = original is not None and (repo / SOURCE).read_bytes() == original
        result['marker_script_unchanged'] = digest(repo / MARKER_SCRIPT) == MARKER_SCRIPT_SHA
        result['driver_script_unchanged'] = digest(repo / DRIVER) == DRIVER_SHA
        result['base_driver_script_unchanged'] = digest(repo / BASE_DRIVER) == BASE_DRIVER_SHA
        result['wrapper_script_unchanged'] = digest(repo / WRAPPER) == WRAPPER_SHA
        if compile_input is not None:
            result['diagnostic_input_unchanged'] = digest(compile_input) == MARKED_SHA
            compile_input.unlink()
            result['temporary_input_removed'] = not compile_input.exists()
        if temporary is not None:
            output_path = Path(temporary.name)
            temporary.cleanup()
            result['temporary_output_removed'] = not output_path.exists()
        if not all(result.get(k, False) for k in
                   ['source_unchanged', 'marker_script_unchanged', 'driver_script_unchanged',
                    'base_driver_script_unchanged', 'wrapper_script_unchanged']):
            code = 1
        result.update(FALSE_FLAGS)
        result.update(elapsed_seconds=time.monotonic() - started, harness_exit_code=code)
        write_json(evidence / 'harness-result.json', result)
        print(json.dumps(result, ensure_ascii=False), flush=True)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
