#!/usr/bin/env python3
"""Run the frozen full-copy cc98 stack diagnostic after normal Lake dependencies."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
MARKER_SCRIPT = Path('.github/scripts/mom-engine-step-a2-diagnostic.py')
MARKER_SCRIPT_SHA = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
DRIVER = Path('.github/scripts/mom-engine-step-a2-deep-stack-driver.py')
DRIVER_SHA = 'f306f3a188dd994fabe5eadc2cf848502555081edc460c8f57a86be64ab4538e'
MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
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
    result = {**FALSE_FLAGS, 'scope': 'Deep stack diagnostic of a full reversible source copy',
              'source_sha256': SOURCE_SHA, 'marker_script_sha256': MARKER_SCRIPT_SHA,
              'driver_sha256': DRIVER_SHA, 'stderr_option_override': False,
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
        assert digest(repo / DRIVER) == DRIVER_SHA
        assert os.environ.get('LEAN_NUM_THREADS') == '2'
        for name in ['CoverHybridPhaseIntegral', 'HybridFiniteLeaf']:
            assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                    (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
        spec = importlib.util.spec_from_file_location('a2_frozen_cc98_markers', repo / MARKER_SCRIPT)
        module = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(module)
        original = (repo / SOURCE).read_bytes()
        marked, manifest, checks = module.instrument(original)
        assert hashlib.sha256(marked).hexdigest() == MARKED_SHA
        (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
        (evidence / 'MomEngineActualDiagCc98c8a2.lean').write_bytes(marked)
        (evidence / 'lean_gdb_parent_driver.py').write_bytes((repo / DRIVER).read_bytes())
        write_json(evidence / 'marker-manifest.json', manifest)
        result.update(checks)
        result['diagnostic_source_sha256'] = MARKED_SHA
        # A unique untracked input in the checkout preserves the proven Lean
        # package-root behavior. All emitted compiler products stay in /tmp.
        fd, name = tempfile.mkstemp(prefix='MomEngineActualDeepStackCc98_', suffix='.lean', dir=repo)
        compile_input = Path(name)
        with os.fdopen(fd, 'wb') as stream:
            stream.write(marked)
        temporary = tempfile.TemporaryDirectory(prefix='mom-engine-a2-deep-stack-', dir='/tmp')
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
        if compile_input is not None:
            result['diagnostic_input_unchanged'] = digest(compile_input) == MARKED_SHA
            compile_input.unlink()
            result['temporary_input_removed'] = not compile_input.exists()
        if temporary is not None:
            output_path = Path(temporary.name)
            temporary.cleanup()
            result['temporary_output_removed'] = not output_path.exists()
        if not all(result.get(k, False) for k in
                   ['source_unchanged', 'marker_script_unchanged', 'driver_script_unchanged']):
            code = 1
        result.update(FALSE_FLAGS)
        result.update(elapsed_seconds=time.monotonic() - started, harness_exit_code=code)
        write_json(evidence / 'harness-result.json', result)
        print(json.dumps(result, ensure_ascii=False), flush=True)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
