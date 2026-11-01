#!/usr/bin/env python3
"""Observe one uninterrupted, unmodified MOM_ENGINE_STEP verifier process.

Snapshots are diagnostic log prefixes, never proof certificates.  The verifier
retains its normal Lake build, source checks, and fresh namespace axiom audit.
All children retain RUNNER_TRACKING_ID for the runner's normal job cleanup.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import tomllib


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def source_identity(repo: Path) -> dict:
    def git(*args: str) -> str:
        return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()

    if git('status', '--porcelain', '--untracked-files=no'):
        raise RuntimeError('Tracked checkout is not clean')
    paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=repo).split(b'\0')
    hashes = {}
    for raw in filter(None, paths):
        relative = os.fsdecode(raw)
        source = repo / relative
        if source.is_symlink():
            digest = hashlib.sha256(os.fsencode(os.readlink(source))).hexdigest()
        else:
            with source.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        hashes[relative] = digest
    task = repo / 'HeckeSkeleton/Moments/MOM_ENGINE_STEP'
    modules = sorted(path.name for path in task.glob('*.lean'))
    imports = [line.removeprefix('import ').strip()
               for line in (task / 'Interface.lean').read_text().splitlines()
               if line.startswith('import ')]
    libraries = [item['name'] for item in
                 tomllib.loads((repo / 'lakefile.toml').read_text())['lean_lib']]
    expected_imports = {'HeckeSkeleton.Moments.MOM_ENGINE_STEP.' + name.removesuffix('.lean')
                        for name in modules if name != 'Interface.lean'}
    if (len(modules) != 1009 or set(imports) != expected_imports
            or len(imports) != 1008 or len(libraries) != 20):
        raise RuntimeError('Full 1009-module / 1008-import / 20-library scope changed')
    return {'head': git('rev-parse', 'HEAD'), 'tree': git('rev-parse', 'HEAD^{tree}'),
            'tracked_sha256': hashes, 'task_modules': modules,
            'interface_imports': imports, 'libraries': libraries}


def process_state(pid: int) -> tuple[str, str, int, int] | None:
    try:
        fields = Path(f'/proc/{pid}/stat').read_text().rpartition(')')[2].split()
        # state, start time (field 22), process group, session
        return fields[0], fields[19], int(fields[2]), int(fields[3])
    except (FileNotFoundError, ProcessLookupError):
        return None


def group_members(process: dict, *, keep_self: bool = False) -> dict:
    leader = process_state(process['pid'])
    if leader is not None and leader[1] != process['start_ticks']:
        raise RuntimeError('Recorded supervisor PID was reused; refusing to signal it')
    members = {}
    for path in Path('/proc').iterdir():
        if not path.name.isdecimal():
            continue
        pid = int(path.name)
        state = process_state(pid)
        if (state is not None and state[0] != 'Z'
                and state[2:] == (process['pid'], process['pid'])
                and int(state[1]) >= int(process['start_ticks'])
                and not (keep_self and pid == os.getpid())):
            members[pid] = state
    return members


def stop_group(process: dict, *, keep_self: bool = False) -> None:
    """Stop only the recorded session/group, even if its leader exits first."""
    if keep_self:
        # The supervisor remains alive while it cleans up the native descendants.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
    deadline = time.monotonic() + 10
    while members := group_members(process, keep_self=keep_self):
        force = time.monotonic() >= deadline
        for pid, expected in members.items():
            # Recheck identity immediately before signalling each exact member.
            current = process_state(pid)
            if current is not None and current[1:] == expected[1:]:
                try:
                    os.kill(pid, signal.SIGKILL if force else signal.SIGTERM)
                except ProcessLookupError:
                    pass
        time.sleep(0.2)
        if time.monotonic() > deadline + 5:
            if group_members(process, keep_self=keep_self):
                raise RuntimeError('Native process group still has live members after cleanup')
            break


def alive(evidence: Path) -> bool:
    process = json.loads((evidence / 'process.json').read_text())
    current = process_state(process['pid'])
    return (current is not None and current[0] != 'Z'
            and current[1] == process['start_ticks'])


def observe(evidence: Path) -> dict | None:
    result_file = evidence / 'supervisor-result.json'
    if result_file.exists():
        return json.loads(result_file.read_text())
    if not alive(evidence):
        # A successful supervisor publishes its result atomically before exiting.
        if result_file.exists():
            return json.loads(result_file.read_text())
        result = {'status': 'failure', 'exit_code': 1, 'verifier_exit_code': None,
                  'error': 'Supervisor exited without a final verifier result'}
        atomic_json(result_file, result)
        return result
    return None


def supervise(repo: Path, evidence: Path) -> int:
    started = time.monotonic()
    child = None
    result = {'status': 'failure', 'exit_code': 1, 'verifier_exit_code': None,
              'source_unchanged': False}

    def interrupted(signum: int, _frame: object) -> None:
        raise RuntimeError(f'Supervisor interrupted by signal {signum}')

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        if process_state(os.getpid())[2:] != (os.getpid(), os.getpid()):
            raise RuntimeError('Supervisor must own its process group and session')
        initial = json.loads((evidence / 'source-before.json').read_text())
        command = [sys.executable, '-u',
                   'HeckeSkeleton/Moments/MOM_ENGINE_STEP/verify.py',
                   'HeckeSkeleton.Moments.MOM_ENGINE_STEP.Interface',
                   '--namespace', 'HeckeSkeleton.Moments.EngineStep',
                   '--declaration', 'HeckeSkeleton.Moments.EngineStep.paired_engine_step',
                   '--evidence', str(evidence)]
        atomic_json(evidence / 'command.json', {'command': command, 'cwd': str(repo)})
        child = subprocess.Popen(command, cwd=repo, stdin=subprocess.DEVNULL)
        result['verifier_exit_code'] = child.wait()
        final = source_identity(repo)
        atomic_json(evidence / 'source-after.json', final)
        result['source_unchanged'] = initial == final
        if not result['source_unchanged']:
            raise RuntimeError('Tracked source identity changed during verification')
        result['exit_code'] = (child.returncode if child.returncode >= 0
                               else 128 - child.returncode)
        result['status'] = 'success' if result['exit_code'] == 0 else 'failure'
    except BaseException as error:
        result['error'] = f'{type(error).__name__}: {error}'
    finally:
        try:
            current = process_state(os.getpid())
            group = {'pid': os.getpid(), 'start_ticks': current[1]}
            if group_members(group, keep_self=True):
                stop_group(group, keep_self=True)
            if child is not None:
                result['verifier_exit_code'] = child.wait(timeout=1)
        except BaseException as error:
            result.update(status='failure', exit_code=1,
                          cleanup_error=f'{type(error).__name__}: {error}')
        result['elapsed_seconds'] = time.monotonic() - started
        atomic_json(evidence / 'supervisor-result.json', result)
    return int(result['exit_code'])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['start', 'run', 'snapshot', 'wait', 'stop'])
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--evidence', type=Path, default=Path('mom-engine-step-b2-evidence'))
    parser.add_argument('--seconds', type=int, default=0)
    parser.add_argument('--destination', type=Path)
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()

    if args.mode == 'start':
        evidence.mkdir(parents=True, exist_ok=False)
        atomic_json(evidence / 'source-before.json', source_identity(repo))
        with (evidence / 'console.log').open('wb') as output:
            process = subprocess.Popen(
                [sys.executable, '-u', str(Path(__file__).resolve()), 'run',
                 '--repo', str(repo), '--evidence', str(evidence)], cwd=repo,
                stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT,
                start_new_session=True)
        current = process_state(process.pid)
        if current is None:
            raise RuntimeError('Supervisor exited before its identity was recorded')
        atomic_json(evidence / 'process.json', {'pid': process.pid, 'start_ticks': current[1]})
        print(f'Started one native verifier supervisor: {process.pid}', flush=True)
        return 0

    if args.mode == 'run':
        return supervise(repo, evidence)

    if args.mode == 'stop':
        if not (evidence / 'process.json').exists():
            return 0
        process = json.loads((evidence / 'process.json').read_text())
        stop_group(process)
        observe(evidence)
        return 0

    deadline = time.monotonic() + args.seconds
    result = observe(evidence)
    while result is None and (args.mode == 'wait' or time.monotonic() < deadline):
        time.sleep(min(15, max(0.1, deadline - time.monotonic()))
                   if args.mode == 'snapshot' else 15)
        result = observe(evidence)

    if args.mode == 'wait':
        print(json.dumps(result, indent=2), flush=True)
        return int(result['exit_code'])

    if args.destination is None:
        raise ValueError('snapshot requires --destination')
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    snapshot_hashes = {}
    for source in sorted(evidence.iterdir()):
        if not source.is_file() or source.name.endswith('.tmp'):
            continue
        # Copy a fixed-length prefix: appending output cannot make this copy grow.
        with source.open('rb') as incoming, (destination / source.name).open('wb') as outgoing:
            remaining = os.fstat(incoming.fileno()).st_size
            while remaining:
                chunk = incoming.read(min(remaining, 1024 * 1024))
                if not chunk:
                    break
                outgoing.write(chunk)
                remaining -= len(chunk)
        with (destination / source.name).open('rb') as stream:
            snapshot_hashes[source.name] = hashlib.file_digest(stream, 'sha256').hexdigest()
    atomic_json(destination / 'snapshot.json', {
        'diagnostic_snapshot_only': True, 'native_process_interrupted': False,
        'observed_at_unix': time.time(), 'final_result_observed': result,
        'snapshot_sha256': snapshot_hashes})
    if output_path := os.environ.get('GITHUB_OUTPUT'):
        with open(output_path, 'a') as output:
            output.write(f'running={str(result is None).lower()}\n')
    print(f'Copied diagnostic snapshot; native still running: {result is None}', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
