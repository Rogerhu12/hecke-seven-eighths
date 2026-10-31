#!/usr/bin/env python3
"""Optionally seed the strict source/object verifier from one pinned successful CI run.

The outer ZIP digest authenticates the complete checkpoint before extraction.
No Lake trace is created. Every reused object is subsequently checked again by
scripts/verify_low_hybrid_exterior.py against the current source/import/options
fingerprint and every emitted companion hash. Failed transport is optional.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.error
import urllib.parse
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[3]
BUILD = ROOT / '.lake/build'
OUT = BUILD / 'lib/lean'
STATE = BUILD / 'wire-low-hybrid-state.json'
REPOSITORY = 'Rogerhu12/hecke-seven-eighths'
RUN_ID = 41162593037
HEAD = 'c55f201b7e7922cf73574d2f2d236a08e4a69af2'
ARTIFACT_ID = 13027438048
ARTIFACT_NAME = 'low-hybrid-project-build-' + HEAD + '-1'
ZIP_SHA256 = 'fd46c071ba3c4694b76950cceab59b3d43a5c69d636f037872d3008acc20294e'
ZIP_SIZE = 429795975
ARCHIVE_NAME = 'low-hybrid-project-build.tar.zst'
MARKER = BUILD / 'mom-engine-step-checkpoint.json'
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def digest(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def relative_member(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or path.parts[:2] != ('.lake', 'build'):
        raise ValueError('Checkpoint member outside .lake/build: ' + name)
    return path


def inside(path: Path, directory: Path) -> None:
    if not path.resolve().is_relative_to(directory.resolve()):
        raise ValueError('Checkpoint destination escapes its build directory')


def read_state(path: Path) -> dict:
    if not path.is_file():
        return {}
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError('Invalid project object state')
    return value


def preserved_state() -> dict:
    """Preserve coherent existing objects; current source checks still follow."""
    valid = {}
    for module, row in read_state(STATE).items():
        if not MODULE.fullmatch(module) or not isinstance(row, dict):
            continue
        output = OUT / Path(*module.split('.')).with_suffix('.olean')
        inside(output, OUT)
        if row.get('exit_code') != 0 or not output.is_file() or not row.get('artifacts'):
            continue
        actual = {}
        for artifact in output.parent.glob(output.stem + '.*'):
            inside(artifact, OUT)
            if artifact.is_file():
                actual[str(artifact.relative_to(OUT))] = digest(artifact)
        if actual == row['artifacts']:
            valid[module] = row
    return valid


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, response, code, message, headers, newurl):
        return None


def download_zip(destination: Path, headers: dict) -> None:
    request = urllib.request.Request(
        f'https://api.github.com/repos/{REPOSITORY}/actions/artifacts/{ARTIFACT_ID}/zip',
        headers=headers)
    try:
        response = urllib.request.build_opener(NoRedirect).open(request, timeout=60)
    except urllib.error.HTTPError as error:
        if error.code not in (301, 302, 303, 307, 308):
            raise
        location = error.headers.get('Location', '')
        parsed = urllib.parse.urlsplit(location)
        host = parsed.hostname or ''
        if (parsed.scheme != 'https' or parsed.username or parsed.password or
                not (host.endswith('.blob.core.windows.net') or
                     host.endswith('.githubusercontent.com'))):
            raise ValueError('Unexpected artifact download redirect') from error
        # The repository token is never forwarded to the signed storage URL.
        response = urllib.request.urlopen(location, timeout=60)
    hasher = hashlib.sha256()
    count = 0
    with response, destination.open('wb') as stream:
        while chunk := response.read(1024 * 1024):
            count += len(chunk)
            if count > ZIP_SIZE + 1024 * 1024:
                raise ValueError('Oversized checkpoint ZIP')
            hasher.update(chunk)
            stream.write(chunk)
    if hasher.hexdigest() != ZIP_SHA256:
        raise ValueError('The checkpoint ZIP digest does not match the pinned artifact')


def extract_checked(archive: Path, staging: Path) -> None:
    total = 0
    process = subprocess.Popen(['zstd', '-dc', str(archive)], stdout=subprocess.PIPE)
    assert process.stdout is not None
    try:
        with tarfile.open(fileobj=process.stdout, mode='r|') as tar:
            for member in tar:
                relative = relative_member(member.name)
                total += member.size
                if member.size < 0 or total > 32 * 1024 ** 3:
                    raise ValueError('Oversized expanded checkpoint')
                selected = (relative.parts[:4] == ('.lake', 'build', 'lib', 'lean') or
                            relative.as_posix() == '.lake/build/wire-low-hybrid-state.json')
                if not selected or member.isdir():
                    continue
                if not member.isfile():
                    raise ValueError('Nonregular selected checkpoint member')
                target = staging / relative
                inside(target, staging)
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
    except BaseException:
        process.kill()
        process.wait()
        raise
    finally:
        process.stdout.close()
    if process.wait() != 0:
        raise ValueError('Checkpoint decompression failed')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', type=Path, default=ROOT / 'mom-engine-step-verification')
    args = parser.parse_args()
    args.evidence.mkdir(parents=True, exist_ok=True)
    report = {'repository': REPOSITORY, 'run_id': RUN_ID, 'head_sha': HEAD,
              'artifact_id': ARTIFACT_ID, 'artifact_name': ARTIFACT_NAME,
              'zip_sha256': ZIP_SHA256}
    if MARKER.is_file() and STATE.is_file():
        prior = json.loads(MARKER.read_text())
        if prior.get('zip_sha256') == ZIP_SHA256:
            report['status'] = 'Previously seeded; all current source/object checks remain mandatory'
            (args.evidence / 'checkpoint.json').write_text(json.dumps(report, indent=2) + '\n')
            print(report['status'], flush=True)
            return 0
    token = os.environ.get('MOM_CHECKPOINT_TOKEN', '')
    if not token:
        raise ValueError('No read-only GitHub token for the optional checkpoint')
    headers = {'Authorization': 'Bearer ' + token, 'Accept': 'application/vnd.github+json',
               'X-GitHub-Api-Version': '2022-11-28'}

    def get(resource: str):
        request = urllib.request.Request(
            f'https://api.github.com/repos/{REPOSITORY}/actions/{resource}', headers=headers)
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.load(response)

    run = get(f'runs/{RUN_ID}')
    artifact = get(f'artifacts/{ARTIFACT_ID}')
    if (run.get('id') != RUN_ID or run.get('event') != 'push' or
            run.get('head_sha') != HEAD or run.get('status') != 'completed' or
            run.get('conclusion') != 'success' or artifact.get('id') != ARTIFACT_ID or
            artifact.get('name') != ARTIFACT_NAME or artifact.get('expired', True) or
            artifact.get('digest') != 'sha256:' + ZIP_SHA256 or
            artifact.get('workflow_run', {}).get('id') != RUN_ID):
        raise ValueError('Pinned successful push checkpoint metadata differs')
    preserved = preserved_state()
    with tempfile.TemporaryDirectory(prefix='mom-engine-checkpoint-', dir=os.environ.get('RUNNER_TEMP')) as temporary:
        temporary = Path(temporary)
        zipped = temporary / 'checkpoint.zip'
        download_zip(zipped, headers)
        archive = temporary / ARCHIVE_NAME
        with zipfile.ZipFile(zipped) as bundle:
            entries = bundle.infolist()
            if len(entries) != 1 or entries[0].filename != ARCHIVE_NAME or entries[0].is_dir():
                raise ValueError('Unexpected checkpoint ZIP inventory')
            with bundle.open(entries[0]) as source, archive.open('wb') as output:
                shutil.copyfileobj(source, output)
        staging = temporary / 'staging'
        extract_checked(archive, staging)
        staged_state = staging / '.lake/build/wire-low-hybrid-state.json'
        incoming = read_state(staged_state)
        if not incoming:
            raise ValueError('Missing authenticated source/object verification state')
        published = 0
        staged_out = staging / '.lake/build/lib/lean'
        for source in staged_out.rglob('*'):
            if not source.is_file():
                continue
            relative = source.relative_to(staged_out)
            module = '.'.join((*relative.parts[:-1], relative.name.split('.', 1)[0]))
            if module in preserved:
                continue
            target = OUT / relative
            inside(target, OUT)
            target.parent.mkdir(parents=True, exist_ok=True)
            os.replace(source, target)
            published += 1
        incoming.update(preserved)
        BUILD.mkdir(parents=True, exist_ok=True)
        state_tmp = STATE.with_suffix('.json.checkpoint-tmp')
        state_tmp.write_text(json.dumps(incoming, indent=2) + '\n')
        os.replace(state_tmp, STATE)
        report.update(status='Seeded; reuse still requires current source/import/options/object checks',
                      published_files=published, preserved_modules=len(preserved),
                      candidate_modules=len(incoming))
        MARKER.write_text(json.dumps(report, indent=2) + '\n')
    (args.evidence / 'checkpoint.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
