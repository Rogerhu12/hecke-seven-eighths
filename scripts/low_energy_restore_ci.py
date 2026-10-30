#!/usr/bin/env python3
"""Optionally restore this workflow's earlier compiled artifacts after a cache miss.

Only OUT and JSON/log records are copied. No downloaded program is executed.
low_energy_verify.py still checks each source, dependency, output, and audit hash
before accepting any restored module. An unavailable checkpoint is a cache miss.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
import stat
import tempfile
import urllib.error
import urllib.parse
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
OUT_PREFIX = '.lake/build/lib/lean/'
LOG_PREFIX = '.low-energy-verification/'
SUFFIXES = ('.olean.private', '.olean.server', '.ir.sig', '.olean', '.ir')
MAX_ARCHIVE = 512 * 1024 * 1024
MAX_EXPANDED = 1024 * 1024 * 1024


class RestoreError(Exception):
    """A message that is safe to show without a token or signed URL."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def allowed_member(info):
    name = info.filename
    path = PurePosixPath(name)
    if (path.is_absolute() or '..' in path.parts or '\\' in name or
            '\x00' in name or ':' in name):
        raise RestoreError('Checkpoint contains an unsafe ZIP path.')
    if stat.S_ISLNK(info.external_attr >> 16):
        raise RestoreError('Checkpoint contains a symbolic link.')
    if info.is_dir():
        prefix = name.rstrip('/') + '/'
        if any(prefix.startswith(p) or p.startswith(prefix) for p in (OUT_PREFIX, LOG_PREFIX)):
            return False
        raise RestoreError('Checkpoint contains a directory outside OUT and LOG.')
    if name.startswith(OUT_PREFIX):
        relative = name[len(OUT_PREFIX):]
        suffix = next((s for s in SUFFIXES if relative.endswith(s)), None)
        if suffix and all(part.isidentifier() for part in relative[:-len(suffix)].split('/')):
            return True
        raise RestoreError('Checkpoint contains an unexpected compiled filename.')
    if name.startswith(LOG_PREFIX):
        relative = name[len(LOG_PREFIX):]
        # The verifier rewrites its final audit source; never restore executable input.
        if relative == 'CompletedMarkedEnergyAudit.lean':
            return False
        if re.fullmatch(r'[A-Za-z0-9_.-]+\.(json|log)', relative):
            return True
        raise RestoreError('Checkpoint contains an unexpected verification filename.')
    raise RestoreError('Checkpoint contains a file outside OUT and LOG.')


def restore_archive(archive, expected_digest=None):
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    if expected_digest and expected_digest != 'sha256:' + digest:
        raise RestoreError('Checkpoint ZIP digest does not match GitHub metadata.')
    with zipfile.ZipFile(archive) as zipped:
        entries = zipped.infolist()
        if len(entries) > 20000 or sum(i.file_size for i in entries) > MAX_EXPANDED:
            raise RestoreError('Checkpoint exceeds the extraction limit.')
        if len({i.filename for i in entries}) != len(entries):
            raise RestoreError('Checkpoint contains duplicate ZIP paths.')
        selected = [i for i in entries if allowed_member(i)]
        for info in selected:
            destination = ROOT / info.filename
            permitted = ROOT / (OUT_PREFIX if info.filename.startswith(OUT_PREFIX) else LOG_PREFIX)
            if not destination.resolve().is_relative_to(permitted.resolve()) or destination.is_symlink():
                raise RestoreError('A checkpoint destination escapes its allowed directory.')
            # Do not follow existing symlinks in the output directory hierarchy.
            if any(p.is_symlink() for p in [permitted, *destination.parents]
                    if p.is_relative_to(ROOT)):
                raise RestoreError('A checkpoint destination contains a symbolic link.')
        for info in selected:
            destination = ROOT / info.filename
            destination.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as temporary:
                temporary.write(zipped.read(info))
                temporary_path = Path(temporary.name)
            temporary_path.replace(destination)
    return len(selected), digest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('phase', choices=['core', 'actual'])
    args = ap.parse_args()
    repository = os.environ.get('GITHUB_REPOSITORY', '')
    branch = os.environ.get('GITHUB_HEAD_REF') or os.environ.get('GITHUB_REF_NAME', '')
    current = os.environ.get('GITHUB_RUN_ID', '')
    token = os.environ.get('GITHUB_TOKEN', '')
    if not token or not current.isdigit() or not branch or not re.fullmatch(
            r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
        print('Checkpoint fallback unavailable: no complete GitHub run context.')
        return 0
    api = 'https://api.github.com/repos/' + repository
    opener = urllib.request.build_opener(NoRedirect())

    def request(url):
        if not url.startswith(api + '/'):
            raise RestoreError('Unexpected GitHub API endpoint.')
        return opener.open(urllib.request.Request(url, headers={
            'Authorization': 'Bearer ' + token, 'Accept': 'application/vnd.github+json',
            'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'low-energy-verification',
        }), timeout=45)

    def get_json(url):
        with request(url) as response:
            return json.load(response)

    try:
        query = urllib.parse.urlencode({'branch': branch, 'status': 'completed', 'per_page': 20})
        runs = get_json(api + '/actions/workflows/low-energy-verify.yml/runs?' + query)
        selected = None
        for run in runs.get('workflow_runs', []):
            if (run.get('head_branch') != branch or run.get('status') != 'completed' or
                    int(run['id']) >= int(current) or run.get('repository', {}).get('full_name') != repository or
                    run.get('head_repository', {}).get('full_name') != repository or
                    run.get('path', '').split('@', 1)[0] != '.github/workflows/low-energy-verify.yml'):
                continue
            artifacts = get_json(api + '/actions/runs/' + str(run['id']) + '/artifacts?per_page=100')
            artifact = next((a for a in artifacts.get('artifacts', []) if
                a.get('name') == 'low-energy-compiled-' + args.phase and
                not a.get('expired') and 0 < a.get('size_in_bytes', 0) <= MAX_ARCHIVE), None)
            if artifact:
                selected = run, artifact
                break
        if selected is None:
            print('No previous completed run has an unexpired checkpoint for this phase.')
            return 0
        run, artifact = selected
        # GitHub redirects ZIP downloads to signed storage. Never forward the API token.
        try:
            response = request(api + '/actions/artifacts/' + str(artifact['id']) + '/zip')
        except urllib.error.HTTPError as error:
            if error.code not in (301, 302, 303, 307, 308):
                raise
            location = error.headers.get('Location', '')
            parsed = urllib.parse.urlparse(location)
            if (parsed.scheme != 'https' or parsed.username or parsed.password or
                    not parsed.hostname or not parsed.hostname.endswith(
                        ('.blob.core.windows.net', '.githubusercontent.com', '.github.com'))):
                raise RestoreError('Unexpected artifact storage redirect.')
            response = urllib.request.urlopen(location, timeout=90)
        with tempfile.TemporaryDirectory(prefix='low-energy-checkpoint-') as directory:
            archive = Path(directory) / 'checkpoint.zip'
            with response, archive.open('wb') as output:
                total = 0
                while chunk := response.read(1024 * 1024):
                    total += len(chunk)
                    if total > MAX_ARCHIVE:
                        raise RestoreError('Checkpoint download exceeds its size limit.')
                    output.write(chunk)
            count, digest = restore_archive(archive, artifact.get('digest'))
        provenance = {'run_id': run['id'], 'head_sha': run.get('head_sha'),
            'artifact_id': artifact['id'], 'archive_sha256': digest, 'files': count,
            'status': 'restored_unverified; per-module verification is mandatory'}
        log = ROOT / LOG_PREFIX
        log.mkdir(parents=True, exist_ok=True)
        (log / 'checkpoint_restore.json').write_text(json.dumps(provenance, indent=2) + '\n')
        print(f'Restored {count} checkpoint files from run {run["id"]}, artifact {artifact["id"]}.')
        print('The verifier must validate each source, dependency, output and audit before reuse.')
    except RestoreError as error:
        print('Checkpoint fallback unavailable: ' + str(error))
    except Exception as error:
        # Do not expose exception URLs, which can contain temporary signed credentials.
        print('Checkpoint fallback unavailable (' + type(error).__name__ + '); building real sources.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
