#!/usr/bin/env python3
"""Optionally seed an untouched island of genuine, pinned native Lake dependencies.

After the normal pinned toolchain/Mathlib setup and checkpoint restore, run:
    GITHUB_TOKEN=... python3 scripts/low_energy_native_foundation.py actual
For a read-only source and protected-output inventory, run:
    python3 scripts/low_energy_native_foundation.py actual --plan-only

This is a cache transport and Lake revalidation step, not a proof gate. It never
creates schema-2 direct-compiler records. Original successful foundation archives
are authenticated by immutable IDs, SHA-256 digests, producing jobs, and source
pins. Every selected local dependency must be another selected module; every
existing OUT .olean, every new source, and Principal are excluded.

The genuine traces and complete native output companions are restored temporarily
at their original package paths. `lake --rehash --no-cache --no-build build ...`
must succeed without rebuilding before native-lake-foundation-v1 evidence is
written. Recorded dependency SHA-256 values are observations AFTER this current
validation, never purported original direct-compiler receipts. The ordinary
source, axiom, Principal, and completedMarkedEnergy checks remain mandatory.

Unavailable archives, changed sources, invalid traces, and any other failure are
cache misses. Only files installed/created by this invocation are removed. A
pre-existing native receipt and its log are left for the verifier to validate.
"""
from __future__ import annotations

import argparse
import base64
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile

from lean_imports import imports as lean_imports


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/build/lib/lean'
LOG = ROOT / '.low-energy-verification'
CATALOG = ROOT / 'docs/low-energy/native_foundation_catalog.json'
CATALOG_SHA256 = 'bc9f033a972d4133ce3ff3ffb9c0328cae42eafdc8d9e147d36e6a0166d5cf0c'
SCHEMA = 'native-lake-foundation-v1'
CATALOG_SCHEMA = 'native-lake-foundation-catalog-v1'
CONFIG_FILES = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                'vendor/class-field-theory/lakefile.toml')
RUNTIME_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')
BUILD_ROOTS = ('.lake/build', 'vendor/class-field-theory/.lake/build')
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
BASE_SUFFIXES = (*RUNTIME_SUFFIXES, '.ilean', '.trace', '.c', '.bc', '.ltar',
                 '.setup.json', '.c.o', '.c.o.trace', '.o', '.o.trace')
ARCHIVE_SUFFIXES = tuple(sorted({*BASE_SUFFIXES,
    *(suffix + '.hash' for suffix in BASE_SUFFIXES)}, key=len, reverse=True))
KEEP_SUFFIXES = {*RUNTIME_SUFFIXES, '.ilean', '.trace', '.c', '.bc',
    *(suffix + '.hash' for suffix in (*RUNTIME_SUFFIXES, '.ilean', '.c', '.bc'))}
CHUNK = 1024 * 1024
MAX_METADATA = 8 * 1024 * 1024
VALIDATION_PREFIX = ['lake', '--rehash', '--no-cache', '--no-build', 'build']


class FoundationError(Exception):
    """A safe diagnostic that contains neither tokens nor storage URLs."""


def digest(path: Path) -> str:
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def module_stem(module: str) -> Path:
    if not MODULE_RE.fullmatch(module):
        raise FoundationError('Invalid module name in the native catalog.')
    return Path(*module.split('.'))


def artifact_path(directory: Path, module: str, suffix: str) -> Path:
    stem = directory / module_stem(module)
    return stem.with_name(stem.name + suffix)


def exists(path: Path) -> bool:
    return path.exists() or path.is_symlink()


def plain_path(root: Path, path: Path) -> None:
    """Reject a destination outside root or through an existing symbolic link."""
    try:
        relative = path.relative_to(root)
    except ValueError:
        raise FoundationError('Native output escapes the repository.') from None
    if root.is_symlink():
        raise FoundationError('The native output root is a symbolic link.')
    current = root
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise FoundationError('A native output destination contains a symbolic link.')


def create_copy(root: Path, origin: Path, destination: Path,
                installed: list[Path]) -> None:
    """Exclusive creation is essential: never replace an existing artifact."""
    plain_path(root, destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    try:
        with destination.open('xb') as output:
            installed.append(destination)
            with origin.open('rb') as source:
                shutil.copyfileobj(source, output, CHUNK)
        os.chmod(destination, 0o644)
    except FileExistsError:
        raise FoundationError('A protected or concurrent output already exists: ' +
                              destination.relative_to(root).as_posix()) from None


def load_catalog(path: Path = CATALOG) -> tuple[dict, str]:
    raw = path.read_bytes()
    current = hashlib.sha256(raw).hexdigest()
    if current != CATALOG_SHA256:
        raise FoundationError('The pinned native catalog digest does not match.')
    catalog = json.loads(raw)
    if (catalog.get('schema') != CATALOG_SCHEMA or
            set(catalog.get('config_sha256', {})) != set(CONFIG_FILES)):
        raise FoundationError('Unexpected native catalog schema or configuration set.')
    return catalog, current


def config_hashes(root: Path, catalog: dict) -> dict[str, str]:
    hashes = {name: digest(root / name) for name in CONFIG_FILES}
    if hashes != catalog['config_sha256']:
        raise FoundationError('Current configuration differs from the native foundation.')
    return hashes


@dataclass
class Plan:
    nodes: dict[str, dict]
    selected: set[str]
    leaves: list[str]
    protected: set[str]
    artifacts: list[int]
    skipped: dict[str, str]


def make_plan(root: Path, catalog: dict, targets: list[str],
              source_roots: list[Path], new_sources: set[str]) -> Plan:
    """Compute a closed native island with no path into an existing OUT module."""
    out = root / '.lake/build/lib/lean'
    plain_path(root, out)
    protected = {path.relative_to(out).as_posix()[:-6].replace('/', '.')
                 for path in out.rglob('*.olean')} if out.is_dir() else set()
    nodes, active, found = {}, set(), {}

    def resolve(module):
        if module not in found:
            relative = module_stem(module).with_suffix('.lean')
            found[module] = next((directory / relative for directory in source_roots
                                  if (directory / relative).is_file()), None)
        return found[module]

    def visit(module):
        if module in nodes:
            return
        source = resolve(module)
        if source is None:
            return  # Lake itself must authenticate external imports at the gate.
        if module in active:
            raise FoundationError('A source import cycle prevents native planning.')
        active.add(module)
        raw = source.read_bytes()
        dependencies = lean_imports(raw.decode('utf-8-sig'))
        for dependency in dependencies:
            visit(dependency)
        nodes[module] = {'source': source, 'source_sha256': hashlib.sha256(raw).hexdigest(),
                         'deps': dependencies}
        active.remove(module)

    for target in targets:
        if resolve(target) is None:
            raise FoundationError('Missing actual source target: ' + target)
        visit(target)
    eligible, skipped = {}, {}

    def check(module):
        if module in eligible:
            return eligible[module]
        eligible[module] = False
        row = catalog['modules'].get(module)
        node = nodes[module]
        relative = node['source'].relative_to(root).as_posix()
        reason = None
        if module in protected:
            reason = 'existing_OUT_olean'
        elif relative in new_sources or module == 'HeckeSkeleton.Principal' or module in targets:
            reason = 'mandatory_direct_source'
        elif row is None:
            reason = 'absent_from_pinned_catalog'
        elif row['source'] != relative or row['source_sha256'] != node['source_sha256']:
            reason = 'source_or_source_root_changed'
        elif row['build_root'] not in BUILD_ROOTS:
            raise FoundationError('Unrecognized native package build root.')
        else:
            # Besides OUT, protect any existing genuine Lake package outputs.
            for directory in ('lib/lean', 'ir'):
                stem = root / row['build_root'] / directory / module_stem(module)
                plain_path(root, stem)
                if any(stem.parent.glob(stem.name + '.*')):
                    reason = 'existing_native_package_output'
                    break
        if reason:
            skipped[module] = reason
            return False
        for dependency in node['deps']:
            if dependency in nodes and not check(dependency):
                skipped[module] = 'ineligible_local_dependency: ' + dependency
                return False
        eligible[module] = True
        return True

    selected = {module for module in nodes if check(module)}
    used = {dependency for module in selected for dependency in nodes[module]['deps']
            if dependency in selected}
    artifacts = sorted({catalog['modules'][module]['artifact_id'] for module in selected})
    return Plan(nodes, selected, sorted(selected - used), protected, artifacts, skipped)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class GitHub:
    def __init__(self, catalog: dict):
        repository = os.environ.get('GITHUB_REPOSITORY', '')
        self.token = os.environ.get('GITHUB_TOKEN', '')
        if repository != catalog['repository'] or not self.token:
            raise FoundationError('No matching GitHub repository/token context for native restore.')
        self.api = 'https://api.github.com/repos/' + repository
        self.opener = urllib.request.build_opener(NoRedirect())

    def request(self, path):
        if not path.startswith('/') or '..' in path:
            raise FoundationError('Invalid pinned GitHub API path.')
        return self.opener.open(urllib.request.Request(self.api + path, headers={
            'Authorization': 'Bearer ' + self.token,
            'Accept': 'application/vnd.github+json',
            'X-GitHub-Api-Version': '2022-11-28',
            'User-Agent': 'low-energy-native-foundation',
        }), timeout=60)

    def get(self, path):
        with self.request(path) as response:
            raw = response.read(MAX_METADATA + 1)
        if len(raw) > MAX_METADATA:
            raise FoundationError('GitHub metadata exceeds its size limit.')
        return json.loads(raw)

    def check_producer(self, catalog):
        run = self.get('/actions/runs/' + str(catalog['run_id']))
        if (run.get('id') != catalog['run_id'] or run.get('head_sha') != catalog['head_sha'] or
                run.get('path', '').split('@', 1)[0] != catalog['workflow_path'] or
                run.get('repository', {}).get('id') != catalog['repository_id'] or
                run.get('head_repository', {}).get('id') != catalog['repository_id']):
            raise FoundationError('The original workflow/source identity does not match.')
        # The overall workflow failed in a later stage. Only the specifically
        # pinned successful producing jobs are admitted, checked below.
        for field in ('source_exporter', 'producing_workflow'):
            expected = catalog[field]
            entry = self.get('/contents/' + expected['path'] + '?ref=' + catalog['head_sha'])
            if entry.get('sha') != expected['git_blob'] or entry.get('encoding') != 'base64':
                raise FoundationError('The pinned native producer source does not match.')
            content = base64.b64decode(entry['content'])
            git_blob = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
            if git_blob != expected['git_blob'] or ('sha256' in expected and
                    hashlib.sha256(content).hexdigest() != expected['sha256']):
                raise FoundationError('Native producer source bytes do not match their pin.')

    def download(self, catalog, artifact_id, destination):
        pin = catalog['artifacts'][str(artifact_id)]
        job = self.get('/actions/jobs/' + str(pin['job_id']))
        if (job.get('id') != pin['job_id'] or job.get('run_id') != catalog['run_id'] or
                job.get('head_sha') != catalog['head_sha'] or job.get('name') != pin['job_name'] or
                job.get('status') != 'completed' or job.get('conclusion') != 'success'):
            raise FoundationError('The pinned native producing job is not a successful matching job.')
        info = self.get('/actions/artifacts/' + str(artifact_id))
        run = info.get('workflow_run', {})
        if (info.get('id') != artifact_id or info.get('name') != pin['name'] or
                info.get('size_in_bytes') != pin['size_bytes'] or info.get('expired') is not False or
                info.get('digest') != 'sha256:' + pin['outer_sha256'] or
                run.get('id') != catalog['run_id'] or run.get('head_sha') != catalog['head_sha'] or
                run.get('repository_id') != catalog['repository_id'] or
                run.get('head_repository_id') != catalog['repository_id']):
            raise FoundationError('Pinned native artifact metadata does not match or has expired.')
        try:
            response = self.request('/actions/artifacts/' + str(artifact_id) + '/zip')
        except urllib.error.HTTPError as error:
            if error.code not in (301, 302, 303, 307, 308):
                raise
            location = error.headers.get('Location', '')
            # No Authorization header is ever sent to artifact storage.
            for _ in range(4):
                parsed = urllib.parse.urlparse(location)
                if (parsed.scheme != 'https' or parsed.username or parsed.password or
                        not parsed.hostname or not parsed.hostname.endswith(
                            ('.blob.core.windows.net', '.githubusercontent.com', '.github.com'))):
                    raise FoundationError('Unexpected artifact storage redirect.')
                try:
                    response = self.opener.open(location, timeout=90)
                    break
                except urllib.error.HTTPError as redirect:
                    if redirect.code not in (301, 302, 303, 307, 308):
                        raise
                    location = redirect.headers.get('Location', '')
            else:
                raise FoundationError('Too many artifact storage redirects.')
        total, hasher = 0, hashlib.sha256()
        with response, destination.open('xb') as output:
            while chunk := response.read(CHUNK):
                total += len(chunk)
                if total > pin['size_bytes']:
                    raise FoundationError('Native artifact download exceeds its pinned size.')
                hasher.update(chunk)
                output.write(chunk)
        if total != pin['size_bytes'] or hasher.hexdigest() != pin['outer_sha256']:
            raise FoundationError('Native artifact ZIP bytes differ from their pinned digest.')


def archive_member(name: str) -> tuple[str, str, str]:
    """Return build-root/module/suffix only for an ordinary module output path."""
    path = PurePosixPath(name)
    if (path.is_absolute() or '..' in path.parts or '\\' in name or '\0' in name or
            ':' in name or path.as_posix() != name):
        raise FoundationError('Unsafe path in a native archive.')
    for build in BUILD_ROOTS:
        for directory in ('lib/lean', 'ir'):
            prefix = build + '/' + directory + '/'
            if not name.startswith(prefix):
                continue
            relative = name[len(prefix):]
            suffix = next((suffix for suffix in ARCHIVE_SUFFIXES if relative.endswith(suffix)), None)
            if suffix:
                module = relative[:-len(suffix)].replace('/', '.')
                if MODULE_RE.fullmatch(module):
                    if (directory == 'lib/lean' and suffix.startswith(('.c', '.bc', '.setup'))) or (
                            directory == 'ir' and not suffix.startswith(('.c', '.bc', '.setup', '.o'))):
                        break
                    return build, module, suffix
    raise FoundationError('A native archive member is not an allowed compiled output.')


def extract_bundle(archive: Path, stage: Path, catalog: dict, artifact_id: int,
                   selected: set[str]) -> dict[str, str]:
    """Authenticate the full bundle, then stream only the selected genuine files."""
    pin = catalog['artifacts'][str(artifact_id)]
    if archive.stat().st_size != pin['size_bytes'] or digest(archive) != pin['outer_sha256']:
        raise FoundationError('Native archive digest changed before extraction.')
    manifest_pin = pin['manifest']
    stem = f"foundation-{manifest_pin['upper']}-{manifest_pin['shard']}"
    manifest_name, bundle_name = stem + '.manifest.json', stem + '.tar.gz'
    hashes, seen, count, expanded = {}, set(), 0, 0
    with zipfile.ZipFile(archive) as zipped:
        infos = zipped.infolist()
        if len(infos) != 2 or {info.filename for info in infos} != {manifest_name, bundle_name}:
            raise FoundationError('Unexpected native ZIP members or duplicate names.')
        for info in infos:
            mode = info.external_attr >> 16
            if info.is_dir() or (stat.S_IFMT(mode) and not stat.S_ISREG(mode)):
                raise FoundationError('Non-regular native ZIP member.')
        if zipped.getinfo(manifest_name).file_size > 65536:
            raise FoundationError('Native archive manifest exceeds its size limit.')
        manifest = json.loads(zipped.read(manifest_name))
        if manifest != manifest_pin:
            raise FoundationError('Native archive manifest differs from its exact pin.')
        # The pinned uploader uses compression-level 0. A modest bounded
        # allowance also tolerates an outer ZIP that recompresses the gzip
        # member; security still rests on its exact independent SHA-256 pin.
        inner_limit = min(pin['expanded_bytes'] + CHUNK, pin['size_bytes'] * 2 + CHUNK)
        if zipped.getinfo(bundle_name).file_size > inner_limit:
            raise FoundationError('Inner native archive exceeds its size limit.')
        with zipped.open(bundle_name) as stream:
            if hashlib.file_digest(stream, 'sha256').hexdigest() != manifest['archive_sha256']:
                raise FoundationError('Inner native archive digest does not match.')
        with zipped.open(bundle_name) as stream, tarfile.open(fileobj=stream, mode='r|gz') as bundle:
            for member in bundle:
                if not member.isfile() or member.name in seen:
                    raise FoundationError('Non-regular or duplicate native TAR member.')
                build, module, suffix = archive_member(member.name)
                seen.add(member.name)
                count += 1
                expanded += member.size
                if (count > manifest['file_count'] or member.size < 0 or
                        expanded > pin['expanded_bytes']):
                    raise FoundationError('Native archive exceeds its pinned inventory.')
                if module not in selected:
                    continue
                row = catalog['modules'][module]
                if row['artifact_id'] != artifact_id or row['build_root'] != build:
                    raise FoundationError('Native archive module ownership does not match.')
                if suffix not in KEEP_SUFFIXES:
                    continue  # In particular, never write the enormous setup JSON.
                destination = stage / member.name
                plain_path(stage, destination)
                destination.parent.mkdir(parents=True, exist_ok=True)
                hasher, total = hashlib.sha256(), 0
                with bundle.extractfile(member) as source, destination.open('xb') as output:
                    while chunk := source.read(CHUNK):
                        total += len(chunk)
                        if total > member.size:
                            raise FoundationError('Expanded native member exceeds its declared size.')
                        hasher.update(chunk)
                        output.write(chunk)
                if total != member.size:
                    raise FoundationError('Truncated native archive member.')
                value = hasher.hexdigest()
                if suffix in RUNTIME_SUFFIXES:
                    expected = row['artifacts'].get(suffix)
                    if expected is None or expected['size_bytes'] != total or expected['sha256'] != value:
                        raise FoundationError('A native runtime companion fails its exact catalog hash.')
                hashes[member.name] = value
        if count != manifest['file_count'] or expanded != pin['expanded_bytes']:
            raise FoundationError('Native archive inventory is incomplete.')
    for module in selected:
        row = catalog['modules'][module]
        for suffix in (*row['artifacts'], '.trace', '.ilean'):
            name = artifact_path(Path(row['build_root']) / 'lib/lean', module, suffix).as_posix()
            if name not in hashes:
                raise FoundationError('A selected native module has incomplete genuine companions: ' + module)
        name = artifact_path(Path(row['build_root']) / 'ir', module, '.c').as_posix()
        if name not in hashes:
            raise FoundationError('A selected native module has no genuine C companion: ' + module)
    return hashes


def runtime_hashes(out: Path, module: str) -> dict[str, str]:
    hashes = {}
    for suffix in RUNTIME_SUFFIXES:
        path = artifact_path(out, module, suffix)
        if path.is_file() and not path.is_symlink():
            hashes[suffix] = digest(path)
    if '.olean' not in hashes:
        raise FoundationError('A validated native dependency has no regular olean: ' + module)
    return hashes


def scoped_files(root: Path, catalog: dict, plan: Plan) -> set[Path]:
    """Lake may create fresh .hash or .trace.nobuild files for our empty stems."""
    result = set()
    for module in plan.selected:
        row = catalog['modules'][module]
        for directory in ('lib/lean', 'ir'):
            stem = root / row['build_root'] / directory / module_stem(module)
            plain_path(root, stem)
            result.update(path for path in stem.parent.glob(stem.name + '.*')
                          if (path.is_file() or path.is_symlink()) and
                          (path.name[len(stem.name):] in ARCHIVE_SUFFIXES or
                           path.name[len(stem.name):] == '.trace.nobuild'))
    return result


def run_seed(root: Path, catalog: dict, catalog_hash: str, plan: Plan, lean: str,
             client: GitHub) -> int:
    out, logs = root / '.lake/build/lib/lean', root / '.low-energy-verification'
    plain_path(root, logs)
    logs.mkdir(exist_ok=True)
    receipt_path = logs / 'native_foundation.json'
    final_log = logs / 'native_foundation_validation.log'
    if exists(receipt_path):
        print('Native foundation receipt already exists; the exact verifier will validate it.')
        return 0
    if exists(final_log):
        raise FoundationError('A previous native validation log is preserved without a receipt.')
    if not plan.selected:
        print('No untouched, source-closed native dependency island is available.')
        return 0
    installed, authenticated_hashes = [], {}
    attempt_log = logs / ('native_foundation_attempt_' + str(time.time_ns()) + '.log')
    success, linked_log = False, False
    gate_before_files = None
    command = VALIDATION_PREFIX + ['+' + module + ':olean' for module in plan.leaves]
    try:
        client.check_producer(catalog)
        with tempfile.TemporaryDirectory(prefix='low-energy-native-') as temporary:
            work = Path(temporary)
            for artifact_id in plan.artifacts:
                pin = catalog['artifacts'][str(artifact_id)]
                archive, stage = work / 'artifact.zip', work / 'stage'
                stage.mkdir()
                print('Restoring authenticated native shard ' + pin['name'], flush=True)
                client.download(catalog, artifact_id, archive)
                selected = {module for module in plan.selected
                            if catalog['modules'][module]['artifact_id'] == artifact_id}
                hashes = extract_bundle(archive, stage, catalog, artifact_id, selected)
                for relative, value in hashes.items():
                    source, destination = stage / relative, root / relative
                    create_copy(root, source, destination, installed)
                    if digest(destination) != value:
                        raise FoundationError('Native output changed during installation.')
                authenticated_hashes.update(hashes)
                archive.unlink()
                shutil.rmtree(stage)
            config_hashes(root, catalog)
            print('Checking native Lake traces without permitting a build.', flush=True)
            gate_before_files = scoped_files(root, catalog, plan)
            with attempt_log.open('xb') as log:
                result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                                        timeout=1800, check=False)
            if result.returncode != 0:
                raise FoundationError('Native Lake no-build validation failed (exit ' +
                                      str(result.returncode) + '); no native receipt was created.')
            configs = config_hashes(root, catalog)
            # The gate can consult a local Lake cache. Its result is accepted only
            # if the final runtime bytes are still the exact authenticated ones.
            for module in sorted(plan.selected):
                row, node = catalog['modules'][module], plan.nodes[module]
                if digest(node['source']) != row['source_sha256']:
                    raise FoundationError('A native source changed during validation.')
                native_out = root / row['build_root'] / 'lib/lean'
                expected = {suffix: entry['sha256'] for suffix, entry in row['artifacts'].items()}
                if runtime_hashes(native_out, module) != expected:
                    raise FoundationError('Lake validation changed an authenticated native runtime bundle.')
                for suffix in row['artifacts']:
                    source, destination = artifact_path(native_out, module, suffix), artifact_path(out, module, suffix)
                    if source != destination:
                        create_copy(root, source, destination, installed)
                if runtime_hashes(out, module) != expected:
                    raise FoundationError('The unified native runtime bundle does not match.')
            output_hashes = {module: runtime_hashes(out, module) for module in sorted(plan.selected)}
            modules = {}
            for module in sorted(plan.selected):
                row, node = catalog['modules'][module], plan.nodes[module]
                local = [dependency for dependency in node['deps'] if dependency in plan.nodes]
                if any(dependency not in plan.selected for dependency in local):
                    raise FoundationError('The installed native island is not dependency closed.')
                trace_path = artifact_path(Path(row['build_root']) / 'lib/lean', module, '.trace').as_posix()
                modules[module] = {'source': row['source'], 'source_sha256': row['source_sha256'],
                    'output_artifact_hashes': output_hashes[module],
                    'validated_dependency_artifact_hashes': {dependency: output_hashes[dependency]
                                                           for dependency in local},
                    'artifact_id': row['artifact_id'],
                    'original_trace_sha256': authenticated_hashes[trace_path]}
            receipt = {'schema': SCHEMA, 'status': 'validated_native_dependencies',
                'lean': lean, 'mathlib': catalog['mathlib'], 'config_sha256': configs,
                'catalog_sha256': catalog_hash,
                'origin': {key: catalog[key] for key in ('repository', 'run_id', 'head_sha',
                           'foundation_fingerprint', 'source_exporter', 'producing_workflow')},
                'artifacts': {str(key): catalog['artifacts'][str(key)] for key in plan.artifacts},
                'provenance_scope': 'Dependency SHA-256 values are current observations after successful '
                    'Lake no-build revalidation; these are not original direct-compiler receipts.',
                'validation': {'command': command, 'exit_code': 0,
                    'log_file': final_log.name, 'log_sha256': digest(attempt_log)},
                'modules': modules}
            # Remove the authentic validation-only companions before publishing
            # the receipt: downstream checkpoint transport admits only runtime files.
            keep = {artifact_path(out, module, suffix) for module in plan.selected
                    for suffix in catalog['modules'][module]['artifacts']}
            gate_created = scoped_files(root, catalog, plan) - gate_before_files
            for path in (set(installed) | gate_created) - keep:
                path.unlink(missing_ok=True)
            os.link(attempt_log, final_log)  # Exclusive, same-filesystem publication.
            linked_log = True
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=logs,
                    prefix='native_foundation_receipt_', suffix='.json', delete=False) as temp:
                pending = Path(temp.name)
                json.dump(receipt, temp, indent=2)
                temp.write('\n')
                temp.flush()
                os.fsync(temp.fileno())
            try:
                os.link(pending, receipt_path)  # Never replace prior evidence.
            finally:
                pending.unlink(missing_ok=True)
            success = True
            attempt_log.unlink()
            print(f'Validated {len(modules)} genuine native dependencies; direct proof gates remain mandatory.')
            return 0
    finally:
        if not success:
            # Only exclusive creations and known outputs newly created during
            # our Lake gate belong to us. Pre-existing or unrelated same-stem
            # files must never be swept up by rollback.
            cleanup = set(installed)
            if gate_before_files is not None:
                cleanup |= scoped_files(root, catalog, plan) - gate_before_files
            for path in cleanup:
                path.unlink(missing_ok=True)
            if linked_log:
                final_log.unlink(missing_ok=True)
            if attempt_log.is_file():
                print('Native validation attempt preserved in ' + attempt_log.name, flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['actual'])
    parser.add_argument('--plan-only', action='store_true')
    args = parser.parse_args()
    try:
        catalog, catalog_hash = load_catalog()
        config_hashes(ROOT, catalog)
        # Local import avoids a dependency cycle when the verifier reads helpers.
        import low_energy_verify as verifier
        targets = ['HeckeSkeleton.LowEnergy.' + module for module in verifier.ACTUAL]
        targets.append('HeckeSkeleton.Principal')
        new_sources = {entry['path'] for entry in json.loads(
            (ROOT / 'docs/low-energy/source_manifest.json').read_text())['files']}
        plan = make_plan(ROOT, catalog, targets, verifier.SOURCE_ROOTS, new_sources)
        summary = {'schema': SCHEMA, 'closure_modules': len(plan.nodes),
            'protected_OUT_modules': len(plan.protected), 'selected_modules': len(plan.selected),
            'maximal_roots': len(plan.leaves), 'artifact_ids': plan.artifacts,
            'download_bytes': sum(catalog['artifacts'][str(key)]['size_bytes'] for key in plan.artifacts),
            'runtime_bytes': sum(entry['size_bytes'] for module in plan.selected
                                 for entry in catalog['modules'][module]['artifacts'].values()),
            'catalog_sha256': catalog_hash}
        print(json.dumps(summary, sort_keys=True), flush=True)
        if args.plan_only:
            return 0
        plain_path(ROOT, LOG / 'native_foundation.json')
        if exists(LOG / 'native_foundation.json') or not plan.selected:
            print('Existing evidence is preserved; the direct verifier decides exact reuse.')
            return 0
        version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
        if version != catalog['lean']:
            raise FoundationError('The Lean compiler differs from the exact native foundation version.')
        return run_seed(ROOT, catalog, catalog_hash, plan, version, GitHub(catalog))
    except FoundationError as error:
        print('Native foundation cache unavailable: ' + str(error), file=sys.stderr)
    except Exception as error:
        # urllib exceptions may embed signed URLs. Never print their contents.
        print('Native foundation cache unavailable (' + type(error).__name__ +
              '); direct verification must continue.', file=sys.stderr)
    return 1


if __name__ == '__main__':
    raise SystemExit(main())
