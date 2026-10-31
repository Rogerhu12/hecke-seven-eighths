"""Isolated mock archive/rollback tests; no Lean invocation or proof evidence."""
from pathlib import Path
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
import shutil
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace
import zipfile

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('native_foundation_tested', SCRIPTS / 'low_energy_native_foundation.py')
N = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = N
spec.loader.exec_module(N)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Fixture:
    def __init__(self, root):
        self.root = root
        self.source_roots = [root]
        self.out = root / '.lake/build/lib/lean'
        self.catalog = {
            'schema': N.CATALOG_SCHEMA, 'repository': 'fixture/fixture',
            'run_id': 1, 'head_sha': 'fixture-head', 'foundation_fingerprint': 'fixture-fingerprint',
            'source_exporter': {'path': 'fixture.py'}, 'producing_workflow': {'path': 'fixture.yml'},
            'lean': 'fixture compiler, never run', 'mathlib': 'fixture-mathlib',
            'config_sha256': {}, 'artifacts': {}, 'modules': {}}
        for name in N.CONFIG_FILES:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('fixture configuration ' + name)
            self.catalog['config_sha256'][name] = N.digest(path)
        for module, imports in [('A', ['Mathlib.Fixture']), ('B', ['A']), ('Target', ['B'])]:
            source = root / (module + '.lean')
            source.write_text('module\n\n' + ''.join('public import ' + dep + '\n' for dep in imports))
            if module == 'Target':
                continue
            self.catalog['modules'][module] = {
                'source': module + '.lean', 'source_sha256': N.digest(source),
                'build_root': '.lake/build', 'artifact_id': 7,
                'artifacts': {suffix: {'sha256': sha((module + suffix).encode()),
                    'size_bytes': len((module + suffix).encode())} for suffix in N.RUNTIME_SUFFIXES}}
        self.archive = root / 'fixture.zip'
        self.write_archive()

    def write_archive(self, unsafe=None, tamper_runtime=False, duplicate=False):
        payloads = []
        for module in self.catalog['modules']:
            build_root = self.catalog['modules'][module]['build_root']
            for suffix in (*N.RUNTIME_SUFFIXES, '.trace', '.ilean', '.olean.hash'):
                raw = (module + suffix).encode()
                if tamper_runtime and module == 'A' and suffix == '.olean':
                    raw += b'tamper'
                payloads.append((f'{build_root}/lib/lean/{module}{suffix}', raw, False))
            for suffix in ('.c', '.c.hash', '.setup.json'):
                payloads.append((f'{build_root}/ir/{module}{suffix}', (module + suffix).encode(), False))
        if unsafe:
            payloads.append(unsafe)
        if duplicate:
            payloads.append(payloads[0])
        compressed = io.BytesIO()
        with tarfile.open(fileobj=compressed, mode='w:gz') as tar:
            for name, raw, symlink in payloads:
                info = tarfile.TarInfo(name)
                if symlink:
                    info.type = tarfile.SYMTYPE
                    info.linkname = '/tmp/forbidden'
                    info.size = 0
                    tar.addfile(info)
                else:
                    info.size = len(raw)
                    tar.addfile(info, io.BytesIO(raw))
        bundle = compressed.getvalue()
        manifest = {'format': 1, 'fingerprint': 'fixture-fingerprint', 'lower': 0,
            'upper': 40, 'shard': 0, 'shards': 4, 'owned_modules': 2,
            'file_count': len(payloads), 'archive_sha256': sha(bundle)}
        with zipfile.ZipFile(self.archive, 'w') as zipped:
            zipped.writestr('foundation-40-0.manifest.json', json.dumps(manifest))
            zipped.writestr('foundation-40-0.tar.gz', bundle)
        self.catalog['artifacts']['7'] = {'name': 'fixture-shard', 'manifest': manifest,
            'outer_sha256': N.digest(self.archive), 'size_bytes': self.archive.stat().st_size,
            'expanded_bytes': sum(len(raw) for _, raw, link in payloads if not link)}

    def plan(self, new_sources=None):
        return N.make_plan(self.root, self.catalog, ['Target'], self.source_roots, new_sources or set())

    def client(self):
        archive = self.archive
        return SimpleNamespace(check_producer=lambda _: None,
            download=lambda catalog, artifact, destination: shutil.copyfile(archive, destination))

    def seed(self, gate_code=0, gate_action=None, client=None):
        def gate(command, **kwargs):
            assert command == N.VALIDATION_PREFIX + ['+B:olean']
            assert '--old' not in command
            kwargs['stdout'].write(b'fixture no-build validation; no compiler ran\n')
            if gate_action:
                gate_action()
            return SimpleNamespace(returncode=gate_code)
        with patch.object(N.subprocess, 'run', side_effect=gate):
            return N.run_seed(self.root, self.catalog, 'fixture-catalog-hash', self.plan(),
                              'fixture compiler, never run', client or self.client())


class NativeFoundationTests(unittest.TestCase):
    def setUp(self):
        # Fixture status messages must not look like real Lake evidence in CI.
        self.enterContext(redirect_stdout(io.StringIO()))
        self.temp = tempfile.TemporaryDirectory(prefix='native-importer-test-')
        self.root = Path(self.temp.name)
        self.f = Fixture(self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_closed_island_and_external_import(self):
        plan = self.f.plan()
        self.assertEqual(plan.selected, {'A', 'B'})
        self.assertEqual(plan.leaves, ['B'])

    def test_protected_dependency_excludes_descendants(self):
        self.f.out.mkdir(parents=True)
        (self.f.out / 'A.olean').write_bytes(b'protected')
        self.assertEqual(self.f.plan().selected, set())

    def test_existing_native_companion_is_preserved(self):
        self.f.out.mkdir(parents=True)
        (self.f.out / 'A.olean.private').write_bytes(b'preexisting partial output')
        self.assertEqual(self.f.plan().selected, set())

    def test_new_source_not_admitted(self):
        self.assertEqual(self.f.plan({'B.lean'}).selected, {'A'})

    def test_changed_source_not_admitted(self):
        (self.root / 'A.lean').write_text('module\n-- source changed\n')
        self.assertEqual(self.f.plan().selected, set())

    def test_source_root_binding(self):
        self.f.catalog['modules']['A']['source'] = 'somewhere/A.lean'
        self.assertEqual(self.f.plan().selected, set())

    def test_extract_authenticates_runtime_and_omits_setup(self):
        stage = self.root / 'stage'
        stage.mkdir()
        hashes = N.extract_bundle(self.f.archive, stage, self.f.catalog, 7, {'A', 'B'})
        self.assertIn('.lake/build/lib/lean/A.trace', hashes)
        self.assertFalse((stage / '.lake/build/ir/A.setup.json').exists())
        self.assertEqual(N.digest(stage / '.lake/build/lib/lean/B.olean'), sha(b'B.olean'))

    def test_authenticated_tar_still_rejects_unsafe_members(self):
        cases = [('../escape', b'bad', False),
                 ('.lake/build/lib/lean/A.lean', b'bad', False),
                 ('.lake/build/lib/lean/Link.olean', b'', True),
                 ('/tmp/escape', b'bad', False)]
        for index, case in enumerate(cases):
            with self.subTest(case=case[0]):
                self.f.write_archive(unsafe=case)
                stage = self.root / ('stage-' + str(index))
                stage.mkdir()
                with self.assertRaises(N.FoundationError):
                    N.extract_bundle(self.f.archive, stage, self.f.catalog, 7, {'A', 'B'})

    def test_duplicate_tar_member_rejected(self):
        self.f.write_archive(duplicate=True)
        stage = self.root / 'stage'
        stage.mkdir()
        with self.assertRaises(N.FoundationError):
            N.extract_bundle(self.f.archive, stage, self.f.catalog, 7, {'A', 'B'})

    def test_runtime_hash_rejected_even_in_authenticated_archive(self):
        self.f.write_archive(tamper_runtime=True)
        stage = self.root / 'stage'
        stage.mkdir()
        with self.assertRaises(N.FoundationError):
            N.extract_bundle(self.f.archive, stage, self.f.catalog, 7, {'A', 'B'})

    def test_success_receipt_and_runtime_only_checkpoint(self):
        self.assertEqual(self.f.seed(), 0)
        log = self.root / '.low-energy-verification'
        receipt = json.loads((log / 'native_foundation.json').read_text())
        self.assertEqual(receipt['schema'], N.SCHEMA)
        self.assertEqual(receipt['status'], 'validated_native_dependencies')
        self.assertNotIn('cache_schema', receipt)
        self.assertNotIn('exit_code', receipt['modules']['A'])
        self.assertEqual(receipt['modules']['B']['validated_dependency_artifact_hashes'],
                         {'A': receipt['modules']['A']['output_artifact_hashes']})
        self.assertEqual(receipt['validation']['log_sha256'],
                         N.digest(log / 'native_foundation_validation.log'))
        actual = {p.name for p in self.f.out.rglob('*') if p.is_file()}
        self.assertEqual(actual, {module + suffix for module in ('A', 'B') for suffix in N.RUNTIME_SUFFIXES})
        self.assertFalse(list((self.root / '.lake/build/ir').rglob('*.*')))

    def test_gate_failure_cleans_only_owned_files(self):
        self.f.out.mkdir(parents=True)
        protected = self.f.out / 'Protected.olean'
        protected.write_bytes(b'keep')
        def generate_nobuild_trace():
            (self.f.out / 'A.trace.nobuild').write_bytes(b'no build occurred')
        with self.assertRaises(N.FoundationError):
            self.f.seed(gate_code=3, gate_action=generate_nobuild_trace)
        self.assertEqual(protected.read_bytes(), b'keep')
        self.assertEqual({p.name for p in self.f.out.iterdir()}, {'Protected.olean'})
        self.assertFalse((self.root / '.low-energy-verification/native_foundation.json').exists())
        self.assertTrue(list((self.root / '.low-energy-verification').glob('native_foundation_attempt_*.log')))

    def test_postgate_runtime_changes_rejected(self):
        with self.assertRaises(N.FoundationError):
            self.f.seed(gate_action=lambda: (self.f.out / 'A.olean').write_bytes(b'changed by fixture'))
        self.assertFalse((self.f.out / 'A.olean').exists())
        self.assertFalse((self.root / '.low-energy-verification/native_foundation.json').exists())

    def test_postgate_source_changes_rejected(self):
        with self.assertRaises(N.FoundationError):
            self.f.seed(gate_action=lambda: (self.root / 'A.lean').write_text('changed during gate'))
        self.assertFalse((self.f.out / 'A.olean').exists())

    def test_failure_before_gate_preserves_concurrent_output(self):
        plan = self.f.plan()
        self.f.out.mkdir(parents=True)
        path = self.f.out / 'A.olean'
        def fail_download(*args):
            path.write_bytes(b'not created by importer')
            raise N.FoundationError('fixture network failure')
        client = SimpleNamespace(check_producer=lambda _: None, download=fail_download)
        with self.assertRaises(N.FoundationError):
            N.run_seed(self.root, self.f.catalog, 'fixture', plan, 'fixture', client)
        self.assertEqual(path.read_bytes(), b'not created by importer')

    def test_before_gate_inventory_preserves_unrelated_existing_files(self):
        self.f.out.mkdir(parents=True)
        unrelated = self.f.out / 'A.unrelated'
        concurrent = self.f.out / 'A.trace.nobuild'
        def download(*args):
            unrelated.write_bytes(b'unrelated file')
            concurrent.write_bytes(b'pre-existing before our gate')
            shutil.copyfile(self.f.archive, args[-1])
        client = SimpleNamespace(check_producer=lambda _: None, download=download)
        with self.assertRaises(N.FoundationError):
            self.f.seed(gate_code=3, client=client)
        self.assertEqual(unrelated.read_bytes(), b'unrelated file')
        self.assertEqual(concurrent.read_bytes(), b'pre-existing before our gate')
        self.assertFalse((self.f.out / 'A.olean').exists())

    def test_vendor_outputs_promoted_without_validation_companions(self):
        source_root = self.root / 'vendor/class-field-theory/Lean4'
        source_root.mkdir(parents=True)
        (self.root / 'A.lean').rename(source_root / 'A.lean')
        self.f.source_roots.append(source_root)
        self.f.catalog['modules']['A']['source'] = 'vendor/class-field-theory/Lean4/A.lean'
        self.f.catalog['modules']['A']['build_root'] = 'vendor/class-field-theory/.lake/build'
        self.f.write_archive()
        self.assertEqual(self.f.seed(), 0)
        self.assertEqual((self.f.out / 'A.olean').read_bytes(), b'A.olean')
        native_root = self.root / 'vendor/class-field-theory/.lake/build'
        self.assertFalse([path for path in native_root.rglob('*') if path.is_file()])
        receipt = json.loads((self.root / '.low-energy-verification/native_foundation.json').read_text())
        self.assertEqual(receipt['modules']['A']['source'], 'vendor/class-field-theory/Lean4/A.lean')

    def test_existing_receipt_and_log_never_replaced(self):
        log = self.root / '.low-energy-verification'
        log.mkdir()
        receipt, validation = log / 'native_foundation.json', log / 'native_foundation_validation.log'
        receipt.write_bytes(b'previous receipt')
        validation.write_bytes(b'previous validation')
        client = SimpleNamespace(check_producer=lambda _: self.fail('producer should not be queried'))
        self.assertEqual(N.run_seed(self.root, self.f.catalog, 'fixture', self.f.plan(), 'fixture', client), 0)
        self.assertEqual(receipt.read_bytes(), b'previous receipt')
        self.assertEqual(validation.read_bytes(), b'previous validation')

    def test_symlink_destination_rejected(self):
        elsewhere = self.root / 'elsewhere'
        elsewhere.mkdir()
        (self.root / '.lake').symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaises(N.FoundationError):
            self.f.plan()


if __name__ == '__main__':
    unittest.main(verbosity=2)
