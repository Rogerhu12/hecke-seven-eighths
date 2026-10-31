"""Software regression fixtures only: no Lean, network, or proof evidence."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / 'scripts'))
import low_energy_lake_verify as lane


class Gates(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='lake-lane-regression-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for config in lane.CONFIG_PATHS:
            path = self.root / config
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('fixture\n')
        self.source_path = 'HeckeSkeleton/LowEnergy/ActualCompletedMarkedEnergy.lean'
        self.raw = b'/- sorry in a comment is not an admission -/\ntheorem sample : True := True.intro\n'
        path = self.root / self.source_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(self.raw)
        (self.root / 'HeckeSkeleton/Principal.lean').write_text('import HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy\n')
        self.entry = {'path': self.source_path,
                      'module': 'HeckeSkeleton.LowEnergy.ActualCompletedMarkedEnergy',
                      'source_sha256': lane.sha256(self.raw),
                      'verification_history': [{'recorded_source_sha256': 'wrong-old-hash'}]}
        self.write_manifest([self.entry])

    def write_manifest(self, entries):
        path = self.root / lane.SOURCE_MANIFEST
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({'files': entries}))

    def test_authoritative_current_hash_accepts_despite_different_history(self):
        self.assertEqual(lane.source_snapshot(self.root)['source_count'], 1)

    def test_matching_history_cannot_rescue_stale_current_hash(self):
        entry = copy.deepcopy(self.entry)
        entry['verification_history'][0]['recorded_source_sha256'] = entry['source_sha256']
        entry['source_sha256'] = '0' * 64
        self.write_manifest([entry])
        with self.assertRaisesRegex(RuntimeError, 'Current source_sha256'):
            lane.source_snapshot(self.root)

    def test_each_forbidden_token_rejected_even_with_matching_hash(self):
        for token in ('sorry', 'axiom', 'admit', 'native_decide'):
            with self.subTest(token=token):
                raw = ('theorem sample : True := by ' + token + '\n').encode()
                (self.root / self.source_path).write_bytes(raw)
                self.write_manifest([{**self.entry, 'source_sha256': lane.sha256(raw)}])
                with self.assertRaisesRegex(RuntimeError, 'Forbidden new-source token'):
                    lane.source_snapshot(self.root)

    def test_outside_namespace_and_traversal_rejected(self):
        for path in ('HeckeGeneral/Proof.lean', '../HeckeSkeleton/Proof.lean',
                     'HeckeSkeleton/../Proof.lean'):
            with self.subTest(path=path):
                self.write_manifest([{**self.entry, 'path': path}])
                with self.assertRaisesRegex(RuntimeError, 'under HeckeSkeleton'):
                    lane.source_snapshot(self.root)

    def test_duplicate_manifest_entries_rejected(self):
        self.write_manifest([self.entry, self.entry])
        with self.assertRaisesRegex(RuntimeError, 'Duplicate'):
            lane.source_snapshot(self.root)

    def test_manifest_count_can_increase_with_reviewed_sources(self):
        path = self.root / 'HeckeSkeleton/LowEnergy/NewHelper.lean'
        raw = b'theorem helper : True := True.intro\n'
        path.write_bytes(raw)
        self.write_manifest([self.entry, {'path': 'HeckeSkeleton/LowEnergy/NewHelper.lean',
                                          'module': 'HeckeSkeleton.LowEnergy.NewHelper',
                                          'source_sha256': lane.sha256(raw)}])
        self.assertEqual(lane.source_snapshot(self.root)['source_count'], 2)

    def test_runtime_trace_hash_and_ir_outputs_rejected_in_other_build_roots(self):
        for rel in ('.lake/build/lib/lean/HeckeSkeleton/Old.olean.private',
                    'vendor/class-field-theory/.lake/build/lib/lean/HeckeSkeleton/Old.trace',
                    '.lake/packages/Extra/.lake/build/ir/HeckeSkeleton/Old.c.hash',
                    '.lake/packages/TauCeti/.lake/build/lib/lean/HeckeSkeleton.olean'):
            with self.subTest(path=rel):
                path = self.root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'preexisting output')
                with self.assertRaisesRegex(RuntimeError, 'Pre-existing HeckeSkeleton'):
                    lane.assert_no_proof_outputs(self.root)
                path.unlink()
        self.assertTrue(lane.assert_no_proof_outputs(self.root))

    def test_pinned_real_metadata_accepts_and_mutation_rejects(self):
        # Exact public release metadata, including its original CRLF encoding.
        manifest = {
            'tag': 'lake-cache-76c696e',
            'commit': '76c696e20ee1f201a6507dde8b1d832a928ac71a',
            'lean_toolchain': 'leanprover/lean4:v4.35.0-rc3',
            'excluded_module_prefixes': ['HeckeSkeleton', 'ThetaGlobal',
                                         'DedekindZetaChallenge', 'DedekindZetaSolution'],
            'skipped_stale_modules': ['HeckeGeneral',
                                      'HeckeGeneral.Analysis.ArchimedeanGammaVertical',
                                      'Zeta23.GammaFacts.StirlingVert'],
            'build_roots': {
                '.lake/build': {'files': 65693, 'bytes': 3769116410, 'modules': 4979},
                'vendor/class-field-theory/.lake/build':
                    {'files': 24870, 'bytes': 725278564, 'modules': 1658},
                '.lake/packages/TauCeti/.lake/build':
                    {'files': 2730, 'bytes': 63208422, 'modules': 182}},
            'uncompressed_bytes': 4557603396,
            'parts': [{'name': 'lake-cache.tar.zst.part-000', 'bytes': 1146434516,
                       'sha256': '2fcc28ecb8224ecd69e656692d79e976ce932bd5a5dd9135ed3ae5721aee636e'}],
            'created': '2026-10-31T08:13:57Z'}
        raw = (json.dumps(manifest, indent=2) + '\n').replace('\n', '\r\n').encode()
        (self.root / 'lake-cache-manifest.json').write_bytes(raw)
        (self.root / 'SHA256SUMS').write_text(
            '2fcc28ecb8224ecd69e656692d79e976ce932bd5a5dd9135ed3ae5721aee636e'
            '  lake-cache.tar.zst.part-000\n')
        self.assertEqual(lane.cache_metadata(self.root)['release_tag'], lane.CACHE_TAG)
        path = self.root / 'lake-cache-manifest.json'
        path.write_bytes(path.read_bytes() + b' ')
        with self.assertRaisesRegex(RuntimeError, 'pinned release assets'):
            lane.cache_metadata(self.root)

    @staticmethod
    def reports(axioms='propext, Classical.choice, Quot.sound'):
        return ''.join("'" + name + "' depends on axioms: [" + axioms + "]\n"
                       for name in lane.REQUIRED_AXIOMS)

    def test_all_exact_names_and_allowed_three_accept(self):
        result = lane.inspect_final_audit(self.reports())
        self.assertTrue(result['ok'])
        self.assertEqual(result['printed_declaration_count'], len(lane.REQUIRED_AXIOMS))

    def test_missing_or_qualified_wrong_second_name_rejected(self):
        for output in (self.reports().splitlines()[0] + '\n',
                       self.reports().replace(lane.REQUIRED_AXIOMS[1],
                                              'ActualCompletedMarkedEnergy.completedMarkedEnergy')):
            with self.subTest(output=output):
                self.assertFalse(lane.inspect_final_audit(output)['ok'])

    def test_admitted_unknown_duplicate_and_malformed_reports_rejected(self):
        outputs = [self.reports('sorryAx'), self.reports('Private.unproved'),
                   self.reports() * 2, self.reports().replace(']', '')]
        for output in outputs:
            with self.subTest(output=output):
                self.assertFalse(lane.inspect_final_audit(output)['ok'])

    def test_missing_preparation_clears_stale_aggregate_and_audit_not_manual_cache(self):
        evidence = self.root / '.low-energy-lake-verification'
        evidence.mkdir()
        for name in ('report.json', 'final-audit.log', 'final-audit.json',
                     'final-audit.lean', 'outputs.json', 'lake-build.log'):
            (evidence / name).write_text('old success')
        manual = self.root / '.low-energy-verification/native_foundation.json'
        manual.parent.mkdir()
        manual.write_text('reusable manual evidence')
        with patch.object(lane, 'ROOT', self.root), patch.object(lane, 'EVIDENCE', evidence):
            with self.assertRaises(RuntimeError):
                lane.verify('a' * 40, self.root, 1)
        report = json.loads((evidence / 'report.json').read_text())
        self.assertEqual(report['status'], 'failed')
        self.assertEqual(report['final_axiom_gate'], 'not_started')
        self.assertNotIn('lake_build', report)
        self.assertFalse((evidence / 'final-audit.json').exists())
        self.assertFalse((evidence / 'lake-build.log').exists())
        self.assertEqual(manual.read_text(), 'reusable manual evidence')


if __name__ == '__main__':
    unittest.main(verbosity=2)

