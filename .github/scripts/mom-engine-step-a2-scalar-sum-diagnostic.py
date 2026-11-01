#!/usr/bin/env python3
"""Reversible full-source scalar-sigma diagnostic after the frozen 61-marker control.

The original cc98 tracked source is never edited. The pinned 91a3 control
preparer supplies its complete source, two existing scoped warnings, phase
W3 omit, and all 61 markers. This variant adds one abstract scalar theorem,
removes the now-unreferenced private coveredLeaf sum theorem, and replaces
only the public finite-sum proof. It removes five obsolete markers and adds
four matching boundaries, preserving every integral/terminal boundary.
The two warning scopes are unchanged. This diagnostic has no acceptance or
production authority, even if its complete temporary module compiles.
Owner comment 6563548652 separately approves those two exact warning scopes;
the false production_approval flag below describes this diagnostic's authority.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
SOURCE_BYTES = 40282
CONTROL_SCRIPT = Path('.github/scripts/mom-engine-step-a2-provider-public-warning-control.py')
CONTROL_SCRIPT_SHA = '91a373aaadf02897e9fafb803bffc4b11290c6a3bdc3a042ea38e9a331cb281f'
CONTROL_CANDIDATE_SHA = 'c4a26eec9fb3b5a4d66ecb0220d4c82e29fc784adbdda4917c27430560bb228c'
CONTROL_MARKED_SHA = '7285c7e5c9d6da0c314f35300ebd617f53f78efd98e4b1d3e9762a37a4da044b'
PRIOR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-public-phase-after.py')
PRIOR_SCRIPT_SHA = 'bc1a8cbab78e8c713e8bada7c97be38336d1c02bff92c82025a0d832b2cb31f8'
MARKER_SCRIPT = Path('.github/scripts/mom-engine-step-a2-diagnostic.py')
MARKER_SCRIPT_SHA = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
BASELINE_MARKED_SHA = '9183fe0d033a45664d888b06640f9785bb414752d323096dcea2c7842b6bcd57'
CANDIDATE_SHA = '505ee96c29c7171932828d3dc3000eb6253ded15e726422fd89067df2445dc5f'
CANDIDATE_BLOB = '75e905cff10acf0b34d1cb4e322b44ad0962cb16'
EXPECTED_MARKED_SHA = '34f437b0532881d27cfd0eb07fa2f6450ce70e3cb524193876e6b16f006bef73'
EXPECTED_MARKED_BLOB = '33b48bf2d03ce133915dcdc70dfac1bf6e45ac06'
OWNER_WARNING_SCOPE_APPROVAL_COMMENT = 6563548652
HELPER_TARGET = 'scalar_sum_sigma_of_class_sum'
PUBLIC_TARGET = 'coverHybridPhaseNonzeroCost_eq_leaf_sum'
REMOVED_PRIVATE_TARGET = 'coveredLeaf_sum_eq_class_sum'
REMOVED_LABELS = [
    'BEFORE_HEADER_coveredLeaf_sum_eq_class_sum',
    'COMMAND_CONTINUED_AFTER_coveredLeaf_sum_eq_class_sum',
    'SUM_PUBLIC_BEFORE_hclasses',
    'SUM_PUBLIC_BEFORE_hleaves',
    'SUM_PUBLIC_BEFORE_FINAL_EXACT',
]
NEW_LABELS = [
    'BEFORE_HEADER_scalar_sum_sigma_of_class_sum',
    'COMMAND_CONTINUED_AFTER_scalar_sum_sigma_of_class_sum',
    'PUBLIC_SUM_BEFORE_EXACT',
    'PUBLIC_SUM_AFTER_EXACT',
]
CONTROL_FALSE_FLAGS = {
    'acceptance_evidence': False,
    'original_module_native_was_run': False,
    'original_module_acceptance': False,
    'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False,
    'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False,
    'candidate_native_validation_performed': False,
    'candidate_equivalence_claimed': False,
}
FALSE_FLAGS = {**CONTROL_FALSE_FLAGS, 'fresh_axiom_audit_performed': False}
# Exact author-reviewed edits are embedded; no mutable extra source file is read.
EDITS = {'insert_before': 'variable {K : Type} [Field K] [NumberField K]\n', 'scalar_helper': 'private theorem scalar_sum_sigma_of_class_sum\n    {α : Type*} [Fintype α] {β : α → Type*} [∀ a, Fintype (β a)]\n    (total : ℝ) (classes : α → ℝ) (leaves : (Σ a : α, β a) → ℝ)\n    (hclasses : total = ∑ a : α, classes a)\n    (hleaves : ∀ a : α, classes a = ∑ b : β a, leaves ⟨a, b⟩) :\n    total = ∑ key : (Σ a : α, β a), leaves key := by\n  exact hclasses.trans\n    ((Finset.sum_congr rfl (fun a _ => hleaves a)).trans\n      (Fintype.sum_sigma leaves).symm)\n\n', 'old_public_sum_proof': '  have hclasses :\n      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =\n        ∑ v : s.CoveredClassKey LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v :=\n    coverHybridPhaseNonzeroCost_eq_class_sum s LC RC exceptional x ξ\n  have hleaves :\n      (∑ v : s.CoveredClassKey LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v) =\n        ∑ v : s.CoveredClassKey LC RC,\n          ∑ j : v.AllocationKey, (v.leaf exceptional F x j).firstPhaseCost ξ := by\n    apply Finset.sum_congr rfl\n    intro v _\n    exact v.phase_class_eq_leaf_sum exceptional F x ξ\n  exact hclasses.trans (hleaves.trans\n    (coveredLeaf_sum_eq_class_sum s LC RC\n      (fun b => (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ)).symm)\n', 'new_public_sum_proof': '  exact scalar_sum_sigma_of_class_sum\n    (α := s.CoveredClassKey LC RC) (β := fun v => v.AllocationKey)\n    (s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ)\n    (coveredClassPhaseCost s LC RC exceptional x ξ)\n    (fun b => (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ)\n    (coverHybridPhaseNonzeroCost_eq_class_sum s LC RC exceptional x ξ)\n    (fun v => v.phase_class_eq_leaf_sum exceptional F x ξ)\n', 'removed_private_declaration': 'private theorem coveredLeaf_sum_eq_class_sum (f : s.CoveredLeafKey LC RC → ℝ) :\n    (∑ b : s.CoveredLeafKey LC RC, f b) =\n      ∑ v : s.CoveredClassKey LC RC, ∑ j : v.AllocationKey, f ⟨v, j⟩ := by\n  exact Fintype.sum_sigma f\n\n', 'restore_private_before': '/-- Exact finite flattening of the covered source, at the first\ncontinuous Fourier parameter. -/\n', 'retained_phase_omit': 'omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in\n', 'retained_two_scoped_warning_option': 'set_option linter.unusedSectionVars false in\n'}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_control_script(path: Path):
    assert sha(path.read_bytes()) == CONTROL_SCRIPT_SHA, 'Frozen 61-marker control changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_91a3_warning_control', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA
    assert module.SOURCE_BYTES == SOURCE_BYTES and module.CANDIDATE_SHA == CONTROL_CANDIDATE_SHA
    assert module.EXPECTED_MARKED_SHA == CONTROL_MARKED_SHA
    assert module.PRIOR_SCRIPT == PRIOR_SCRIPT and module.PRIOR_SCRIPT_SHA == PRIOR_SCRIPT_SHA
    assert module.MARKER_SCRIPT == MARKER_SCRIPT and module.MARKER_SCRIPT_SHA == MARKER_SCRIPT_SHA
    assert module.FALSE_FLAGS == CONTROL_FALSE_FLAGS
    return module


def prepare(original: bytes, marker_module, prior_module, control_module):
    """Pure preparation returns baseline59, candidate505ee, marked60, manifest, checks.

    No files, processes, module constants, compiler settings or guards change.
    Both inverse routes recover the pinned full 61-marker control and cc98.
    """
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA and marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    baseline, old_candidate, old_marked, old_manifest, old_checks = \
        control_module.prepare(original, marker_module, prior_module)
    assert len(baseline) == 45595 and sha(baseline) == BASELINE_MARKED_SHA
    assert len(old_candidate) == 40441 and sha(old_candidate) == CONTROL_CANDIDATE_SHA
    assert len(old_marked) == 45900 and sha(old_marked) == CONTROL_MARKED_SHA
    assert len(old_manifest) == 61 and old_checks['marker_count'] == 61
    edits = {key: value.encode() for key, value in EDITS.items()}
    assert len(edits['scalar_helper']) == 497
    assert sha(edits['scalar_helper']) == '20e181336310b268af0f98517a0e16f8f4182a710a8098c9df3d4d8ade99795c'
    assert len(edits['removed_private_declaration']) == 240
    assert sha(edits['removed_private_declaration']) == '41260f1e242fedbee62c9e6c18fd4ae7a8353baaaf8fd5b5e1ed4992755f933f'
    assert edits['retained_phase_omit'] == control_module.OMIT
    assert edits['retained_two_scoped_warning_option'] == control_module.OPTION

    removed_entries = [entry for entry in old_manifest if entry['label'] in REMOVED_LABELS]
    retained_entries = [entry for entry in old_manifest if entry['label'] not in REMOVED_LABELS]
    assert len(removed_entries) == 5 and len(retained_entries) == 56
    assert [entry['label'] for entry in removed_entries] == REMOVED_LABELS
    removed_lines = {entry['inserted_line'].encode() for entry in removed_entries}
    assert len(removed_lines) == 5

    def remove_lines(data: bytes, lines: set[bytes]) -> bytes:
        return b''.join(line for line in data.splitlines(keepends=True) if line not in lines)

    old_marked_without_obsolete = remove_lines(old_marked, removed_lines)

    def apply_edits(data: bytes) -> bytes:
        for key in ['insert_before', 'old_public_sum_proof', 'removed_private_declaration']:
            assert data.count(edits[key]) == 1, key
        assert edits['scalar_helper'] not in data
        data = data.replace(edits['insert_before'], edits['scalar_helper'] + edits['insert_before'], 1)
        data = data.replace(edits['removed_private_declaration'], b'', 1)
        return data.replace(edits['old_public_sum_proof'], edits['new_public_sum_proof'], 1)

    candidate = apply_edits(old_candidate)
    edited_marked = apply_edits(old_marked_without_obsolete)
    assert len(candidate) == 40382 and sha(candidate) == CANDIDATE_SHA
    assert git_blob(candidate) == CANDIDATE_BLOB
    assert REMOVED_PRIVATE_TARGET.encode() not in candidate
    assert b'as_aux_lemma' not in candidate

    def marker_line(label: str, kind: str) -> bytes:
        command = 'run_cmd' if kind == 'command' else '  run_tac'
        return (command + ' IO.eprintln ' + json.dumps(marker_module.PREFIX + ' ' + label) + '\n').encode()

    kinds = ['command', 'command', 'tactic', 'tactic']
    new_lines = [marker_line(label, kind) for label, kind in zip(NEW_LABELS, kinds)]
    assert all(line not in edited_marked for line in new_lines)
    helper = edits['scalar_helper']
    assert helper.endswith(b'\n\n')
    marked = edited_marked.replace(helper, new_lines[0] + helper[:-1] + new_lines[1] + b'\n', 1)
    proof = edits['new_public_sum_proof']
    marked = marked.replace(proof, new_lines[2] + proof + new_lines[3], 1)
    assert len(marked) == 45757 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    assert REMOVED_PRIVATE_TARGET.encode() not in marked
    assert b'as_aux_lemma' not in marked

    public_header_marker = next(entry['inserted_line'].encode() for entry in old_manifest
                                if entry['label'] == 'BEFORE_HEADER_' + PUBLIC_TARGET)

    def undo_edits(data: bytes, with_markers: bool = False) -> bytes:
        assert data.count(edits['scalar_helper']) == 1
        assert data.count(edits['new_public_sum_proof']) == 1
        data = data.replace(edits['new_public_sum_proof'], edits['old_public_sum_proof'], 1)
        data = data.replace(edits['scalar_helper'], b'', 1)
        # In the marked inverse the deleted private declaration belongs BEFORE
        # the surviving public BEFORE_HEADER command, not between it and its doc.
        anchor = (public_header_marker if with_markers else b'') + edits['restore_private_before']
        assert data.count(anchor) == 1
        return data.replace(anchor, edits['removed_private_declaration'] + anchor, 1)

    def restore_obsolete_markers(data: bytes) -> bytes:
        actual = iter(data.splitlines(keepends=True))
        recovered = []
        for expected in old_marked.splitlines(keepends=True):
            if expected in removed_lines:
                recovered.append(expected)
            else:
                line = next(actual, None)
                assert line == expected, 'Inverse changed a retained original line'
                recovered.append(line)
        assert next(actual, None) is None
        return b''.join(recovered)

    inverse_marked = undo_edits(remove_lines(marked, set(new_lines)), with_markers=True)
    assert inverse_marked == old_marked_without_obsolete
    assert restore_obsolete_markers(inverse_marked) == old_marked
    assert undo_edits(candidate) == old_candidate

    all_marker_lines = {entry['inserted_line'].encode() for entry in retained_entries} | set(new_lines)
    assert len(all_marker_lines) == 60
    assert all(marked.count(line) == 1 for line in all_marker_lines)
    assert remove_lines(marked, all_marker_lines) == candidate
    assert undo_edits(remove_lines(marked, all_marker_lines)) == old_candidate

    def remove_controls(data: bytes) -> bytes:
        for prefix, anchor in [
                (control_module.OMIT, control_module.PHASE_HEADER),
                (control_module.OPTION, control_module.PROVIDER_HEADER),
                (control_module.OPTION, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
            assert data.count(prefix + anchor) == 1
            data = data.replace(prefix + anchor, anchor, 1)
        assert control_module.OPTION not in data and control_module.OMIT not in data
        return data

    assert remove_controls(undo_edits(candidate)) == original
    assert remove_controls(undo_edits(remove_lines(marked, all_marker_lines))) == original
    old_marker_lines = {entry['inserted_line'].encode() for entry in old_manifest}
    assert remove_controls(remove_lines(restore_obsolete_markers(inverse_marked), old_marker_lines)) == original
    # The two precise controls and their command/doc associations survive.
    for target, prefix, anchor in [
            (control_module.PHASE_TARGET, control_module.OMIT, control_module.PHASE_HEADER),
            (control_module.PROVIDER_TARGET, control_module.OPTION, control_module.PROVIDER_HEADER),
            (control_module.PUBLIC_TARGET, control_module.OPTION,
             control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
        before = marker_line('BEFORE_HEADER_' + target, 'command')
        assert before + prefix + anchor in marked
    assert marked.count(control_module.OPTION) == candidate.count(control_module.OPTION) == 2
    assert marked.count(control_module.OMIT) == candidate.count(control_module.OMIT) == 1
    assert public_header_marker + edits['restore_private_before'] in marked
    suffix = b'private theorem leaf_firstPhaseCost_integrable_of_firstKernel\n'
    assert candidate[candidate.index(suffix):] == old_candidate[old_candidate.index(suffix):]
    assert marked[marked.index(suffix):] == old_marked[old_marked.index(suffix):]
    nested_start = b'private def coveredClassNestedSum '
    nested_end = edits['removed_private_declaration']
    original_nested = old_candidate[old_candidate.index(nested_start):old_candidate.index(nested_end)]
    assert original_nested in candidate
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in marked.splitlines() if line.startswith(prefix)] == \
            [line for line in original.splitlines() if line.startswith(prefix)]

    manifest = []
    for entry in retained_entries:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['control_61_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        updated['is_new_scalar_sum_marker'] = False
        manifest.append(updated)
    helper_anchor = original[:original.index(edits['insert_before'])].count(b'\n') + 1
    proof_anchor = original[:original.index(edits['old_public_sum_proof'])].count(b'\n') + 1
    proof_after = proof_anchor + edits['old_public_sum_proof'].count(b'\n')
    anchors = [helper_anchor, helper_anchor, proof_anchor, proof_after]
    for label, kind, line, anchor in zip(NEW_LABELS, kinds, new_lines, anchors):
        manifest.append({
            'label': label, 'kind': kind, 'inserted_line': line.decode(),
            'original_insert_before_line': anchor,
            'original_line_is_edit_anchor': True,
            'instrumented_line': marked[:marked.index(line)].count(b'\n') + 1,
            'control_61_instrumented_line': None,
            'origin': 'scalar_sum_replacement', 'is_new_scalar_sum_marker': True,
        })
    manifest.sort(key=lambda entry: entry['instrumented_line'])
    assert len(manifest) == 60
    assert [entry['label'] for entry in manifest if not entry['is_new_scalar_sum_marker']] == \
        [entry['label'] for entry in retained_entries]
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] ==
               entry['inserted_line'].encode() for entry in manifest)
    warning_scopes = []
    for scope, anchor in zip(old_checks['warning_scopes'], [
            control_module.PROVIDER_HEADER, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER]):
        updated = dict(scope)
        updated['control_61_instrumented_line'] = scope['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(control_module.OPTION + anchor)].count(b'\n') + 1
        warning_scopes.append(updated)
    omit_scope = dict(old_checks['omit_scope'])
    omit_scope['control_61_instrumented_line'] = omit_scope['instrumented_line']
    omit_scope['instrumented_line'] = marked[:marked.index(control_module.OMIT + control_module.PHASE_HEADER)].count(b'\n') + 1
    checks = {
        'marker_count': 60, 'control_marker_count': 61,
        'removed_marker_count': 5, 'removed_marker_labels': REMOVED_LABELS,
        'retained_control_marker_count': 56,
        'new_marker_count': 4, 'new_marker_labels': NEW_LABELS,
        'all_retained_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True, 'two_way_reversal_verified': True,
        'full_61_marker_control_reverse_verified': True,
        'candidate_reverse_to_control_and_cc98_verified': True,
        'marker_removal_recovers_candidate_bytes': True,
        'doccomment_associations_verified': True,
        'removed_private_declaration': REMOVED_PRIVATE_TARGET,
        'removed_private_declaration_remaining_references': 0,
        'helper_before_ambient_variables': True,
        'public_headers_unchanged': True, 'original_data_declarations_unchanged': True,
        'nested_flatten_and_class_helpers_unchanged': True,
        'integral_and_terminal_full_suffix_unchanged': True,
        'new_warning_scope_count': 0,
        'warning_scope_count': 2, 'warning_scopes': warning_scopes,
        'warning_line_bytes_per_scope': 45, 'warning_lines_total_bytes': 90,
        'omit_scope_count': 1, 'omit_scope': omit_scope,
        'phase_warning_uses_default': True, 'no_global_warning_override': True,
        'no_alias_or_as_aux_lemma_change': True,
        'baseline_61_control_preparation_checks': old_checks,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true', help='Run only the frozen bounded diagnostic executor')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts, 'Evidence must not be written in .lake'
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    control_module = load_control_script(repo / CONTROL_SCRIPT)
    prior_module = control_module.load_prior_script(repo / PRIOR_SCRIPT)
    marker_module = prior_module.load_marker_script(repo / MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(
        original, marker_module, prior_module, control_module)
    (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
    (evidence / 'ActualGaussFiniteLeaves.scalar-sum-candidate.lean').write_bytes(candidate)
    (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
    (evidence / (marker_module.MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    write_json(evidence / 'source-edits.json', EDITS)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Full cc98 scalar-sigma proof replacement with unchanged two scoped warning controls and 60 reversible markers; diagnostic only',
        'owner_warning_scope_approval_comment': OWNER_WARNING_SCOPE_APPROVAL_COMMENT,
        'production_approval_flag_meaning': 'This diagnostic does not grant production approval; the two exact retained warning scopes were separately approved by the owner comment recorded above.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'control_script_path': str(CONTROL_SCRIPT), 'control_script_sha256': CONTROL_SCRIPT_SHA,
        'prior_script_path': str(PRIOR_SCRIPT), 'prior_script_sha256': PRIOR_SCRIPT_SHA,
        'marker_script_path': str(MARKER_SCRIPT), 'marker_script_sha256': MARKER_SCRIPT_SHA,
        'control_candidate_sha256': CONTROL_CANDIDATE_SHA, 'control_marked_source_sha256': CONTROL_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'same private provider and public phase controls as frozen 91a3',
            'declarations': control_module.WARNING_TARGETS,
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 90,
            'new_scopes': 0,
        },
        'other_warning_option_override': None,
        'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2', 'Expected unchanged workflow thread setting'
            # No imported guard/constant is rebound. Use frozen 0858 directly.
            marker_module.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['control_script_unchanged'] = sha((repo / CONTROL_SCRIPT).read_bytes()) == CONTROL_SCRIPT_SHA
        result['prior_script_unchanged'] = sha((repo / PRIOR_SCRIPT).read_bytes()) == PRIOR_SCRIPT_SHA
        result['marker_script_unchanged'] = sha((repo / MARKER_SCRIPT).read_bytes()) == MARKER_SCRIPT_SHA
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'scoped_candidate_sha256', 'diagnostic_source_sha256',
        'marker_count', 'two_way_reversal_verified', 'full_61_marker_control_reverse_verified',
        'warning_option_override', 'original_source_unchanged', 'control_script_unchanged',
        'prior_script_unchanged', 'marker_script_unchanged', 'acceptance_evidence',
        'production_approval', 'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
