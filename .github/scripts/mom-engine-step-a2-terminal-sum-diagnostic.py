#!/usr/bin/env python3
"""Full-source terminal scalar proof diagnostic with 61 reversible markers.

The frozen 283752 preparer supplies the complete 03c62 source and all sixty
markers. Only a generic scalar helper and the terminal finite-sum proof tail
are changed. The original change tactic, public sum/integral boundaries and
the entire terminal integral suffix are preserved. All three retained warning
scopes have separate owner approval; this diagnostic grants no acceptance or
production authority. No imported constant or guard is rebound. Execution
uses the unchanged frozen 0858 runner with its 150 s / 10 s bounds.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys

SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean')
SOURCE_SHA = 'cc98c8a2c5c3c3f6c59695935245f463c84e6e7f7c8292b5062e2d1813d94c87'
SOURCE_BYTES = 40282
WARNING_SCRIPT = Path('.github/scripts/mom-engine-step-a2-scalar-sum-warning-control.py')
WARNING_SCRIPT_SHA = '283752262162f6935370110ed0bd613a6cc41ebf5de805799b5749d37c69b5df'
BASE_CANDIDATE_SHA = '03c62f89a35b052776f8a039ea61a9830a25b692a4f438bc61ffdc373c2dbf6d'
BASE_MARKED_SHA = 'c66540e7b40de0615ffdfed539620c07af0f53e76e496c52f63383a95ca117c3'
CANDIDATE_SHA = '1ee270ad098598dc83ac7ec2c8eef4fcb8fd3a88530958b14e32d955463f480e'
CANDIDATE_BLOB = '6b14da68c8fe19c43e6599f43a4421e929adbb51'
EXPECTED_MARKED_SHA = 'c652bc5bcd47053a57b64bdd1f8b0b17324a229875aed7106c85eae01fd6e1a6'
EXPECTED_MARKED_BLOB = '834fd38fe72cd64d58b57e6612bda12d785cd8b7'
HELPER_TARGET = 'scalar_weighted_terminal_sum'
TERMINAL_TARGET = 'phase_cost_eq_budgets_leaves'
REMOVED_LABELS = ['TERMINAL_SUM_BEFORE_RW', 'TERMINAL_SUM_BEFORE_SIMP', 'TERMINAL_SUM_BEFORE_RING']
NEW_LABELS = ['BEFORE_HEADER_scalar_weighted_terminal_sum',
              'COMMAND_CONTINUED_AFTER_scalar_weighted_terminal_sum',
              'TERMINAL_SUM_BEFORE_EXACT', 'TERMINAL_SUM_AFTER_EXACT']
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'candidate_equivalence_claimed': False, 'fresh_axiom_audit_performed': False,
}
# Exact reviewed edits are embedded; no mutable external candidate is read.
EDITS = {'insert_before': 'variable {K : Type} [Field K] [NumberField K]\n', 'scalar_helper': 'private theorem scalar_weighted_terminal_sum\n    {J : Type*} [Fintype J]\n    (weight zeroCoefficient zeroAmplitude zeroPower\n      tailCoefficient tailAmplitude tailPower nonzero : ℝ)\n    (leaves scaledLeaves : J → ℝ)\n    (hsum : nonzero = ∑ b : J, leaves b)\n    (hscaled : ∀ b : J, scaledLeaves b = weight * leaves b) :\n    weight * (zeroCoefficient * zeroAmplitude * zeroPower + nonzero +\n      tailCoefficient * tailAmplitude * tailPower) =\n      weight * zeroCoefficient * zeroAmplitude * zeroPower +\n      weight * tailCoefficient * tailAmplitude * tailPower +\n      ∑ b : J, scaledLeaves b := by\n  rw [hsum]\n  simp only [hscaled, Finset.mul_sum, mul_add, mul_assoc]\n  ring\n\n', 'old_terminal_sum_proof_tail': '  rw [s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x ξ]\n  simp only [fiberCoveredLeaf, ActualHybridLeaf.scale_firstPhaseCost,\n    zeroBudget, tailBudget, Finset.mul_sum, mul_add, mul_assoc]\n  ring\n', 'new_terminal_sum_proof_tail': '  exact scalar_weighted_terminal_sum\n    (J := s.CoveredLeafKey LC RC)\n    (s.fiber : ℝ)\n    Czero (T.windows.multiplicity * T.zeroAmplitude) (Z ^ (T.productExponent * ε))\n    Cerror (T.windows.multiplicity * T.tailAmplitude) (Z ^ (-Nsave))\n    (s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ)\n    (fun b => (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ)\n    (fun b => (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost ξ)\n    (s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x ξ)\n    (fun b => (s.coveredLeaf LC RC exceptional F x b).scale_firstPhaseCost\n      (s.fiber : ℝ) (Nat.cast_nonneg _) ξ)\n', 'original_change_prefix_preserved': '  change (s.fiber : ℝ) *\n    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +\n      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ +\n      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) = _\n'}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_warning_script(path: Path):
    assert sha(path.read_bytes()) == WARNING_SCRIPT_SHA, 'Frozen warning control changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_terminal_scalar_warning_base', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA and module.SOURCE_BYTES == SOURCE_BYTES
    assert module.CANDIDATE_SHA == BASE_CANDIDATE_SHA and module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    assert module.FALSE_FLAGS == FALSE_FLAGS
    return module


def prepare(original: bytes, marker_module, prior_module, control_module, scalar_module, warning_module):
    """Pure: baseline59, candidate1ee270, marked61, manifest, checks."""
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA and marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    assert warning_module.CANDIDATE_SHA == BASE_CANDIDATE_SHA
    assert warning_module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    baseline, old_candidate, old_marked, old_manifest, old_checks = warning_module.prepare(
        original, marker_module, prior_module, control_module, scalar_module)
    assert len(old_candidate) == 40427 and sha(old_candidate) == BASE_CANDIDATE_SHA
    assert len(old_marked) == 45802 and sha(old_marked) == BASE_MARKED_SHA
    assert len(old_manifest) == old_checks['marker_count'] == 60
    assert old_checks['warning_scope_count'] == 3
    assert old_checks['full_60_marker_scalar_reverse_verified']
    assert old_checks['full_61_marker_control_reverse_verified']
    edits = {key: value.encode() for key, value in EDITS.items()}
    for key, size, expected in [
            ('scalar_helper', 692, '86addbffb8f84f192451f5bdd8da11fd0c246681c49e2529d89ee290b3870c97'),
            ('old_terminal_sum_proof_tail', 215, '77f676da179240462e433bfdf520febe154af7039127a0600af3579d4d2dd7f8'),
            ('new_terminal_sum_proof_tail', 648, '67176bcd87885331aa394af832d8ceb159da93bbc7ecfdb5b1af9f065bf73735')]:
        assert len(edits[key]) == size and sha(edits[key]) == expected, key
    removed = [m for m in old_manifest if m['label'] in REMOVED_LABELS]
    retained = [m for m in old_manifest if m['label'] not in REMOVED_LABELS]
    assert [m['label'] for m in removed] == REMOVED_LABELS
    assert len(retained) == 57
    removed_lines = {m['inserted_line'].encode() for m in removed}

    def remove_lines(data: bytes, removed_set: set[bytes]) -> bytes:
        return b''.join(line for line in data.splitlines(keepends=True) if line not in removed_set)

    stripped = remove_lines(old_marked, removed_lines)

    def apply_edits(data: bytes) -> bytes:
        assert data.count(edits['insert_before']) == data.count(edits['old_terminal_sum_proof_tail']) == 1
        assert edits['scalar_helper'] not in data
        data = data.replace(edits['insert_before'], edits['scalar_helper'] + edits['insert_before'], 1)
        return data.replace(edits['old_terminal_sum_proof_tail'], edits['new_terminal_sum_proof_tail'], 1)

    def undo_edits(data: bytes) -> bytes:
        assert data.count(edits['scalar_helper']) == data.count(edits['new_terminal_sum_proof_tail']) == 1
        data = data.replace(edits['scalar_helper'], b'', 1)
        return data.replace(edits['new_terminal_sum_proof_tail'], edits['old_terminal_sum_proof_tail'], 1)

    candidate = apply_edits(old_candidate)
    edited_marked = apply_edits(stripped)
    assert len(candidate) == 41552 and sha(candidate) == CANDIDATE_SHA and git_blob(candidate) == CANDIDATE_BLOB

    def marker_line(label: str, kind: str) -> bytes:
        return (('run_cmd' if kind == 'command' else '  run_tac') +
                ' IO.eprintln "A2_ACTUAL_CC98_DIAGNOSTIC ' + label + '"\n').encode()

    kinds = ['command', 'command', 'tactic', 'tactic']
    new_lines = [marker_line(label, kind) for label, kind in zip(NEW_LABELS, kinds)]
    marked = edited_marked.replace(edits['scalar_helper'], new_lines[0] + edits['scalar_helper'] + new_lines[1], 1)
    marked = marked.replace(edits['new_terminal_sum_proof_tail'],
                            new_lines[2] + edits['new_terminal_sum_proof_tail'] + new_lines[3], 1)
    assert len(marked) == 47047 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    assert remove_lines(marked, set(new_lines)) == edited_marked
    inverse_stripped = undo_edits(remove_lines(marked, set(new_lines)))
    assert inverse_stripped == stripped and undo_edits(candidate) == old_candidate
    # Reinsert exactly the three original obsolete marker lines in their old stream.
    source_lines = iter(inverse_stripped.splitlines(keepends=True))
    rebuilt = []
    for line in old_marked.splitlines(keepends=True):
        if line not in removed_lines:
            assert next(source_lines, None) == line
        rebuilt.append(line)
    assert next(source_lines, None) is None and b''.join(rebuilt) == old_marked
    all_markers = {m['inserted_line'].encode() for m in retained} | set(new_lines)
    assert len(all_markers) == 61 and all(marked.count(line) == 1 for line in all_markers)
    assert remove_lines(marked, all_markers) == candidate
    assert undo_edits(remove_lines(marked, all_markers)) == old_candidate

    # Finish the independent inverse through the frozen scalar and cc98 sources.
    inverse = undo_edits(candidate)
    warning_anchor = warning_module.PUBLIC_DOC + warning_module.PUBLIC_HEADER
    assert inverse.count(warning_module.OPTION + warning_anchor) == 1
    inverse = inverse.replace(warning_module.OPTION + warning_anchor, warning_anchor, 1)
    assert sha(inverse) == scalar_module.CANDIDATE_SHA
    earlier = {k: v.encode() for k, v in scalar_module.EDITS.items()}
    inverse = inverse.replace(earlier['scalar_helper'], b'', 1)
    inverse = inverse.replace(earlier['new_public_sum_proof'], earlier['old_public_sum_proof'], 1)
    inverse = inverse.replace(earlier['restore_private_before'],
                              earlier['removed_private_declaration'] + earlier['restore_private_before'], 1)
    assert sha(inverse) == scalar_module.CONTROL_CANDIDATE_SHA
    for prefix, anchor in [
            (control_module.OMIT, control_module.PHASE_HEADER),
            (control_module.OPTION, control_module.PROVIDER_HEADER),
            (control_module.OPTION, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
        assert inverse.count(prefix + anchor) == 1
        inverse = inverse.replace(prefix + anchor, anchor, 1)
    assert inverse == original

    # Original statements, data, change, and the entire terminal integral stay literal.
    declaration = re.compile(rb'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:theorem|def|abbrev|instance)\s+([^\s:{(]+)')
    def headers(data: bytes):
        return [(m.group(1), data[m.start():data.index(b':=', m.start())])
                for m in declaration.finditer(data) if m.group(1) != HELPER_TARGET.encode()]
    assert headers(candidate) == headers(old_candidate) and len(headers(candidate)) == 55
    assert candidate.count(edits['original_change_prefix_preserved']) == 1
    change_marker = next(m['inserted_line'].encode() for m in old_manifest if m['label'] == 'TERMINAL_SUM_BEFORE_CHANGE')
    assert change_marker + edits['original_change_prefix_preserved'] + new_lines[2] in marked
    suffix = b'theorem integral_phase_cost_eq_budgets_leaves\n'
    assert candidate[candidate.index(suffix):] == old_candidate[old_candidate.index(suffix):]
    assert candidate[candidate.index(suffix):] == original[original.index(suffix):]
    assert marked[marked.index(suffix):] == old_marked[old_marked.index(suffix):]
    segment_start = warning_module.PUBLIC_DOC + warning_module.PUBLIC_HEADER
    segment_end = b'/-- Exact terminal and nonzero separation on the original second\n'
    assert candidate[candidate.index(segment_start):candidate.index(segment_end)] == old_candidate[old_candidate.index(segment_start):old_candidate.index(segment_end)]
    assert candidate.index(edits['scalar_helper']) < candidate.index(edits['insert_before'])
    assert candidate.count(control_module.OPTION) == marked.count(control_module.OPTION) == 3
    assert candidate.count(control_module.OMIT) == marked.count(control_module.OMIT) == 1
    assert b'as_aux_lemma' not in candidate
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in candidate.splitlines() if line.startswith(prefix)] == [
            line for line in original.splitlines() if line.startswith(prefix)]

    manifest = []
    for entry in retained:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['base_warning60_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        updated['is_new_terminal_scalar_marker'] = False
        manifest.append(updated)
    anchors = [original[:original.index(edits['insert_before'])].count(b'\n') + 1] * 2
    old_tail_line = original[:original.index(edits['old_terminal_sum_proof_tail'])].count(b'\n') + 1
    anchors += [old_tail_line, old_tail_line + edits['old_terminal_sum_proof_tail'].count(b'\n')]
    for label, kind, line, anchor_line in zip(NEW_LABELS, kinds, new_lines, anchors):
        manifest.append({'label': label, 'kind': kind, 'inserted_line': line.decode(),
            'original_insert_before_line': anchor_line, 'original_line_is_edit_anchor': True,
            'base_warning60_instrumented_line': None,
            'instrumented_line': marked[:marked.index(line)].count(b'\n') + 1,
            'origin': 'terminal_scalar_replacement', 'is_new_terminal_scalar_marker': True})
    manifest.sort(key=lambda m: m['instrumented_line'])
    assert len(manifest) == 61
    assert [m['label'] for m in manifest if not m['is_new_terminal_scalar_marker']] == [m['label'] for m in retained]
    assert all(marked.splitlines(keepends=True)[m['instrumented_line'] - 1] == m['inserted_line'].encode() for m in manifest)
    warning_scopes = []
    for scope in old_checks['warning_scopes']:
        updated = {k: v for k, v in scope.items() if k not in ['temporary_control_only', 'production_approval']}
        before = marker_line('BEFORE_HEADER_' + scope['short_name'], 'command')
        assert marked.count(before + control_module.OPTION) == 1
        updated['base_warning60_instrumented_line'] = scope['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(before + control_module.OPTION)].count(b'\n') + 2
        updated['owner_scope_approval_comment'] = 6563834756 if scope['short_name'] == warning_module.PUBLIC_TARGET else 6563548652
        updated['retained_owner_approved_scope'] = True
        warning_scopes.append(updated)
    omit_scope = dict(old_checks['omit_scope'])
    omit_scope['base_warning60_instrumented_line'] = omit_scope['instrumented_line']
    omit_scope['instrumented_line'] = marked[:marked.index(control_module.OMIT + control_module.PHASE_HEADER)].count(b'\n') + 1
    checks = {
        'marker_count': 61, 'base_marker_count': 60,
        'removed_marker_count': 3, 'removed_marker_labels': REMOVED_LABELS,
        'retained_base_marker_count': 57, 'new_marker_count': 4, 'new_marker_labels': NEW_LABELS,
        'all_retained_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True, 'two_way_reversal_verified': True,
        'full_warning60_marked_inverse_verified': True, 'full_61_marker_control_reverse_verified': True,
        'candidate_reverse_to_base03c62_and_cc98_verified': True,
        'marker_removal_recovers_candidate_bytes': True, 'doccomment_associations_verified': True,
        'original_change_prefix_preserved': True, 'before_change_marker_preserved': True,
        'all_55_previous_headers_unchanged': True, 'original_data_declarations_unchanged': True,
        'public_sum_and_integral_proofs_and_checkpoints_unchanged': True,
        'terminal_integral_full_suffix_unchanged': True, 'helper_before_ambient_variables': True,
        'warning_scope_count': 3, 'warning_scopes': warning_scopes, 'new_warning_scope_count': 0,
        'warning_line_bytes_per_scope': 45, 'warning_lines_total_bytes': 135,
        'omit_scope_count': 1, 'omit_scope': omit_scope,
        'terminal_sum_warning_uses_default': True, 'terminal_integral_warning_uses_default': True,
        'public_integral_warning_uses_default': True, 'no_global_warning_override': True,
        'no_alias_or_as_aux_lemma_change': True,
        'base_warning60_preparation_checks': old_checks,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    warning = load_warning_script(repo / WARNING_SCRIPT)
    scalar = warning.load_scalar_script(repo / warning.SCALAR_SCRIPT)
    control = scalar.load_control_script(repo / scalar.CONTROL_SCRIPT)
    prior = control.load_prior_script(repo / scalar.PRIOR_SCRIPT)
    marker = prior.load_marker_script(repo / scalar.MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(original, marker, prior, control, scalar, warning)
    script_pins = {str(WARNING_SCRIPT): WARNING_SCRIPT_SHA,
        str(warning.SCALAR_SCRIPT): warning.SCALAR_SCRIPT_SHA,
        str(scalar.CONTROL_SCRIPT): scalar.CONTROL_SCRIPT_SHA,
        str(scalar.PRIOR_SCRIPT): scalar.PRIOR_SCRIPT_SHA,
        str(scalar.MARKER_SCRIPT): scalar.MARKER_SCRIPT_SHA}
    for name, data in [('ActualGaussFiniteLeaves.original.lean', original),
                       ('ActualGaussFiniteLeaves.terminal-scalar-candidate.lean', candidate),
                       ('MomEngineActualDiagCc98c8a2.baseline-marked.lean', baseline),
                       (marker.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    write_json(evidence / 'source-edits.json', EDITS)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Complete terminal scalar proof candidate with 61 reversible markers; diagnostic only',
        'owner_warning_scope_approval_comments': [6563548652, 6563834756],
        'production_approval_flag_meaning': 'This diagnostic grants no production approval. All three unchanged warning scopes have the separate owner approvals recorded above; older nested control metadata records the earlier diagnostic state.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'script_pins': script_pins, 'warning_script_path': str(WARNING_SCRIPT),
        'warning_script_sha256': WARNING_SCRIPT_SHA,
        'base_candidate_sha256': BASE_CANDIDATE_SHA, 'base_marked_source_sha256': BASE_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'three unchanged owner-approved provider/public-phase/public-sum declarations',
            'declarations': [s['declaration'] for s in checks['warning_scopes']],
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 135, 'new_scopes': 0},
        'other_warning_option_override': None,
        'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            marker.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['frozen_scripts_unchanged'] = {path: sha((repo / path).read_bytes()) == expected for path, expected in script_pins.items()}
        assert result['original_source_unchanged'] and all(result['frozen_scripts_unchanged'].values())
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'scoped_candidate_sha256', 'diagnostic_source_sha256', 'marker_count',
        'full_warning60_marked_inverse_verified', 'candidate_reverse_to_base03c62_and_cc98_verified',
        'warning_option_override', 'terminal_sum_warning_uses_default', 'terminal_integral_warning_uses_default',
        'original_source_unchanged', 'frozen_scripts_unchanged', 'acceptance_evidence',
        'production_approval', 'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
