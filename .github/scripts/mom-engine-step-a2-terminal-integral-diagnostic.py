#!/usr/bin/env python3
"""Full-source terminal integral proof diagnostic with 62 reversible markers.

The frozen 0dd0c279 preparer supplies the complete 5c99 source and all
61 markers. Only a generic measure-theoretic helper and the terminal integral
proof after its original finite-measure letI are changed. The public heads,
data, all earlier proofs, and the original two axiom prints are preserved.
All four retained warning scopes have separate owner approval; the terminal
integral retains its default warning setting. This diagnostic grants no
acceptance or production authority. No imported constant or guard is rebound.
Execution uses the unchanged frozen 0858 runner with its 150 s / 10 s bounds.
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
TERMINAL_WARNING_SCRIPT = Path('.github/scripts/mom-engine-step-a2-terminal-sum-warning-control.py')
TERMINAL_WARNING_SCRIPT_SHA = '0dd0c2792e65920ff848a367095174262ddd97d5e3811da2f483f1e500138a93'
BASE_CANDIDATE_SHA = '5c99faaf4235bc4ed242422e04eb4ad0a6c910c1c3e75646f19aa66f747b2288'
BASE_MARKED_SHA = 'aff852ee8fe91b34bd73220f1faeb4e5c5599b77e91844bbb7683c9127e3b48e'
CANDIDATE_SHA = 'b81c8566cf067792b4e25363381a746281df5460a1e81dad68590ec090d742e2'
CANDIDATE_BLOB = 'f9224b2f42ed28274e2072bdf20d529991a2a4b4'
EXPECTED_MARKED_SHA = '27b3d5305e353a5057da196cb950c0853fdd47e1502e238938118842b840c4ab'
EXPECTED_MARKED_BLOB = 'cad62d8cc4004c64a9d43ce16381da25faef58fe'
HELPER_TARGET = 'scalar_integral_const_add_sum'
TERMINAL_TARGET = 'integral_phase_cost_eq_budgets_leaves'
REMOVED_LABELS = ['TERMINAL_INTEGRAL_BEFORE_SIMP_RW', 'TERMINAL_INTEGRAL_BEFORE_INTEGRAL_ADD',
                  'TERMINAL_INTEGRAL_BEFORE_INTEGRAL_SUM']
NEW_LABELS = ['BEFORE_HEADER_scalar_integral_const_add_sum',
              'COMMAND_CONTINUED_AFTER_scalar_integral_const_add_sum',
              'TERMINAL_INTEGRAL_BEFORE_EXACT', 'TERMINAL_INTEGRAL_AFTER_EXACT']
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'candidate_equivalence_claimed': False, 'fresh_axiom_audit_performed': False,
}
# Exact reviewed edits are embedded; no mutable external candidate is read.
EDITS = {'insert_before': 'variable {K : Type} [Field K] [NumberField K]\n', 'scalar_helper': 'private theorem scalar_integral_const_add_sum\n    {X J : Type*} [MeasurableSpace X] [Fintype J]\n    (μ : Measure X) [IsFiniteMeasure μ]\n    (c : ℝ) (f : X → ℝ) (leaves : J → X → ℝ) (costs : J → ℝ)\n    (hpoint : ∀ ξ, f ξ = c + ∑ b : J, leaves b ξ)\n    (hterms : ∀ b : J, Integrable (leaves b) μ)\n    (hcosts : ∀ b : J, (∫ ξ, leaves b ξ ∂μ) = costs b) :\n    (∫ ξ, f ξ ∂μ) = μ.real Set.univ * c + ∑ b : J, costs b := by\n  calc\n    (∫ ξ, f ξ ∂μ) = ∫ ξ, c + ∑ b : J, leaves b ξ ∂μ :=\n      integral_congr_ae (Filter.Eventually.of_forall hpoint)\n    _ = (∫ _ : X, c ∂μ) + ∫ ξ, ∑ b : J, leaves b ξ ∂μ :=\n      integral_add (integrable_const c)\n        (integrable_finsetSum Finset.univ (fun b _ => hterms b))\n    _ = μ.real Set.univ * c + ∑ b : J, ∫ ξ, leaves b ξ ∂μ := by\n      simpa only [integral_const, smul_eq_mul] using\n        congrArg (fun z : ℝ => (∫ _ : X, c ∂μ) + z)\n          (integral_finsetSum (μ := μ) (f := leaves) Finset.univ\n            (fun b _ => hterms b))\n    _ = μ.real Set.univ * c + ∑ b : J, costs b :=\n      congrArg (fun z : ℝ => μ.real Set.univ * c + z)\n        (Finset.sum_congr rfl (fun b _ => hcosts b))\n\n', 'old_terminal_integral_proof_tail': '  simp_rw [T.phase_cost_eq_budgets_leaves LC RC exceptional F x]\n  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun b _ =>\n    (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable))]\n  rw [integral_const, integral_finsetSum]\n  · simp only [smul_eq_mul]\n    congr 1\n    apply Finset.sum_congr rfl\n    intro b _\n    exact (s.fiberCoveredLeaf LC RC exceptional F x b).integral_firstPhaseCost\n  · intro b _\n    exact (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable\n', 'new_terminal_integral_proof_tail': '  exact scalar_integral_const_add_sum\n    (X := W) (J := s.CoveredLeafKey LC RC)\n    (actualFourierMeasure F)\n    (T.zeroBudget ε Czero + T.tailBudget Cerror)\n    (fun ξ => (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero)\n    (fun b => (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost)\n    (fun b => (s.fiberCoveredLeaf LC RC exceptional F x b).cost)\n    (fun ξ => T.phase_cost_eq_budgets_leaves LC RC exceptional F x ξ ε Cerror Czero)\n    (fun b => leaf_firstPhaseCost_integrable_of_firstKernel\n      (s.fiberCoveredLeaf LC RC exceptional F x b) F\n      (s.fiberCoveredLeaf_firstKernel LC RC exceptional F x b))\n    (fun b => leaf_integral_firstPhaseCost_of_firstKernel\n      (s.fiberCoveredLeaf LC RC exceptional F x b) F\n      (s.fiberCoveredLeaf_firstKernel LC RC exceptional F x b))\n', 'original_finite_measure_letI_preserved': '  letI := actualFourierMeasure_finite F\n'}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_terminal_warning_script(path: Path):
    assert sha(path.read_bytes()) == TERMINAL_WARNING_SCRIPT_SHA, 'Frozen terminal warning control changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_terminal_integral_warning_base', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA and module.SOURCE_BYTES == SOURCE_BYTES
    assert module.CANDIDATE_SHA == BASE_CANDIDATE_SHA and module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    assert module.FALSE_FLAGS == FALSE_FLAGS
    return module


def prepare(original: bytes, marker_module, prior_module, control_module, scalar_module,
            warning_module, terminal_module, terminal_warning_module):
    """Pure: baseline59, candidateb81c, marked62, manifest, checks."""
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA and marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    assert terminal_warning_module.CANDIDATE_SHA == BASE_CANDIDATE_SHA
    assert terminal_warning_module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    baseline, old_candidate, old_marked, old_manifest, old_checks = terminal_warning_module.prepare(
        original, marker_module, prior_module, control_module, scalar_module, warning_module, terminal_module)
    assert len(old_candidate) == 41597 and sha(old_candidate) == BASE_CANDIDATE_SHA
    assert len(old_marked) == 47092 and sha(old_marked) == BASE_MARKED_SHA
    assert len(old_manifest) == old_checks['marker_count'] == 61
    assert old_checks['warning_scope_count'] == 4 and old_checks['new_warning_scope_count'] == 1
    assert old_checks['terminal_integral_warning_uses_default']
    assert old_checks['full_terminal61_marked_inverse_verified']
    assert old_checks['full_warning60_marked_inverse_verified']
    assert old_checks['full_61_marker_control_reverse_verified']
    assert old_checks['candidate_reverse_to_terminal1ee270_and_cc98_verified']
    edits = {key: value.encode() for key, value in EDITS.items()}
    for key, size, expected in [
            ('scalar_helper', 1231, '72135b4fa280cf0b1dda947a2896f1ea8f8c1d41146410b9f33c6365aff1b1ca'),
            ('old_terminal_integral_proof_tail', 522, '7d8e6c56c00143b81de7989472cd2691e32c7391b3f42234e28cc6aeb8ba951c'),
            ('new_terminal_integral_proof_tail', 828, '21f97b3f02cb0ed4a9e7e86ef98afa5c8de486a9dc3382e3eb28cc30ab9a7376')]:
        assert len(edits[key]) == size and sha(edits[key]) == expected, key
    removed = [entry for entry in old_manifest if entry['label'] in REMOVED_LABELS]
    retained = [entry for entry in old_manifest if entry['label'] not in REMOVED_LABELS]
    assert [entry['label'] for entry in removed] == REMOVED_LABELS and len(retained) == 58
    removed_lines = {entry['inserted_line'].encode() for entry in removed}

    def remove_lines(data: bytes, removed_set: set[bytes]) -> bytes:
        return b''.join(line for line in data.splitlines(keepends=True) if line not in removed_set)

    stripped = remove_lines(old_marked, removed_lines)

    def apply_edits(data: bytes) -> bytes:
        assert data.count(edits['insert_before']) == data.count(edits['old_terminal_integral_proof_tail']) == 1
        assert edits['scalar_helper'] not in data
        data = data.replace(edits['insert_before'], edits['scalar_helper'] + edits['insert_before'], 1)
        return data.replace(edits['old_terminal_integral_proof_tail'], edits['new_terminal_integral_proof_tail'], 1)

    def undo_edits(data: bytes) -> bytes:
        assert data.count(edits['scalar_helper']) == data.count(edits['new_terminal_integral_proof_tail']) == 1
        data = data.replace(edits['scalar_helper'], b'', 1)
        return data.replace(edits['new_terminal_integral_proof_tail'], edits['old_terminal_integral_proof_tail'], 1)

    candidate = apply_edits(old_candidate)
    edited_marked = apply_edits(stripped)
    assert len(candidate) == 43134 and sha(candidate) == CANDIDATE_SHA and git_blob(candidate) == CANDIDATE_BLOB

    def marker_line(label: str, kind: str) -> bytes:
        return (('run_cmd' if kind == 'command' else '  run_tac') +
                ' IO.eprintln "A2_ACTUAL_CC98_DIAGNOSTIC ' + label + '"\n').encode()

    kinds = ['command', 'command', 'tactic', 'tactic']
    new_lines = [marker_line(label, kind) for label, kind in zip(NEW_LABELS, kinds)]
    marked = edited_marked.replace(edits['scalar_helper'], new_lines[0] + edits['scalar_helper'] + new_lines[1], 1)
    marked = marked.replace(edits['new_terminal_integral_proof_tail'],
                            new_lines[2] + edits['new_terminal_integral_proof_tail'] + new_lines[3], 1)
    assert len(marked) == 48725 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    assert remove_lines(marked, set(new_lines)) == edited_marked
    inverse_stripped = undo_edits(remove_lines(marked, set(new_lines)))
    assert inverse_stripped == stripped and undo_edits(candidate) == old_candidate
    source_lines = iter(inverse_stripped.splitlines(keepends=True))
    rebuilt = []
    for line in old_marked.splitlines(keepends=True):
        if line not in removed_lines:
            assert next(source_lines, None) == line
        rebuilt.append(line)
    assert next(source_lines, None) is None and b''.join(rebuilt) == old_marked
    all_markers = {entry['inserted_line'].encode() for entry in retained} | set(new_lines)
    assert len(all_markers) == 62 and all(marked.count(line) == 1 for line in all_markers)
    assert remove_lines(marked, all_markers) == candidate
    assert undo_edits(remove_lines(marked, all_markers)) == old_candidate

    # Independently finish the source inverse through every frozen stage to cc98.
    inverse = undo_edits(candidate)
    option = control_module.OPTION
    terminal_anchor = terminal_warning_module.TERMINAL_DOC + terminal_warning_module.TERMINAL_HEADER
    assert inverse.count(option + terminal_anchor) == 1
    inverse = inverse.replace(option + terminal_anchor, terminal_anchor, 1)
    assert sha(inverse) == terminal_module.CANDIDATE_SHA
    earlier_terminal = {key: value.encode() for key, value in terminal_module.EDITS.items()}
    assert inverse.count(earlier_terminal['scalar_helper']) == inverse.count(earlier_terminal['new_terminal_sum_proof_tail']) == 1
    inverse = inverse.replace(earlier_terminal['scalar_helper'], b'', 1)
    inverse = inverse.replace(earlier_terminal['new_terminal_sum_proof_tail'], earlier_terminal['old_terminal_sum_proof_tail'], 1)
    assert sha(inverse) == warning_module.CANDIDATE_SHA
    public_sum_anchor = warning_module.PUBLIC_DOC + warning_module.PUBLIC_HEADER
    assert inverse.count(option + public_sum_anchor) == 1
    inverse = inverse.replace(option + public_sum_anchor, public_sum_anchor, 1)
    assert sha(inverse) == scalar_module.CANDIDATE_SHA
    earlier_scalar = {key: value.encode() for key, value in scalar_module.EDITS.items()}
    assert inverse.count(earlier_scalar['scalar_helper']) == inverse.count(earlier_scalar['new_public_sum_proof']) == 1
    inverse = inverse.replace(earlier_scalar['scalar_helper'], b'', 1)
    inverse = inverse.replace(earlier_scalar['new_public_sum_proof'], earlier_scalar['old_public_sum_proof'], 1)
    assert inverse.count(earlier_scalar['restore_private_before']) == 1
    inverse = inverse.replace(earlier_scalar['restore_private_before'],
                              earlier_scalar['removed_private_declaration'] + earlier_scalar['restore_private_before'], 1)
    assert sha(inverse) == scalar_module.CONTROL_CANDIDATE_SHA
    for prefix, anchor in [(control_module.OMIT, control_module.PHASE_HEADER),
                           (option, control_module.PROVIDER_HEADER),
                           (option, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
        assert inverse.count(prefix + anchor) == 1
        inverse = inverse.replace(prefix + anchor, anchor, 1)
    assert inverse == original

    declaration = re.compile(rb'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|def|abbrev|instance)\s+([^\s:{(]+)')
    def headers(data: bytes):
        return [(match.group(2), data[match.start():data.index(b':=', match.start())])
                for match in declaration.finditer(data) if match.group(2) != HELPER_TARGET.encode()]
    assert headers(candidate) == headers(old_candidate) and len(headers(candidate)) == 56
    def data_blocks(data: bytes):
        return [(match.group(2), data[match.start():data.index(b'\n\n', match.start()) + 2])
                for match in declaration.finditer(data) if match.group(1) in [b'def', b'abbrev', b'instance']]
    assert len(data_blocks(candidate)) == 17
    assert data_blocks(candidate) == data_blocks(old_candidate) == data_blocks(original)
    without_helper = candidate.replace(edits['scalar_helper'], b'', 1)
    assert without_helper.split(edits['new_terminal_integral_proof_tail'], 1) == old_candidate.split(edits['old_terminal_integral_proof_tail'], 1)
    assert edits['original_finite_measure_letI_preserved'] + edits['new_terminal_integral_proof_tail'] in candidate
    finite_marker = next(entry['inserted_line'].encode() for entry in old_manifest
                         if entry['label'] == 'TERMINAL_INTEGRAL_BEFORE_FINITE_MEASURE')
    assert finite_marker + edits['original_finite_measure_letI_preserved'] + new_lines[2] in marked
    assert candidate.count(option) == marked.count(option) == 4
    assert candidate.count(control_module.OMIT) == marked.count(control_module.OMIT) == 1
    assert candidate.index(edits['scalar_helper']) < candidate.index(edits['insert_before'])
    assert option + ('theorem ' + TERMINAL_TARGET + '\n').encode() not in candidate
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in candidate.splitlines() if line.startswith(prefix)] == [
            line for line in original.splitlines() if line.startswith(prefix)]

    manifest = []
    for entry in retained:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['terminal_warning61_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        updated['added_in_terminal_integral_diagnostic'] = False
        manifest.append(updated)
    for label, kind, line in zip(NEW_LABELS, kinds, new_lines):
        manifest.append({'label': label, 'kind': kind, 'inserted_line': line.decode(),
                         'original_insert_before_line': None,
                         'instrumented_line': marked[:marked.index(line)].count(b'\n') + 1,
                         'added_in_terminal_integral_diagnostic': True})
    manifest.sort(key=lambda entry: entry['instrumented_line'])
    assert len(manifest) == 62 and len({entry['label'] for entry in manifest}) == 62
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] == entry['inserted_line'].encode()
               for entry in manifest)
    retained_line_set = {entry['inserted_line'].encode() for entry in retained}
    assert [line for line in marked.splitlines(keepends=True) if line in retained_line_set] == [
        line for line in old_marked.splitlines(keepends=True) if line in retained_line_set]

    warning_scopes = []
    for scope in old_checks['warning_scopes']:
        updated = {key: value for key, value in scope.items() if key not in ['temporary_control_only', 'production_approval']}
        before = marker_line('BEFORE_HEADER_' + scope['short_name'], 'command')
        assert marked.count(before + option) == 1
        updated['base_terminal_warning61_instrumented_line'] = scope['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(before + option)].count(b'\n') + 2
        updated['owner_scope_approval_comment'] = (6564186347 if scope['short_name'] == terminal_warning_module.TERMINAL_TARGET
            else 6563834756 if scope['short_name'] == warning_module.PUBLIC_TARGET else 6563548652)
        updated['retained_owner_approved_scope'] = True
        warning_scopes.append(updated)
    omit_scope = dict(old_checks['omit_scope'])
    omit_scope['base_terminal_warning61_instrumented_line'] = omit_scope['instrumented_line']
    omit_scope['instrumented_line'] = marked[:marked.index(control_module.OMIT + control_module.PHASE_HEADER)].count(b'\n') + 1
    checks = {
        'marker_count': 62, 'base_marker_count': 61,
        'removed_marker_count': 3, 'removed_marker_labels': REMOVED_LABELS,
        'retained_base_marker_count': 58, 'new_marker_count': 4, 'new_marker_labels': NEW_LABELS,
        'all_retained_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True, 'two_way_reversal_verified': True,
        'full_terminal_warning61_marked_inverse_verified': True,
        'full_terminal61_marked_inverse_verified': True,
        'full_warning60_marked_inverse_verified': True,
        'full_61_marker_control_reverse_verified': True,
        'candidate_reverse_to_base5c99_and_cc98_verified': True,
        'marker_removal_recovers_candidate_bytes': True, 'doccomment_associations_verified': True,
        'original_finite_measure_letI_preserved': True, 'finite_measure_marker_preserved': True,
        'all_56_previous_headers_unchanged': True, 'all_17_original_data_declarations_unchanged': True,
        'all_other_proof_bytes_unchanged': True,
        'public_sum_and_integral_proofs_and_checkpoints_unchanged': True,
        'terminal_sum_proof_and_checkpoints_unchanged': True,
        'original_imports_and_print_axioms_unchanged': True, 'helper_before_ambient_variables': True,
        'warning_scope_count': 4, 'warning_scopes': warning_scopes, 'new_warning_scope_count': 0,
        'warning_line_bytes_per_scope': 45, 'warning_lines_total_bytes': 180,
        'omit_scope_count': 1, 'omit_scope': omit_scope,
        'terminal_sum_warning_uses_default': False, 'terminal_integral_warning_uses_default': True,
        'public_integral_warning_uses_default': True, 'no_global_warning_override': True,
        'no_alias_or_as_aux_lemma_change': True,
        'base_terminal_warning61_preparation_checks': old_checks,
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
    terminal_warning = load_terminal_warning_script(repo / TERMINAL_WARNING_SCRIPT)
    terminal = terminal_warning.load_terminal_script(repo / terminal_warning.TERMINAL_SCRIPT)
    warning = terminal.load_warning_script(repo / terminal.WARNING_SCRIPT)
    scalar = warning.load_scalar_script(repo / warning.SCALAR_SCRIPT)
    control = scalar.load_control_script(repo / scalar.CONTROL_SCRIPT)
    prior = control.load_prior_script(repo / scalar.PRIOR_SCRIPT)
    marker = prior.load_marker_script(repo / scalar.MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(
        original, marker, prior, control, scalar, warning, terminal, terminal_warning)
    script_pins = {
        str(TERMINAL_WARNING_SCRIPT): TERMINAL_WARNING_SCRIPT_SHA,
        str(terminal_warning.TERMINAL_SCRIPT): terminal_warning.TERMINAL_SCRIPT_SHA,
        str(terminal.WARNING_SCRIPT): terminal.WARNING_SCRIPT_SHA,
        str(warning.SCALAR_SCRIPT): warning.SCALAR_SCRIPT_SHA,
        str(scalar.CONTROL_SCRIPT): scalar.CONTROL_SCRIPT_SHA,
        str(scalar.PRIOR_SCRIPT): scalar.PRIOR_SCRIPT_SHA,
        str(scalar.MARKER_SCRIPT): scalar.MARKER_SCRIPT_SHA,
    }
    for name, data in [('ActualGaussFiniteLeaves.original.lean', original),
                       ('ActualGaussFiniteLeaves.terminal-integral-candidate.lean', candidate),
                       ('MomEngineActualDiagCc98c8a2.baseline-marked.lean', baseline),
                       (marker.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    write_json(evidence / 'source-edits.json', EDITS)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Complete terminal integral proof candidate with 62 reversible markers; diagnostic only',
        'owner_warning_scope_approval_comments': [6563548652, 6563834756, 6564186347],
        'production_approval_flag_meaning': 'This diagnostic grants no production approval. All four unchanged warning scopes have the separate owner approvals recorded above; older nested control metadata records the earlier diagnostic states.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'script_pins': script_pins, 'terminal_warning_script_path': str(TERMINAL_WARNING_SCRIPT),
        'terminal_warning_script_sha256': TERMINAL_WARNING_SCRIPT_SHA,
        'base_candidate_sha256': BASE_CANDIDATE_SHA, 'base_marked_source_sha256': BASE_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'four unchanged owner-approved provider/public-phase/public-sum/terminal-sum declarations',
            'declarations': [scope['declaration'] for scope in checks['warning_scopes']],
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 180, 'new_scopes': 0},
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
        result['frozen_scripts_unchanged'] = {path: sha((repo / path).read_bytes()) == expected
                                             for path, expected in script_pins.items()}
        assert result['original_source_unchanged'] and all(result['frozen_scripts_unchanged'].values())
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'scoped_candidate_sha256', 'diagnostic_source_sha256', 'marker_count',
        'full_terminal_warning61_marked_inverse_verified', 'candidate_reverse_to_base5c99_and_cc98_verified',
        'warning_option_override', 'terminal_integral_warning_uses_default',
        'original_source_unchanged', 'frozen_scripts_unchanged', 'acceptance_evidence',
        'production_approval', 'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
