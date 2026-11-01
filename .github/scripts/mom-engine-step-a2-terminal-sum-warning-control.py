#!/usr/bin/env python3
"""One-scope warning control for the frozen full-source 61-marker terminal diagnostic.

The pinned 9fa475fa preparer supplies the complete 1ee270ad source and all
61 markers. This control inserts exactly one 45-byte declaration-local
unusedSectionVars option before phase_cost_eq_budgets_leaves's original
doccomment. The three earlier owner-approved scopes stay unchanged; the
additional terminal-sum scope is temporary diagnostic evidence, with no
production approval. Both integral declarations retain their default warning
settings. No imported constant or guard is rebound and no tracked source is
edited. The original frozen 0858 executor supplies the 150 s / 10 s bounds.
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
TERMINAL_SCRIPT = Path('.github/scripts/mom-engine-step-a2-terminal-sum-diagnostic.py')
TERMINAL_SCRIPT_SHA = '9fa475faf51b11596747dbfa5dcd496d76d0b28a27f77fb1e356ecb8bbaeed6b'
BASE_CANDIDATE_SHA = '1ee270ad098598dc83ac7ec2c8eef4fcb8fd3a88530958b14e32d955463f480e'
BASE_MARKED_SHA = 'c652bc5bcd47053a57b64bdd1f8b0b17324a229875aed7106c85eae01fd6e1a6'
CANDIDATE_SHA = '5c99faaf4235bc4ed242422e04eb4ad0a6c910c1c3e75646f19aa66f747b2288'
CANDIDATE_BLOB = '0569b124dedc453ca7e8a477b3fda42eb356895e'
EXPECTED_MARKED_SHA = 'aff852ee8fe91b34bd73220f1faeb4e5c5599b77e91844bbb7683c9127e3b48e'
EXPECTED_MARKED_BLOB = '3af220557124fa486e6899809cbbb9b97bbc74ad'
TERMINAL_TARGET = 'phase_cost_eq_budgets_leaves'
TERMINAL_QUALIFIED = 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.TerminalCalibration.' + TERMINAL_TARGET
TERMINAL_DOC = b'/-- Exact terminal and nonzero separation on the original second\nsource.  Neither terminal budget is a new assumed aggregate estimate. -/\n'
TERMINAL_HEADER = b'theorem phase_cost_eq_budgets_leaves\n'
OPTION = b'set_option linter.unusedSectionVars false in\n'
OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENTS = [6563548652, 6563834756]
FALSE_FLAGS = {
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
    'fresh_axiom_audit_performed': False,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_terminal_script(path: Path):
    assert sha(path.read_bytes()) == TERMINAL_SCRIPT_SHA, 'Frozen terminal 61-marker wrapper changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_terminal61_warning_control_base', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA
    assert module.SOURCE_BYTES == SOURCE_BYTES and module.CANDIDATE_SHA == BASE_CANDIDATE_SHA
    assert module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    assert module.FALSE_FLAGS == FALSE_FLAGS
    return module


def prepare(original: bytes, marker_module, prior_module, control_module,
            scalar_module, warning_module, terminal_module):
    """Pure: baseline59, scoped candidate, scoped marked61, manifest, checks.

    Removing the only new OPTION recovers both pinned terminal61 byte streams.
    Their complete inverse chain is rechecked by terminal_module.prepare, then
    an independent source inverse below rechecks every edit back to cc98.
    """
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA and marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    assert terminal_module.CANDIDATE_SHA == BASE_CANDIDATE_SHA
    assert terminal_module.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    baseline, old_candidate, old_marked, old_manifest, old_checks = terminal_module.prepare(
        original, marker_module, prior_module, control_module, scalar_module, warning_module)
    assert len(old_candidate) == 41552 and sha(old_candidate) == BASE_CANDIDATE_SHA
    assert len(old_marked) == 47047 and sha(old_marked) == BASE_MARKED_SHA
    assert len(old_manifest) == old_checks['marker_count'] == 61
    assert old_checks['warning_scope_count'] == 3 and old_checks['new_warning_scope_count'] == 0
    assert old_checks['terminal_sum_warning_uses_default']
    assert old_checks['terminal_integral_warning_uses_default']
    assert old_checks['full_warning60_marked_inverse_verified']
    assert old_checks['full_61_marker_control_reverse_verified']
    assert old_checks['candidate_reverse_to_base03c62_and_cc98_verified']

    anchor = TERMINAL_DOC + TERMINAL_HEADER
    assert len(OPTION) == 45
    assert old_candidate.count(anchor) == old_marked.count(anchor) == 1
    assert OPTION + anchor not in old_candidate and OPTION + anchor not in old_marked
    before = ('run_cmd IO.eprintln "A2_ACTUAL_CC98_DIAGNOSTIC BEFORE_HEADER_' + TERMINAL_TARGET + '"\n').encode()
    assert before + anchor in old_marked
    candidate = old_candidate.replace(anchor, OPTION + anchor, 1)
    marked = old_marked.replace(anchor, OPTION + anchor, 1)
    assert len(candidate) == 41597 and sha(candidate) == CANDIDATE_SHA
    assert git_blob(candidate) == CANDIDATE_BLOB
    assert len(marked) == 47092 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    assert candidate.replace(OPTION + anchor, anchor, 1) == old_candidate
    assert marked.replace(OPTION + anchor, anchor, 1) == old_marked
    assert before + OPTION + anchor in marked
    assert candidate.count(OPTION) == marked.count(OPTION) == 4
    assert candidate.count(control_module.OMIT) == marked.count(control_module.OMIT) == 1

    marker_lines = {m['inserted_line'].encode() for m in old_manifest}
    assert len(marker_lines) == 61
    assert all(marked.count(line) == 1 for line in marker_lines)
    unmarked = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert unmarked == candidate
    assert unmarked.replace(OPTION + anchor, anchor, 1) == old_candidate
    assert [line for line in marked.splitlines(keepends=True) if line in marker_lines] == [
        line for line in old_marked.splitlines(keepends=True) if line in marker_lines]

    # Independently undo the terminal scalar edits and all earlier source edits.
    inverse = unmarked.replace(OPTION + anchor, anchor, 1)
    terminal_edits = {k: v.encode() for k, v in terminal_module.EDITS.items()}
    assert inverse.count(terminal_edits['scalar_helper']) == 1
    assert inverse.count(terminal_edits['new_terminal_sum_proof_tail']) == 1
    inverse = inverse.replace(terminal_edits['scalar_helper'], b'', 1)
    inverse = inverse.replace(terminal_edits['new_terminal_sum_proof_tail'],
                              terminal_edits['old_terminal_sum_proof_tail'], 1)
    assert sha(inverse) == terminal_module.BASE_CANDIDATE_SHA == warning_module.CANDIDATE_SHA
    warning_anchor = warning_module.PUBLIC_DOC + warning_module.PUBLIC_HEADER
    assert inverse.count(OPTION + warning_anchor) == 1
    inverse = inverse.replace(OPTION + warning_anchor, warning_anchor, 1)
    assert sha(inverse) == scalar_module.CANDIDATE_SHA
    scalar_edits = {k: v.encode() for k, v in scalar_module.EDITS.items()}
    assert inverse.count(scalar_edits['scalar_helper']) == inverse.count(scalar_edits['new_public_sum_proof']) == 1
    inverse = inverse.replace(scalar_edits['scalar_helper'], b'', 1)
    inverse = inverse.replace(scalar_edits['new_public_sum_proof'], scalar_edits['old_public_sum_proof'], 1)
    assert inverse.count(scalar_edits['restore_private_before']) == 1
    inverse = inverse.replace(scalar_edits['restore_private_before'],
                              scalar_edits['removed_private_declaration'] + scalar_edits['restore_private_before'], 1)
    assert sha(inverse) == scalar_module.CONTROL_CANDIDATE_SHA
    for prefix, scope_anchor in [
            (control_module.OMIT, control_module.PHASE_HEADER),
            (OPTION, control_module.PROVIDER_HEADER),
            (OPTION, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
        assert inverse.count(prefix + scope_anchor) == 1
        inverse = inverse.replace(prefix + scope_anchor, scope_anchor, 1)
    assert inverse == original

    # The added scope is outside the original doccomment, header and proof.
    declaration = re.compile(rb'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:theorem|def|abbrev|instance)\s+([^\s:{(]+)')
    def headers(data: bytes):
        return [(m.group(1), data[m.start():data.index(b':=', m.start())])
                for m in declaration.finditer(data)]
    assert headers(candidate) == headers(old_candidate)
    assert len(headers(candidate)) == 56
    assert candidate[candidate.index(TERMINAL_HEADER):] == old_candidate[old_candidate.index(TERMINAL_HEADER):]
    assert marked[marked.index(TERMINAL_HEADER):] == old_marked[old_marked.index(TERMINAL_HEADER):]
    integral_suffix = b'theorem integral_phase_cost_eq_budgets_leaves\n'
    assert candidate[candidate.index(integral_suffix):] == original[original.index(integral_suffix):]
    assert candidate[candidate.index(integral_suffix):] == old_candidate[old_candidate.index(integral_suffix):]
    assert marked[marked.index(integral_suffix):] == old_marked[old_marked.index(integral_suffix):]
    assert OPTION + integral_suffix not in candidate and OPTION + integral_suffix not in marked
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in candidate.splitlines() if line.startswith(prefix)] == [
            line for line in original.splitlines() if line.startswith(prefix)]

    manifest = []
    for entry in old_manifest:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['terminal61_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        updated['added_in_terminal_warning_control'] = False
        manifest.append(updated)
    assert [m['label'] for m in manifest] == [m['label'] for m in old_manifest]
    assert all(marked.splitlines(keepends=True)[m['instrumented_line'] - 1] == m['inserted_line'].encode()
               for m in manifest)
    # All three retained approved scopes and the omit scope precede this option.
    for scope in old_checks['warning_scopes']:
        assert marked.splitlines(keepends=True)[scope['instrumented_line'] - 1] == OPTION
        assert scope['owner_scope_approval_comment'] in OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENTS
        assert scope['retained_owner_approved_scope']
    assert marked.splitlines(keepends=True)[old_checks['omit_scope']['instrumented_line'] - 1] == control_module.OMIT
    new_scope = {
        'declaration': TERMINAL_QUALIFIED, 'short_name': TERMINAL_TARGET,
        'option': 'linter.unusedSectionVars', 'value': False, 'inserted_bytes': 45,
        'candidate_insert_before_line': old_candidate[:old_candidate.index(anchor)].count(b'\n') + 1,
        'terminal61_insert_before_line': old_marked[:old_marked.index(anchor)].count(b'\n') + 1,
        'instrumented_line': marked[:marked.index(OPTION + anchor)].count(b'\n') + 1,
        'follows_before_header_marker': True, 'precedes_original_doccomment': True,
        'single_declaration_scope_verified': True, 'temporary_control_only': True,
        'production_approval': False,
    }
    checks = {
        'marker_count': 61, 'base_marker_count': 61, 'new_marker_count': 0,
        'new_marker_labels': [], 'removed_marker_count': 0, 'removed_marker_labels': [],
        'retained_base_marker_count': 61, 'all_61_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True, 'two_way_reversal_verified': True,
        'full_terminal61_marked_inverse_verified': True,
        'full_warning60_marked_inverse_verified': True,
        'full_61_marker_control_reverse_verified': True,
        'candidate_reverse_to_terminal1ee270_and_cc98_verified': True,
        'marker_removal_recovers_candidate_bytes': True,
        'doccomment_associations_verified': True,
        'all_56_declaration_headers_unchanged': True,
        'all_terminal61_definitions_and_proof_bodies_unchanged': True,
        'public_sum_and_integral_proofs_and_checkpoints_unchanged': True,
        'terminal_sum_header_proof_and_checkpoints_unchanged': True,
        'terminal_integral_full_suffix_unchanged': True,
        'original_imports_and_print_axioms_unchanged': True,
        'new_warning_scope_count': 1, 'warning_scope_count': 4,
        'warning_scopes': [*old_checks['warning_scopes'], new_scope],
        'new_warning_scope': new_scope,
        'warning_line_bytes_per_scope': 45, 'warning_lines_total_bytes': 180,
        'omit_scope_count': 1, 'omit_scope': old_checks['omit_scope'],
        'terminal_sum_warning_uses_default': False,
        'terminal_integral_warning_uses_default': True,
        'public_integral_warning_uses_default': True,
        'no_global_warning_override': True, 'no_alias_or_as_aux_lemma_change': True,
        'base_terminal61_preparation_checks': old_checks,
    }
    return baseline, candidate, marked, manifest, checks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true', help='Run the unchanged frozen 0858 bounded executor')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts, 'Evidence must not be written in .lake'
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    terminal = load_terminal_script(repo / TERMINAL_SCRIPT)
    warning = terminal.load_warning_script(repo / terminal.WARNING_SCRIPT)
    scalar = warning.load_scalar_script(repo / warning.SCALAR_SCRIPT)
    control = scalar.load_control_script(repo / scalar.CONTROL_SCRIPT)
    prior = control.load_prior_script(repo / scalar.PRIOR_SCRIPT)
    marker = prior.load_marker_script(repo / scalar.MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(
        original, marker, prior, control, scalar, warning, terminal)
    script_pins = {
        str(TERMINAL_SCRIPT): TERMINAL_SCRIPT_SHA,
        str(terminal.WARNING_SCRIPT): terminal.WARNING_SCRIPT_SHA,
        str(warning.SCALAR_SCRIPT): warning.SCALAR_SCRIPT_SHA,
        str(scalar.CONTROL_SCRIPT): scalar.CONTROL_SCRIPT_SHA,
        str(scalar.PRIOR_SCRIPT): scalar.PRIOR_SCRIPT_SHA,
        str(scalar.MARKER_SCRIPT): scalar.MARKER_SCRIPT_SHA,
    }
    for name, data in [('ActualGaussFiniteLeaves.original.lean', original),
                       ('ActualGaussFiniteLeaves.terminal-sum-warning-candidate.lean', candidate),
                       ('MomEngineActualDiagCc98c8a2.baseline-marked.lean', baseline),
                       (marker.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    write_json(evidence / 'scope-edit.json', {
        'insert_before': (TERMINAL_DOC + TERMINAL_HEADER).decode(), 'insert': OPTION.decode(),
        'bytes': 45, 'target': TERMINAL_QUALIFIED, 'temporary_control_only': True,
        'production_approval': False,
    })
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Complete terminal61 source plus one temporary terminal-sum unusedSectionVars scope; diagnostic only',
        'owner_prior_warning_scope_approval_comments': OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENTS,
        'owner_prior_warning_scope_approval_declarations': [s['declaration'] for s in checks['warning_scopes'][:-1]],
        'new_warning_scope_production_approval': False,
        'production_approval_flag_meaning': 'This diagnostic grants no production approval. Owner comments 6563548652 and 6563834756 cover only the three retained scopes, not the additional terminal-sum control. Older nested control metadata records its earlier diagnostic state.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'script_pins': script_pins,
        'terminal_script_path': str(TERMINAL_SCRIPT), 'terminal_script_sha256': TERMINAL_SCRIPT_SHA,
        'base_candidate_sha256': BASE_CANDIDATE_SHA, 'base_marked_source_sha256': BASE_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'three retained approved scopes plus one temporary terminal finite-sum scope',
            'declarations': [s['declaration'] for s in checks['warning_scopes']],
            'new_scope_declaration': TERMINAL_QUALIFIED,
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 180, 'new_scopes': 1,
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
        result['new_warning_scope_production_approval'] = False
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'scoped_candidate_sha256', 'diagnostic_source_sha256', 'marker_count',
        'full_terminal61_marked_inverse_verified', 'full_61_marker_control_reverse_verified',
        'warning_option_override', 'terminal_sum_warning_uses_default', 'terminal_integral_warning_uses_default',
        'original_source_unchanged', 'frozen_scripts_unchanged', 'acceptance_evidence',
        'production_approval', 'new_warning_scope_production_approval', 'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
