#!/usr/bin/env python3
"""One-scope warning control for the frozen full-source 60-marker scalar diagnostic.

The pinned scalar wrapper prepares the complete cc98/505ee source and all
60 markers. This control inserts exactly one 45-byte declaration-local
unusedSectionVars option before coverHybridPhaseNonzeroCost_eq_leaf_sum's
original doccomment. The two earlier owner-approved scopes stay unchanged;
this additional scope is temporary diagnostic evidence, with no production
approval. The integral and terminal declarations retain their default warning
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
SCALAR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-scalar-sum-diagnostic.py')
SCALAR_SCRIPT_SHA = 'a9354aea9c276159ecdcee82761fa33c39d48baba2924118bb419e6786a4de09'
SCALAR_CANDIDATE_SHA = '505ee96c29c7171932828d3dc3000eb6253ded15e726422fd89067df2445dc5f'
SCALAR_MARKED_SHA = '34f437b0532881d27cfd0eb07fa2f6450ce70e3cb524193876e6b16f006bef73'
CANDIDATE_SHA = '03c62f89a35b052776f8a039ea61a9830a25b692a4f438bc61ffdc373c2dbf6d'
CANDIDATE_BLOB = '5a41175e7a1a57b30b516afd96ed9da64c8c58bf'
EXPECTED_MARKED_SHA = 'c66540e7b40de0615ffdfed539620c07af0f53e76e496c52f63383a95ca117c3'
EXPECTED_MARKED_BLOB = 'd6c9dfaf08a14c9228d04e232432ab746be5815b'
PUBLIC_TARGET = 'coverHybridPhaseNonzeroCost_eq_leaf_sum'
PUBLIC_QUALIFIED = 'HeckeSkeleton.Moments.EngineStep.ActualGaussStage.' + PUBLIC_TARGET
PUBLIC_DOC = b'/-- Exact finite flattening of the covered source, at the first\ncontinuous Fourier parameter. -/\n'
PUBLIC_HEADER = b'theorem coverHybridPhaseNonzeroCost_eq_leaf_sum\n'
OPTION = b'set_option linter.unusedSectionVars false in\n'
OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENT = 6563548652
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


def load_scalar_script(path: Path):
    assert sha(path.read_bytes()) == SCALAR_SCRIPT_SHA, 'Frozen scalar 60-marker wrapper changed'
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_scalar60_warning_control_base', path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    assert module.SOURCE == SOURCE and module.SOURCE_SHA == SOURCE_SHA
    assert module.SOURCE_BYTES == SOURCE_BYTES and module.CANDIDATE_SHA == SCALAR_CANDIDATE_SHA
    assert module.EXPECTED_MARKED_SHA == SCALAR_MARKED_SHA
    assert module.FALSE_FLAGS == FALSE_FLAGS
    assert module.OWNER_WARNING_SCOPE_APPROVAL_COMMENT == OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENT
    return module


def prepare(original: bytes, marker_module, prior_module, control_module, scalar_module):
    """Pure preparation: baseline59, new candidate, new marked60, manifest, checks.

    The only source mutation relative to frozen scalar60 is the one OPTION.
    Removing it recovers both pinned scalar60 byte streams; their complete
    prior inverse chain is rechecked by scalar_module.prepare on every call.
    """
    assert len(original) == SOURCE_BYTES and sha(original) == SOURCE_SHA
    assert marker_module.TIMEOUT_SECONDS == 150 and marker_module.KILL_AFTER_SECONDS == 10
    assert marker_module.EXPECTED_SOURCE == SOURCE_SHA and marker_module.EXPECTED_BYTES == SOURCE_BYTES
    assert marker_module.MODULE == 'MomEngineActualDiagCc98c8a2'
    assert scalar_module.CANDIDATE_SHA == SCALAR_CANDIDATE_SHA
    assert scalar_module.EXPECTED_MARKED_SHA == SCALAR_MARKED_SHA
    baseline, old_candidate, old_marked, old_manifest, old_checks = scalar_module.prepare(
        original, marker_module, prior_module, control_module)
    assert len(old_candidate) == 40382 and sha(old_candidate) == SCALAR_CANDIDATE_SHA
    assert len(old_marked) == 45757 and sha(old_marked) == SCALAR_MARKED_SHA
    assert len(old_manifest) == old_checks['marker_count'] == 60
    assert old_checks['warning_scope_count'] == 2 and old_checks['new_warning_scope_count'] == 0
    assert old_checks['full_61_marker_control_reverse_verified']
    assert old_checks['candidate_reverse_to_control_and_cc98_verified']
    anchor = PUBLIC_DOC + PUBLIC_HEADER
    assert len(OPTION) == 45
    assert old_candidate.count(anchor) == old_marked.count(anchor) == 1
    assert OPTION + anchor not in old_candidate and OPTION + anchor not in old_marked
    before = ('run_cmd IO.eprintln "A2_ACTUAL_CC98_DIAGNOSTIC BEFORE_HEADER_' + PUBLIC_TARGET + '"\n').encode()
    assert before + anchor in old_marked
    candidate = old_candidate.replace(anchor, OPTION + anchor, 1)
    marked = old_marked.replace(anchor, OPTION + anchor, 1)
    assert len(candidate) == 40427 and sha(candidate) == CANDIDATE_SHA
    assert git_blob(candidate) == CANDIDATE_BLOB
    assert len(marked) == 45802 and sha(marked) == EXPECTED_MARKED_SHA
    assert git_blob(marked) == EXPECTED_MARKED_BLOB
    assert candidate.replace(OPTION + anchor, anchor, 1) == old_candidate
    assert marked.replace(OPTION + anchor, anchor, 1) == old_marked
    assert before + OPTION + anchor in marked
    assert candidate.count(OPTION) == marked.count(OPTION) == 3
    assert candidate.count(control_module.OMIT) == marked.count(control_module.OMIT) == 1

    marker_lines = {m['inserted_line'].encode() for m in old_manifest}
    assert len(marker_lines) == 60
    assert all(marked.count(line) == 1 for line in marker_lines)
    unmarked = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert unmarked == candidate
    assert unmarked.replace(OPTION + anchor, anchor, 1) == old_candidate
    assert [line for line in marked.splitlines(keepends=True) if line in marker_lines] == [
        line for line in old_marked.splitlines(keepends=True) if line in marker_lines]

    # Independently finish the source inverse through the original cc98 file.
    edits = {k: v.encode() for k, v in scalar_module.EDITS.items()}
    inverse = unmarked.replace(OPTION + anchor, anchor, 1)
    assert inverse.count(edits['scalar_helper']) == inverse.count(edits['new_public_sum_proof']) == 1
    inverse = inverse.replace(edits['scalar_helper'], b'', 1)
    inverse = inverse.replace(edits['new_public_sum_proof'], edits['old_public_sum_proof'], 1)
    assert inverse.count(edits['restore_private_before']) == 1
    inverse = inverse.replace(edits['restore_private_before'],
                              edits['removed_private_declaration'] + edits['restore_private_before'], 1)
    for prefix, scope_anchor in [
            (control_module.OMIT, control_module.PHASE_HEADER),
            (OPTION, control_module.PROVIDER_HEADER),
            (OPTION, control_module.PUBLIC_DOC + control_module.PUBLIC_HEADER)]:
        assert inverse.count(prefix + scope_anchor) == 1
        inverse = inverse.replace(prefix + scope_anchor, scope_anchor, 1)
    assert inverse == original

    # The option sits outside the original doccomment/header and all proof text.
    declaration = re.compile(rb'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:theorem|def|abbrev|instance)\s+([^\s:{(]+)')
    def headers(data: bytes):
        return [(m.group(1), data[m.start():data.index(b':=', m.start())])
                for m in declaration.finditer(data)]
    assert headers(candidate) == headers(old_candidate)
    assert len(headers(candidate)) == 55
    suffix = b'private theorem leaf_firstPhaseCost_integrable_of_firstKernel\n'
    assert candidate[candidate.index(suffix):] == old_candidate[old_candidate.index(suffix):]
    assert marked[marked.index(suffix):] == old_marked[old_marked.index(suffix):]
    assert candidate[candidate.index(suffix):] == original[original.index(suffix):]
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in candidate.splitlines() if line.startswith(prefix)] == [
            line for line in original.splitlines() if line.startswith(prefix)]

    manifest = []
    for entry in old_manifest:
        updated = dict(entry)
        line = entry['inserted_line'].encode()
        updated['scalar60_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        updated['added_in_warning_control'] = False
        manifest.append(updated)
    assert [m['label'] for m in manifest] == [m['label'] for m in old_manifest]
    assert all(marked.splitlines(keepends=True)[m['instrumented_line'] - 1] == m['inserted_line'].encode()
               for m in manifest)
    # Existing warning/omit scopes precede the added one and keep their positions.
    for scope in old_checks['warning_scopes']:
        assert marked.splitlines(keepends=True)[scope['instrumented_line'] - 1] == OPTION
    assert marked.splitlines(keepends=True)[old_checks['omit_scope']['instrumented_line'] - 1] == control_module.OMIT
    new_scope = {
        'declaration': PUBLIC_QUALIFIED, 'short_name': PUBLIC_TARGET,
        'option': 'linter.unusedSectionVars', 'value': False, 'inserted_bytes': 45,
        'candidate_insert_before_line': old_candidate[:old_candidate.index(anchor)].count(b'\n') + 1,
        'scalar60_insert_before_line': old_marked[:old_marked.index(anchor)].count(b'\n') + 1,
        'instrumented_line': marked[:marked.index(OPTION + anchor)].count(b'\n') + 1,
        'follows_before_header_marker': True, 'precedes_original_doccomment': True,
        'single_declaration_scope_verified': True, 'temporary_control_only': True,
        'production_approval': False,
    }
    checks = {
        'marker_count': 60, 'control_marker_count': 60, 'new_marker_count': 0,
        'new_marker_labels': [], 'removed_marker_count': 0, 'removed_marker_labels': [],
        'retained_control_marker_count': 60, 'all_60_marker_bytes_and_order_preserved': True,
        'byte_reversal_verified': True, 'two_way_reversal_verified': True,
        'full_60_marker_scalar_reverse_verified': True,
        'full_61_marker_control_reverse_verified': True,
        'candidate_reverse_to_scalar_and_cc98_verified': True,
        'marker_removal_recovers_candidate_bytes': True,
        'doccomment_associations_verified': True,
        'all_55_declaration_headers_unchanged': True,
        'all_scalar60_definitions_and_proof_bodies_unchanged': True,
        'integral_and_terminal_full_suffix_unchanged': True,
        'original_imports_and_print_axioms_unchanged': True,
        'new_warning_scope_count': 1, 'warning_scope_count': 3,
        'warning_scopes': [*old_checks['warning_scopes'], new_scope],
        'new_warning_scope': new_scope,
        'warning_line_bytes_per_scope': 45, 'warning_lines_total_bytes': 135,
        'omit_scope_count': 1, 'omit_scope': old_checks['omit_scope'],
        'phase_warning_uses_default': True, 'integral_warning_uses_default': True,
        'terminal_warnings_use_default': True, 'no_global_warning_override': True,
        'no_alias_or_as_aux_lemma_change': True,
        'baseline_scalar60_preparation_checks': old_checks,
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
    scalar_module = load_scalar_script(repo / SCALAR_SCRIPT)
    control_module = scalar_module.load_control_script(repo / scalar_module.CONTROL_SCRIPT)
    prior_module = control_module.load_prior_script(repo / scalar_module.PRIOR_SCRIPT)
    marker_module = prior_module.load_marker_script(repo / scalar_module.MARKER_SCRIPT)
    baseline, candidate, marked, manifest, checks = prepare(
        original, marker_module, prior_module, control_module, scalar_module)
    script_pins = {
        str(SCALAR_SCRIPT): SCALAR_SCRIPT_SHA,
        str(scalar_module.CONTROL_SCRIPT): scalar_module.CONTROL_SCRIPT_SHA,
        str(scalar_module.PRIOR_SCRIPT): scalar_module.PRIOR_SCRIPT_SHA,
        str(scalar_module.MARKER_SCRIPT): scalar_module.MARKER_SCRIPT_SHA,
    }
    (evidence / 'ActualGaussFiniteLeaves.original.lean').write_bytes(original)
    (evidence / 'ActualGaussFiniteLeaves.scalar-sum-warning-candidate.lean').write_bytes(candidate)
    (evidence / 'MomEngineActualDiagCc98c8a2.baseline-marked.lean').write_bytes(baseline)
    (evidence / (marker_module.MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    write_json(evidence / 'scope-edit.json', {
        'insert_before': (PUBLIC_DOC + PUBLIC_HEADER).decode(), 'insert': OPTION.decode(),
        'bytes': 45, 'target': PUBLIC_QUALIFIED, 'temporary_control_only': True,
        'production_approval': False,
    })
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Complete scalar60 source plus one temporary public-sum unusedSectionVars scope; diagnostic only',
        'owner_prior_warning_scope_approval_comment': OWNER_PRIOR_WARNING_SCOPE_APPROVAL_COMMENT,
        'owner_prior_warning_scope_approval_declarations': control_module.WARNING_TARGETS,
        'new_warning_scope_production_approval': False,
        'production_approval_flag_meaning': 'This diagnostic grants no production approval. Owner comment 6563548652 covers only the two retained scopes, not the additional public-sum control.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'script_pins': script_pins,
        'scalar_script_path': str(SCALAR_SCRIPT), 'scalar_script_sha256': SCALAR_SCRIPT_SHA,
        'scalar_candidate_sha256': SCALAR_CANDIDATE_SHA, 'scalar_marked_source_sha256': SCALAR_MARKED_SHA,
        'baseline_marked_source_sha256': sha(baseline), 'baseline_marked_source_bytes': len(baseline),
        'scoped_candidate_sha256': sha(candidate), 'scoped_candidate_bytes': len(candidate),
        'scoped_candidate_git_blob': git_blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': git_blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {
            'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'two retained approved scopes plus one temporary public finite-sum scope',
            'declarations': [*control_module.WARNING_TARGETS, PUBLIC_QUALIFIED],
            'new_scope_declaration': PUBLIC_QUALIFIED,
            'inserted_bytes_per_declaration': 45, 'total_inserted_bytes': 135, 'new_scopes': 1,
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
            marker_module.execute(repo, evidence, marked, result)
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
        'full_60_marker_scalar_reverse_verified', 'full_61_marker_control_reverse_verified',
        'warning_option_override', 'integral_warning_uses_default', 'original_source_unchanged',
        'frozen_scripts_unchanged', 'acceptance_evidence', 'production_approval',
        'new_warning_scope_production_approval', 'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
