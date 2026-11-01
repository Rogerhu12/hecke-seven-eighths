#!/usr/bin/env python3
"""Bounded full-source public-sum as_aux_lemma comparison; diagnostic only.

The frozen scalar60 preparer and 0858 executor are reused unchanged. Only
the current seven-line public sum proof is wrapped. All sixty marker lines
remain byte-identical and in order. PUBLIC_SUM_AFTER_EXACT now observes the
return of the entire as_aux_lemma tactic, including closure/addDecl, rather
than a separate return from its inner exact. The two existing owner-approved
warning scopes remain unchanged; the public sum and integral use defaults.
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
SCALAR_SCRIPT = Path('.github/scripts/mom-engine-step-a2-scalar-sum-diagnostic.py')
SCALAR_SHA = 'a9354aea9c276159ecdcee82761fa33c39d48baba2924118bb419e6786a4de09'
BASE_CANDIDATE_SHA = '505ee96c29c7171932828d3dc3000eb6253ded15e726422fd89067df2445dc5f'
BASE_MARKED_SHA = '34f437b0532881d27cfd0eb07fa2f6450ce70e3cb524193876e6b16f006bef73'
CANDIDATE_SHA = '89fb89ef0da395713ad988fbf2f2ba35ec6dba8690f767be21d974dcb1416f1c'
CANDIDATE_BLOB = '1d0e5fa3b1ab189716a910e629a05d9d206f326f'
MARKED_SHA = 'b4ff49906f0c16572741fbdea9b56e69e6a1d2302aa68fe8c2bbb05ec6a3ec02'
MARKED_BLOB = '68f88657dc4f08dec54c6a5c86b8b1fcdb3f3158'
OWNER_WARNING_SCOPE_APPROVAL_COMMENT = 6563548652
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


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def load_frozen(repo: Path):
    path = repo / SCALAR_SCRIPT
    assert sha(path.read_bytes()) == SCALAR_SHA
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('a2_frozen_scalar60_prepare', path)
    assert spec is not None and spec.loader is not None
    scalar = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scalar)
    assert scalar.FALSE_FLAGS == FALSE_FLAGS
    assert scalar.CANDIDATE_SHA == BASE_CANDIDATE_SHA
    assert scalar.EXPECTED_MARKED_SHA == BASE_MARKED_SHA
    control = scalar.load_control_script(repo / scalar.CONTROL_SCRIPT)
    prior = control.load_prior_script(repo / scalar.PRIOR_SCRIPT)
    marker = prior.load_marker_script(repo / scalar.MARKER_SCRIPT)
    return scalar, control, prior, marker


def guard_snapshot(scalar, control, prior, marker):
    return (marker.EXPECTED_SOURCE, marker.EXPECTED_BYTES,
            marker.TIMEOUT_SECONDS, marker.KILL_AFTER_SECONDS,
            marker.MODULE, marker.PREFIX,
            json.dumps(marker.ACCEPTANCE, sort_keys=True),
            scalar.CANDIDATE_SHA, scalar.EXPECTED_MARKED_SHA,
            control.CANDIDATE_SHA, control.EXPECTED_MARKED_SHA,
            prior.MARKER_SCRIPT_SHA)


def prepare(original: bytes, scalar, control, prior, marker):
    """Pure: baseline59, old505, old60, candidate89fb, marked60, manifest, checks."""
    guards = guard_snapshot(scalar, control, prior, marker)
    assert guards[:4] == (SOURCE_SHA, 40282, 150, 10)
    baseline, old_candidate, old_marked, old_manifest, old_checks = scalar.prepare(
        original, marker, prior, control)
    assert guard_snapshot(scalar, control, prior, marker) == guards
    assert len(old_candidate) == 40382 and sha(old_candidate) == BASE_CANDIDATE_SHA
    assert len(old_marked) == 45757 and sha(old_marked) == BASE_MARKED_SHA
    assert len(old_manifest) == 60
    old_proof = scalar.EDITS['new_public_sum_proof'].encode()
    assert old_proof.count(b'\n') == 7
    assert old_candidate.count(old_proof) == old_marked.count(old_proof) == 1
    new_proof = b'  as_aux_lemma =>\n' + b''.join(
        b'  ' + line for line in old_proof.splitlines(keepends=True))
    assert len(new_proof) - len(old_proof) == 32
    candidate = old_candidate.replace(old_proof, new_proof, 1)
    marked = old_marked.replace(old_proof, new_proof, 1)
    assert len(candidate) == 40414 and sha(candidate) == CANDIDATE_SHA
    assert blob(candidate) == CANDIDATE_BLOB
    assert len(marked) == 45789 and sha(marked) == MARKED_SHA
    assert blob(marked) == MARKED_BLOB
    assert candidate.replace(new_proof, old_proof, 1) == old_candidate
    assert marked.replace(new_proof, old_proof, 1) == old_marked

    entries = {entry['label']: entry for entry in old_manifest}
    before = entries['PUBLIC_SUM_BEFORE_EXACT']['inserted_line'].encode()
    after = entries['PUBLIC_SUM_AFTER_EXACT']['inserted_line'].encode()
    assert marked.count(before + new_proof + after) == 1
    assert before.startswith(b'  run_tac ') and after.startswith(b'  run_tac ')
    assert candidate.count(b'as_aux_lemma') == marked.count(b'as_aux_lemma') == 1
    assert candidate.count(control.OPTION) == marked.count(control.OPTION) == 2
    assert candidate.count(control.OMIT) == marked.count(control.OMIT) == 1

    manifest = []
    for entry in old_manifest:
        line = entry['inserted_line'].encode()
        assert marked.count(line) == 1
        updated = dict(entry)
        updated['scalar_60_instrumented_line'] = entry['instrumented_line']
        updated['instrumented_line'] = marked[:marked.index(line)].count(b'\n') + 1
        if entry['label'] == 'PUBLIC_SUM_AFTER_EXACT':
            updated['as_aux_boundary_note'] = (
                'Entire as_aux_lemma returned, including closure/addDecl; '
                'this is not a separate inner-exact event.')
        manifest.append(updated)
    assert [entry['label'] for entry in manifest] == [entry['label'] for entry in old_manifest]
    assert [entry['instrumented_line'] for entry in manifest] == sorted(
        entry['instrumented_line'] for entry in manifest)
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == 60
    assert sum(marker.PREFIX.encode() in line for line in marked.splitlines()) == 60
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] ==
               entry['inserted_line'].encode() for entry in manifest)
    clean = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert clean == candidate

    # Independently recover the frozen c4 control and then cc98, after undoing
    # only this new wrapper. No old module is modified to accept a new source.
    edits = {key: value.encode() for key, value in scalar.EDITS.items()}
    recovered = clean.replace(new_proof, old_proof, 1)
    recovered = recovered.replace(edits['scalar_helper'], b'', 1)
    recovered = recovered.replace(edits['new_public_sum_proof'], edits['old_public_sum_proof'], 1)
    recovered = recovered.replace(edits['restore_private_before'],
        edits['removed_private_declaration'] + edits['restore_private_before'], 1)
    assert sha(recovered) == scalar.CONTROL_CANDIDATE_SHA and len(recovered) == 40441
    for prefix, anchor in [
            (control.OMIT, control.PHASE_HEADER),
            (control.OPTION, control.PROVIDER_HEADER),
            (control.OPTION, control.PUBLIC_DOC + control.PUBLIC_HEADER)]:
        assert recovered.count(prefix + anchor) == 1
        recovered = recovered.replace(prefix + anchor, anchor, 1)
        assert marked.count(prefix + anchor) == 1
    assert recovered == original
    suffix = b'private theorem leaf_firstPhaseCost_integrable_of_firstKernel\n'
    assert candidate[candidate.index(suffix):] == old_candidate[old_candidate.index(suffix):]
    assert marked[marked.index(suffix):] == old_marked[old_marked.index(suffix):]
    for prefix in [b'import ', b'#print axioms ']:
        assert [line for line in candidate.splitlines() if line.startswith(prefix)] == \
            [line for line in original.splitlines() if line.startswith(prefix)]
    assert guard_snapshot(scalar, control, prior, marker) == guards
    checks = {
        'marker_count': 60, 'previous_marker_count': 60,
        'all_previous_marker_lines_and_order_preserved': True,
        'added_marker_count': 0, 'removed_marker_count': 0,
        'only_public_sum_proof_wrapped': True, 'proof_delta_bytes': 32,
        'public_sum_before_marker_outside_aux': True,
        'public_sum_after_marker_outside_aux': True,
        'public_sum_after_marker_meaning': 'Entire as_aux_lemma returned, not a separate inner-exact event',
        'marker_removal_recovers_candidate': True,
        'candidate_and_marked_reverse_to_previous_exact': True,
        'candidate_reverse_to_c4_and_cc98_exact': True,
        'two_way_reversal_verified': True, 'module_guards_unchanged': True,
        'public_headers_and_all_data_unchanged': True,
        'integral_and_terminal_full_suffix_unchanged': True,
        'warning_scope_count': 2, 'new_warning_scope_count': 0,
        'warning_scopes': old_checks['warning_scopes'],
        'omit_scope_count': 1, 'omit_scope': old_checks['omit_scope'],
        'public_sum_linter_default': True, 'public_integral_linter_default': True,
        'baseline_scalar_preparation_checks': old_checks,
    }
    return baseline, old_candidate, old_marked, candidate, marked, manifest, checks


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
    scalar, control, prior, marker = load_frozen(repo)
    guards = guard_snapshot(scalar, control, prior, marker)
    baseline, old_candidate, old_marked, candidate, marked, manifest, checks = prepare(
        original, scalar, control, prior, marker)
    for name, data in [
        ('ActualGaussFiniteLeaves.original.lean', original),
        ('ActualGaussFiniteLeaves.previous-505-candidate.lean', old_candidate),
        ('ActualGaussFiniteLeaves.public-sum-aux-candidate.lean', candidate),
        ('previous-scalar60.lean', old_marked),
        ('baseline59.lean', baseline), (marker.MODULE + '.lean', marked)]:
        (evidence / name).write_bytes(data)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Full temporary public-sum auxiliary proof comparison with the same sixty markers; diagnostic only',
        'owner_warning_scope_approval_comment': OWNER_WARNING_SCOPE_APPROVAL_COMMENT,
        'production_approval_flag_meaning': 'This diagnostic grants no production approval; two retained scopes have separate owner approval.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'scalar_script_path': str(SCALAR_SCRIPT), 'scalar_script_sha256': SCALAR_SHA,
        'previous_candidate_sha256': sha(old_candidate), 'previous_marked_sha256': sha(old_marked),
        'candidate_sha256': sha(candidate), 'candidate_bytes': len(candidate),
        'candidate_git_blob': blob(candidate),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'diagnostic_source_git_blob': blob(marked),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False, 'global_warning_option_override': None,
        'warning_option_override': {'option': 'linter.unusedSectionVars', 'value': False,
            'scope': 'unchanged two owner-approved provider/public-phase declarations',
            'declarations': control.WARNING_TARGETS, 'new_scopes': 0},
        'other_warning_option_override': None,
        'timeout_seconds': 150, 'kill_after_seconds': 10, 'lean_job_count': 2,
        'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2'
            assert guard_snapshot(scalar, control, prior, marker) == guards
            marker.execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        result['scalar_script_unchanged'] = sha((repo / SCALAR_SCRIPT).read_bytes()) == SCALAR_SHA
        result['control_script_unchanged'] = sha((repo / scalar.CONTROL_SCRIPT).read_bytes()) == scalar.CONTROL_SCRIPT_SHA
        result['prior_script_unchanged'] = sha((repo / scalar.PRIOR_SCRIPT).read_bytes()) == scalar.PRIOR_SCRIPT_SHA
        result['marker_script_unchanged'] = sha((repo / scalar.MARKER_SCRIPT).read_bytes()) == scalar.MARKER_SCRIPT_SHA
        result['module_guards_unchanged'] = guard_snapshot(scalar, control, prior, marker) == guards
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'candidate_sha256', 'diagnostic_source_sha256',
        'marker_count', 'two_way_reversal_verified', 'new_warning_scope_count',
        'original_source_unchanged', 'module_guards_unchanged', 'acceptance_evidence',
        'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
