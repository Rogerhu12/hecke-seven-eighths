#!/usr/bin/env python3
"""Complete default-setting Pool65fb candidate diagnostic from candidate abbe.

This standalone file copies the validated D266a execute lifecycle statically.
It imports no diagnostic wrapper and rebinds no imported guard. Full original
candidate source, including every declaration, data definition, proof, import and axiom
print, is recoverable exactly by deleting marker lines. Normal options remain
unchanged; this bounded temporary module is not native/fresh acceptance.
The owner will select whether to publish it; its existence proves no hotspot.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time

EXPECTED_SOURCE = '65fbf1b00c8f754277ee04dafb60296549fd630cc6dfa5d1445309ce91718ca1'
EXPECTED_BYTES = 13433
EXPECTED_LINES = 242
EXPECTED_LEAN = '4.35.0-rc3'
EXPECTED_LEAN_COMMIT = '470d5ce1400764999581fd26d5d72b00d990b0f4'
EXPECTED_MATHLIB = '0493595ecd5da8ef14742febab99728f98e948e8'
SOURCE_CANDIDATE_HEAD = 'abbe08285275bed30d830476110c3739e8b5f8b5'
SOURCE_CANDIDATE_TREE = 'cc199f73b722a985646d4a373ba67671a4b37a7c'
SOURCE_BLOB = '5da0042fa780c5096721757b7a2a31173578cc86'
PREFIX = 'A2_OWNER_POOL_DIAGNOSTIC'
MODULE = 'MomEnginePoolFiniteLeavesDiag65fbf1b0'
TIMEOUT_SECONDS = 150
KILL_AFTER_SECONDS = 10
EXECUTOR_BASE_SCRIPT_SHA256 = '266a512fec83c659fc03186e46980eca1a698e22c8b8bd9fc36ec0032592f48a'
EXECUTOR_BASE_FUNCTION_SHA256 = '61b9e442c9712943c93ffbc4652e7cb08bf4b78279cc749d8394893a3f5ae4ef'
EXECUTOR_ADAPTED_FUNCTION_SHA256 = '2bfa19431e6992be0c5d4714d5b11d48abc504ffa13b2662455cdc40e57c6797'
EXECUTOR_ADAPTATIONS = [("for name in ['OrdinaryExceptionalLabelIntegral', 'ConstantCommonLeaf']:",
  "for name in ['PoolCoverHybridStage', 'ActualGaussFiniteLeaves']:"),
 ("prefix='a2-d-literal-f499-diagnostic-'", "prefix='a2-pool-candidate-65fb-diagnostic-'")]
EXECUTOR_ORIGIN_0858_SCRIPT_SHA256 = '0858bc9e93b1ba60a6d45ae39e694149001689fa29bfd1928ffcaa9696e95ed3'
EXPECTED_MARKED_SHA256 = '6950559e2cbb0665259b7e3251fad000d5978c8c5934a67e8b72c324de0e8139'
EXPECTED_MARKED_BYTES = 18167
EXPECTED_MARKER_COUNT = 60
DECLARATIONS = [('pool_sum_sigma_fintype', 24, 24, 31),
 ('scalar_pool_terminal_sum', 32, 32, 57),
 ('CoveredLeafKey', 91, 89, 96),
 ('coveredLeafKeyFintype', 97, 97, 104),
 ('coveredLeaf', 107, 107, 128),
 ('coveredLeaf_firstKernel', 129, 129, 133),
 ('zeroBudget', 139, 139, 146),
 ('tailBudget', 147, 147, 154),
 ('phase_cost_eq_budgets_leaves', 157, 155, 207),
 ('integral_phase_cost_eq_budgets_leaves', 210, 208, 235)]
EXPECTED_IMPORTS = ['import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolCoverHybridStage\n',
 'import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves\n']
EXPECTED_PRINTS = ['#print axioms '
 'HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.phase_cost_eq_budgets_leaves\n',
 '#print axioms '
 'HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.integral_phase_cost_eq_budgets_leaves\n']
INSERTIONS = [(3, 80, 'command', 0, 'AFTER_ORIGINAL_IMPORTS'),
 (24, 90, 'command', 0, 'BEFORE_HEADER_pool_sum_sigma_fintype'),
 (31, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_pool_sum_sigma_fintype'),
 (32, 90, 'command', 0, 'BEFORE_HEADER_scalar_pool_terminal_sum'),
 (54, 50, 'tactic', 2, 'GENERIC_SUM_BEFORE_SIMP_ONLY'),
 (56, 10, 'tactic', 2, 'GENERIC_SUM_AFTER_SIMP_ONLY'),
 (56, 50, 'tactic', 2, 'GENERIC_SUM_BEFORE_RING'),
 (57, 10, 'tactic', 2, 'GENERIC_SUM_AFTER_RING'),
 (57, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_scalar_pool_terminal_sum'),
 (89, 90, 'command', 0, 'BEFORE_HEADER_CoveredLeafKey'),
 (96, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_CoveredLeafKey'),
 (97, 90, 'command', 0, 'BEFORE_HEADER_coveredLeafKeyFintype'),
 (104, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_coveredLeafKeyFintype'),
 (106, 80, 'command', 0, 'AFTER_FINTYPE_CACHE_LOCAL_INSTANCE'),
 (107, 90, 'command', 0, 'BEFORE_HEADER_coveredLeaf'),
 (128, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_coveredLeaf'),
 (129, 90, 'command', 0, 'BEFORE_HEADER_coveredLeaf_firstKernel'),
 (132, 50, 'tactic', 2, 'FIRST_KERNEL_BEFORE_RCASES'),
 (133, 10, 'tactic', 2, 'FIRST_KERNEL_AFTER_RCASES'),
 (133, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_coveredLeaf_firstKernel'),
 (139, 90, 'command', 0, 'BEFORE_HEADER_zeroBudget'),
 (146, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_zeroBudget'),
 (147, 90, 'command', 0, 'BEFORE_HEADER_tailBudget'),
 (154, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_tailBudget'),
 (155, 90, 'command', 0, 'BEFORE_HEADER_phase_cost_eq_budgets_leaves'),
 (164, 50, 'tactic', 2, 'SUM_BEFORE_UNFOLD'),
 (165, 10, 'tactic', 2, 'SUM_AFTER_UNFOLD'),
 (165, 50, 'tactic', 2, 'SUM_BEFORE_RW_MAIN'),
 (166, 10, 'tactic', 2, 'SUM_AFTER_RW_MAIN'),
 (166, 50, 'tactic', 2, 'SUM_BEFORE_SIMP_RW'),
 (167, 10, 'tactic', 2, 'SUM_AFTER_SIMP_RW'),
 (167, 50, 'tactic', 2, 'SUM_BEFORE_EXACT'),
 (207, 10, 'tactic', 2, 'SUM_AFTER_EXACT'),
 (207, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_phase_cost_eq_budgets_leaves'),
 (208, 90, 'command', 0, 'BEFORE_HEADER_integral_phase_cost_eq_budgets_leaves'),
 (218, 50, 'tactic', 2, 'INTEGRAL_BEFORE_FINITE_MEASURE'),
 (219, 10, 'tactic', 2, 'INTEGRAL_AFTER_FINITE_MEASURE'),
 (219, 50, 'tactic', 2, 'INTEGRAL_BEFORE_HAVE_INTEGRABLE'),
 (222, 50, 'tactic', 4, 'INTEGRAL_HI_BEFORE_SIMPA'),
 (224, 5, 'tactic', 4, 'INTEGRAL_HI_AFTER_SIMPA'),
 (224, 10, 'tactic', 2, 'INTEGRAL_AFTER_HAVE_INTEGRABLE'),
 (224, 50, 'tactic', 2, 'INTEGRAL_BEFORE_SIMP_RW'),
 (225, 10, 'tactic', 2, 'INTEGRAL_AFTER_SIMP_RW'),
 (225, 50, 'tactic', 2, 'INTEGRAL_BEFORE_INTEGRAL_ADD'),
 (226, 10, 'tactic', 2, 'INTEGRAL_AFTER_INTEGRAL_ADD'),
 (226, 50, 'tactic', 2, 'INTEGRAL_BEFORE_INTEGRAL_CONST_SUM'),
 (227, 10, 'tactic', 2, 'INTEGRAL_AFTER_INTEGRAL_CONST_SUM'),
 (228, 50, 'tactic', 4, 'INTEGRAL_AFTER_SMUL_BEFORE_CONGR'),
 (229, 10, 'tactic', 4, 'INTEGRAL_AFTER_CONGR'),
 (229, 50, 'tactic', 4, 'INTEGRAL_BEFORE_SUM_CONGR'),
 (230, 10, 'tactic', 4, 'INTEGRAL_AFTER_SUM_CONGR'),
 (231, 50, 'tactic', 4, 'INTEGRAL_COST_BEFORE_SIMPA'),
 (233, 5, 'tactic', 4, 'INTEGRAL_COST_AFTER_SIMPA'),
 (234, 50, 'tactic', 4, 'INTEGRAL_SIDE_BEFORE_EXACT'),
 (235, 5, 'tactic', 4, 'INTEGRAL_SIDE_AFTER_EXACT'),
 (235, 10, 'tactic', 2, 'INTEGRAL_AFTER_COMPLETE_PROOF'),
 (235, 80, 'command', 0, 'COMMAND_CONTINUED_AFTER_integral_phase_cost_eq_budgets_leaves'),
 (240, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_160'),
 (241, 80, 'command', 0, 'BEFORE_ORIGINAL_PRINT_161'),
 (243, 99, 'command', 0, 'AFTER_ALL_ORIGINAL_COMMANDS')]
SOURCE = Path('HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolFiniteLeaves.lean')
FALSE_FLAGS = {
    'acceptance_evidence': False, 'original_module_native_was_run': False,
    'original_module_acceptance': False, 'complete_target_module_compiled': False,
    'complete_module_within_five_minutes': False, 'full_task_acceptance': False,
    'compiler_outputs_can_be_restored_as_project_cache': False,
    'production_approval': False, 'candidate_native_validation_performed': False,
    'fresh_axiom_audit_performed': False,
}

BASE_OWNER_HEAD = '16927b5cb39e3034ac86d3af49e39aae17440af4'
BASE_OWNER_TREE = 'caa913a0e45a8bb31db1251a15a69e91732ac921'
BASE_OWNER_SOURCE_SHA256 = '7fafdf5687b18cf53f9e6f4792e999198a0ab875396376690e1c625f0a718c01'
BASE_OWNER_SOURCE_BYTES = 8576
BASE_OWNER_SOURCE_BLOB = '6ca8316f24dd56f09ea9b29262e1dacf78c6dd5b'
SOURCE_EDITS_FROM_OWNER = [{'kind': 'insert_before',
  'anchor': 'variable {K : Type} [Field K] [NumberField K]\n',
  'insert': 'private abbrev pool_sum_sigma_fintype\n'
            '    {P : Type*} {I₀ : Type*}\n'
            '    {I₁ : P → Type*} {I₆ : P → Type*} {I₇ : P → Type*}\n'
            '    [Fintype P] [Fintype I₀]\n'
            '    [∀ p, Fintype (I₁ p)] [∀ p, Fintype (I₆ p)] [∀ p, Fintype (I₇ p)] :\n'
            '    Fintype (I₀ ⊕ ((Σ p, I₁ p) ⊕ ((Σ p, I₆ p) ⊕ (Σ p, I₇ p)))) :=\n'
            '  inferInstance\n'
            '\n'
            'private theorem scalar_pool_terminal_sum\n'
            '    {P : Type*} {I₀ : Type*}\n'
            '    {I₁ : P → Type*} {I₆ : P → Type*} {I₇ : P → Type*}\n'
            '    [Fintype P] [Fintype I₀]\n'
            '    [∀ p, Fintype (I₁ p)] [∀ p, Fintype (I₆ p)] [∀ p, Fintype (I₇ p)]\n'
            '    (a m : ℝ) (w₁ w₆ w₇ : P → ℝ) (z₀ t₀ : ℝ)\n'
            '    (z₁ t₁ z₆ t₆ z₇ t₇ : P → ℝ)\n'
            '    (f₀ : I₀ → ℝ) (f₁ : ∀ p, I₁ p → ℝ)\n'
            '    (f₆ : ∀ p, I₆ p → ℝ) (f₇ : ∀ p, I₇ p → ℝ)\n'
            '    (r : I₀ ⊕ ((Σ p, I₁ p) ⊕ ((Σ p, I₆ p) ⊕ (Σ p, I₇ p))) → ℝ)\n'
            '    (h₀ : ∀ b, r (.inl b) = (a * m) * f₀ b)\n'
            '    (h₁ : ∀ p b, r (.inr (.inl ⟨p, b⟩)) = (a * w₁ p) * f₁ p b)\n'
            '    (h₆ : ∀ p b, r (.inr (.inr (.inl ⟨p, b⟩))) = (a * w₆ p) * f₆ p b)\n'
            '    (h₇ : ∀ p b, r (.inr (.inr (.inr ⟨p, b⟩))) = (a * w₇ p) * f₇ p b) :\n'
            '    a * (m * (z₀ + t₀ + ∑ b, f₀ b) +\n'
            '      (∑ p, w₁ p * (z₁ p + t₁ p + ∑ b, f₁ p b)) +\n'
            '      (∑ p, w₆ p * (z₆ p + t₆ p + ∑ b, f₆ p b)) +\n'
            '      (∑ p, w₇ p * (z₇ p + t₇ p + ∑ b, f₇ p b))) =\n'
            '      a * (m * z₀ + (∑ p, w₁ p * z₁ p) + (∑ p, w₆ p * z₆ p) +\n'
            '        (∑ p, w₇ p * z₇ p)) +\n'
            '      a * (m * t₀ + (∑ p, w₁ p * t₁ p) + (∑ p, w₆ p * t₆ p) +\n'
            '        (∑ p, w₇ p * t₇ p)) + ∑ b, r b := by\n'
            '  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, h₀, h₁, h₆, h₇,\n'
            '    Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc]\n'
            '  ring\n'
            '\n'},
 {'kind': 'insert_before',
  'anchor': 'def coveredLeaf (exceptional : s.CoverHybridPredicates B)\n',
  'insert': 'private abbrev coveredLeafKeyFintype : Fintype (s.CoveredLeafKey B) :=\n'
            '  pool_sum_sigma_fintype\n'
            '    (P := P.primes)\n'
            '    (I₀ := s.main.CoveredLeafKey B.main B.main)\n'
            '    (I₁ := fun p => (s.one p).CoveredLeafKey (B.residual p 1) (B.residual p 1))\n'
            '    (I₆ := fun p => (s.six p).CoveredLeafKey (B.residual p 6) (B.residual p 6))\n'
            '    (I₇ := fun p => (s.seven p).CoveredLeafKey (B.residual p 7) (B.residual p 7))\n'
            '\n'
            'attribute [local instance] coveredLeafKeyFintype\n'
            '\n'},
 {'kind': 'replace_once',
  'old': '  unfold coverHybridPhaseCost\n'
         '  rw [T.main.phase_cost_eq_budgets_leaves B.main B.main exceptional.main F x ξ]\n'
         '  simp_rw [ActualGaussStage.TerminalCalibration.phase_cost_eq_budgets_leaves (F := F)]\n'
         '  simp only [zeroBudget, tailBudget, Fintype.sum_sum_type, Fintype.sum_sigma,\n'
         '    coveredLeaf, ActualHybridLeaf.scale_firstPhaseCost, Finset.sum_add_distrib,\n'
         '    Finset.mul_sum, mul_add, mul_assoc]\n'
         '  ring\n',
  'new': '  unfold coverHybridPhaseCost\n'
         '  rw [T.main.phase_cost_eq_budgets_leaves B.main B.main exceptional.main F x ξ]\n'
         '  simp_rw [ActualGaussStage.TerminalCalibration.phase_cost_eq_budgets_leaves (F := F)]\n'
         '  exact scalar_pool_terminal_sum\n'
         '    (P := P.primes)\n'
         '    (I₀ := s.main.CoveredLeafKey B.main B.main)\n'
         '    (I₁ := fun p => (s.one p).CoveredLeafKey (B.residual p 1) (B.residual p 1))\n'
         '    (I₆ := fun p => (s.six p).CoveredLeafKey (B.residual p 6) (B.residual p 6))\n'
         '    (I₇ := fun p => (s.seven p).CoveredLeafKey (B.residual p 7) (B.residual p 7))\n'
         '    (4 / d.density) d.multiplicity\n'
         '    (fun p => FirstGaussPoolData.localErrorWeight p.val 1)\n'
         '    (fun p => FirstGaussPoolData.localErrorWeight p.val 6)\n'
         '    (fun p => FirstGaussPoolData.localErrorWeight p.val 7)\n'
         '    (T.main.zeroBudget ε Czero) (T.main.tailBudget Cerror)\n'
         '    (fun p => (T.one p).zeroBudget ε Czero) (fun p => (T.one p).tailBudget Cerror)\n'
         '    (fun p => (T.six p).zeroBudget ε Czero) (fun p => (T.six p).tailBudget Cerror)\n'
         '    (fun p => (T.seven p).zeroBudget ε Czero) (fun p => (T.seven p).tailBudget Cerror)\n'
         '    (fun b => (s.main.fiberCoveredLeaf B.main B.main exceptional.main F x '
         'b).firstPhaseCost ξ)\n'
         '    (fun p b => ((s.one p).fiberCoveredLeaf (B.residual p 1) (B.residual p 1)\n'
         '      (exceptional.one p) F (fun i => x i.val) b).firstPhaseCost ξ)\n'
         '    (fun p b => ((s.six p).fiberCoveredLeaf (B.residual p 6) (B.residual p 6)\n'
         '      (exceptional.six p) F (fun i => x i.val) b).firstPhaseCost ξ)\n'
         '    (fun p b => ((s.seven p).fiberCoveredLeaf (B.residual p 7) (B.residual p 7)\n'
         '      (exceptional.seven p) F (fun i => x i.val) b).firstPhaseCost ξ)\n'
         '    (fun b => (s.coveredLeaf B exceptional F x b).firstPhaseCost ξ)\n'
         '    (fun b => (s.main.fiberCoveredLeaf B.main B.main exceptional.main F x '
         'b).scale_firstPhaseCost\n'
         '      ((4 / d.density) * d.multiplicity)\n'
         '      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le) d.multiplicity_nonneg) ξ)\n'
         '    (fun p b => ((s.one p).fiberCoveredLeaf (B.residual p 1) (B.residual p 1)\n'
         '      (exceptional.one p) F (fun i => x i.val) b).scale_firstPhaseCost\n'
         '      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 1)\n'
         '      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)\n'
         '        (FirstGaussPoolData.localErrorWeight_nonneg p.val 1)) ξ)\n'
         '    (fun p b => ((s.six p).fiberCoveredLeaf (B.residual p 6) (B.residual p 6)\n'
         '      (exceptional.six p) F (fun i => x i.val) b).scale_firstPhaseCost\n'
         '      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 6)\n'
         '      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)\n'
         '        (FirstGaussPoolData.localErrorWeight_nonneg p.val 6)) ξ)\n'
         '    (fun p b => ((s.seven p).fiberCoveredLeaf (B.residual p 7) (B.residual p 7)\n'
         '      (exceptional.seven p) F (fun i => x i.val) b).scale_firstPhaseCost\n'
         '      ((4 / d.density) * FirstGaussPoolData.localErrorWeight p.val 7)\n'
         '      (mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)\n'
         '        (FirstGaussPoolData.localErrorWeight_nonneg p.val 7)) ξ)\n'}]
FINTYPE_CACHE_APPROVAL_COMMENT = 6567091453

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def restore_owner_source(candidate: bytes) -> bytes:
    """Reverse exactly the three approved candidate edits; do not change a file."""
    assert len(candidate) == EXPECTED_BYTES and sha(candidate) == EXPECTED_SOURCE
    text = candidate.decode()
    for edit in reversed(SOURCE_EDITS_FROM_OWNER):
        if edit['kind'] == 'insert_before':
            combined = edit['insert'] + edit['anchor']
            assert text.count(combined) == 1
            text = text.replace(combined, edit['anchor'], 1)
        else:
            assert edit['kind'] == 'replace_once' and text.count(edit['new']) == 1
            text = text.replace(edit['new'], edit['old'], 1)
    original = text.encode()
    assert len(original) == BASE_OWNER_SOURCE_BYTES and sha(original) == BASE_OWNER_SOURCE_SHA256
    assert hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest() == BASE_OWNER_SOURCE_BLOB
    for edit in SOURCE_EDITS_FROM_OWNER:
        if edit['kind'] == 'insert_before':
            assert text.count(edit['anchor']) == 1
            text = text.replace(edit['anchor'], edit['insert'] + edit['anchor'], 1)
        else:
            assert text.count(edit['old']) == 1
            text = text.replace(edit['old'], edit['new'], 1)
    assert text.encode() == candidate
    return original


def instrument(original: bytes) -> tuple[bytes, list[dict], dict]:
    """Pure exact whole-source insertion; all original lines survive both inverses."""
    assert len(original) == EXPECTED_BYTES and sha(original) == EXPECTED_SOURCE
    assert hashlib.sha1(b'blob ' + str(len(original)).encode() + b'\0' + original).hexdigest() == SOURCE_BLOB
    assert PREFIX.encode() not in original
    lines = original.splitlines(keepends=True)
    assert len(lines) == EXPECTED_LINES and all(line.endswith(b'\n') for line in lines)
    assert [line.decode() for line in lines if line.startswith(b'import ')] == EXPECTED_IMPORTS
    assert [line.decode() for line in lines if line.startswith(b'#print axioms ')] == EXPECTED_PRINTS
    assert b'set_option ' not in original and b'as_aux_lemma' not in original
    events = []
    for before, priority, kind, indent, label in INSERTIONS:
        assert 1 <= before <= len(lines) + 1
        assert re.fullmatch('[A-Za-z0-9_]+', label)
        assert kind in ('command', 'tactic')
        text = (' ' * indent + ('run_cmd' if kind == 'command' else 'run_tac') +
                ' IO.eprintln "' + PREFIX + ' ' + label + '"\n')
        events.append({'original_insert_before_line': before, 'priority': priority,
                       'kind': kind, 'indent': indent, 'label': label, 'inserted_line': text})
    events.sort(key=lambda e: (e['original_insert_before_line'], e['priority']))
    assert len(events) == EXPECTED_MARKER_COUNT
    assert len({e['label'] for e in events}) == EXPECTED_MARKER_COUNT
    output, manifest = [], []
    for line_no in range(1, len(lines) + 2):
        for event in events:
            if event['original_insert_before_line'] == line_no:
                entry = dict(event)
                entry['instrumented_line'] = len(output) + 1
                output.append(entry['inserted_line'].encode())
                manifest.append(entry)
        if line_no <= len(lines):
            output.append(lines[line_no - 1])
    marked = b''.join(output)
    assert len(marked) == EXPECTED_MARKED_BYTES and sha(marked) == EXPECTED_MARKED_SHA256
    marker_lines = {entry['inserted_line'].encode() for entry in manifest}
    assert len(marker_lines) == EXPECTED_MARKER_COUNT
    assert all(marked.count(line) == 1 for line in marker_lines)
    restored = b''.join(line for line in marked.splitlines(keepends=True) if line not in marker_lines)
    assert restored == original
    reverse = marked
    for entry in reversed(manifest):
        marker = entry['inserted_line'].encode()
        assert reverse.count(marker) == 1
        reverse = reverse.replace(marker, b'', 1)
    assert reverse == original
    assert [line for line in marked.splitlines(keepends=True) if line not in marker_lines] == lines
    assert all(marked.splitlines(keepends=True)[entry['instrumented_line'] - 1] ==
               entry['inserted_line'].encode() for entry in manifest)
    for name, header, start, after in DECLARATIONS:
        assert name.encode() in lines[header - 1]
        assert 1 <= start <= header < after <= len(lines) + 1
        if start != header:
            assert lines[start - 1].startswith(b'/--')
            assert b'-/\n' in b''.join(lines[start - 1:header - 1])
            assert marked.count(b''.join(lines[start - 1:header])) == 1
    for prefix in (b'import ', b'#print axioms '):
        assert [line for line in marked.splitlines(keepends=True) if line.startswith(prefix)] == [
            line for line in lines if line.startswith(prefix)]
    assert b'set_option ' not in marked and b'as_aux_lemma' not in marked
    checks = {
        'marker_count': EXPECTED_MARKER_COUNT, 'declaration_count': len(DECLARATIONS),
        'command_marker_count': sum(e['kind'] == 'command' for e in manifest),
        'tactic_marker_count': sum(e['kind'] == 'tactic' for e in manifest),
        'original_import_count': len(EXPECTED_IMPORTS), 'original_print_axioms_count': len(EXPECTED_PRINTS),
        'byte_reversal_verified': True, 'individual_removal_reversal_verified': True,
        'all_original_lines_preserved_in_order': True, 'doccomment_associations_verified': True,
        'all_original_data_headers_and_proofs_preserved_after_marker_removal': True,
        'new_warning_scope_count': 0, 'warning_scope_count': 0,
        'all_original_linters_default': True, 'proof_transformations_added': 0,
        'original_full_source_sha256': sha(original), 'original_full_source_bytes': len(original),
        'diagnostic_source_sha256': sha(marked), 'diagnostic_source_bytes': len(marked),
        'full_original_module_copy_used': True,
    }
    restored_owner = restore_owner_source(original)
    checks.update(candidate_to_owner_exact_reverse_verified=True, owner_to_candidate_exact_forward_verified=True,
                  base_owner_source_sha256=sha(restored_owner), base_owner_source_bytes=len(restored_owner),
                  candidate_new_private_declaration_count=3, candidate_phase_proof_rewritten=True)
    return marked, manifest, checks


def execute(repo: Path, evidence: Path, marked: bytes, result: dict) -> None:
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True)
    assert EXPECTED_LEAN in version and EXPECTED_LEAN_COMMIT in version, version
    mathlib = subprocess.check_output(['git', '-C', str(repo / '.lake/packages/mathlib'),
                                      'rev-parse', 'HEAD'], text=True).strip()
    assert mathlib == EXPECTED_MATHLIB, mathlib
    for name in ['PoolCoverHybridStage', 'ActualGaussFiniteLeaves']:
        assert (repo / '.lake/build/lib/lean/HeckeSkeleton/Moments/MOM_ENGINE_STEP' /
                (name + '.olean')).is_file(), 'Run normal Lake :deps first: ' + name
    result.update(lean_version=version.strip(), mathlib_commit=mathlib,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
                  source_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo, text=True).strip())
    # The package-root flag only determines the name of this temporary module;
    # the original two imports resolve through the normal `lake env` paths.
    with tempfile.TemporaryDirectory(prefix='a2-pool-candidate-65fb-diagnostic-') as temporary:
        directory = Path(temporary)
        source = directory / (MODULE + '.lean')
        source.write_bytes(marked)
        compiler = directory / 'compiler'
        compiler.mkdir()
        command = ['lake', 'env', 'lean', '-j2', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-DstderrAsMessages=false', '-R', str(directory), '-o', str(compiler / (MODULE + '.olean')),
                   '-i', str(compiler / (MODULE + '.ilean')), str(source)]
        result.update(command=command, temporary_directory=str(directory),
                      compiler_output_directory=str(compiler), started=True)
        write_json(evidence / 'result.json', result)
        start = time.monotonic()
        observations = []
        read_errors = []
        process = subprocess.Popen(command, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        result.update(owned_process_pid=process.pid, owned_process_group=process.pid)

        def reader() -> None:
            pending = b''
            try:
                with (evidence / 'complete-output.log').open('wb') as output:
                    assert process.stdout is not None
                    while chunk := process.stdout.read1(65536):
                        output.write(chunk)
                        output.flush()
                        pending += chunk
                        while b'\n' in pending:
                            line, pending = pending.split(b'\n', 1)
                            decoded = line.decode('utf-8', errors='replace')
                            if PREFIX in decoded:
                                observation = {'elapsed_seconds': time.monotonic() - start, 'line': decoded}
                                observations.append(observation)
                                print(json.dumps(observation, ensure_ascii=False), flush=True)
                                write_json(evidence / 'marker-observations.json', observations)
                    if PREFIX.encode() in pending:
                        observations.append({'elapsed_seconds': time.monotonic() - start,
                                             'line': pending.decode('utf-8', errors='replace')})
            except Exception as exc:
                read_errors.append(repr(exc))

        worker = threading.Thread(target=reader, daemon=True)
        worker.start()

        def own_group(sig: signal.Signals) -> None:
            try:
                os.killpg(process.pid, sig)
                result.setdefault('cleanup_signals', []).append(sig.name)
            except ProcessLookupError:
                pass

        old_handlers = {}

        def interrupted(signum, _frame):
            raise InterruptedError('Diagnostic runner interrupted by signal ' + str(signum))

        for sig in (signal.SIGINT, signal.SIGTERM):
            old_handlers[sig] = signal.signal(sig, interrupted)
        try:
            try:
                code = process.wait(timeout=TIMEOUT_SECONDS)
                result['status'] = 'diagnostic_process_finished'
            except subprocess.TimeoutExpired:
                result.update(status='diagnostic_timeout', timed_out=True)
                own_group(signal.SIGTERM)
                try:
                    code = process.wait(timeout=KILL_AFTER_SECONDS)
                except subprocess.TimeoutExpired:
                    own_group(signal.SIGKILL)
                    code = process.wait(timeout=5)
            result['diagnostic_exit_code'] = code
        finally:
            # Only the session created above is signaled.  No process discovery,
            # attaching, pkill, system setting, or other session is involved.
            own_group(signal.SIGTERM)
            if process.poll() is None:
                try:
                    process.wait(timeout=KILL_AFTER_SECONDS)
                except subprocess.TimeoutExpired:
                    own_group(signal.SIGKILL)
                    process.wait(timeout=5)
            own_group(signal.SIGKILL)  # remove any remaining owned descendants
            worker.join(timeout=2)
            for sig, previous in old_handlers.items():
                signal.signal(sig, previous)
            result.update(elapsed_seconds=time.monotonic() - start,
                          diagnostic_exit_code=process.returncode,
                          output_reader_finished=not worker.is_alive(), output_read_errors=read_errors,
                          observed_markers=observations,
                          last_observed_marker=observations[-1] if observations else None,
                          diagnostic_input_unchanged=sha(source.read_bytes()) == sha(marked))
            write_json(evidence / 'marker-observations.json', observations)
    result['temporary_directory_removed'] = not Path(result['temporary_directory']).exists()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--run', action='store_true', help='Run the bounded diagnostic; default is pure preparation')
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    assert '.lake' not in evidence.parts
    evidence.mkdir(parents=True, exist_ok=True)
    assert not (evidence / 'result.json').exists(), 'Use a fresh evidence directory'
    original = (repo / SOURCE).read_bytes()
    marked, manifest, checks = instrument(original)
    (evidence / 'PoolFiniteLeaves.candidate.lean').write_bytes(original)
    (evidence / 'PoolFiniteLeaves.owner-original.lean').write_bytes(restore_owner_source(original))
    (evidence / (MODULE + '.lean')).write_bytes(marked)
    write_json(evidence / 'marker-manifest.json', manifest)
    result = {
        **FALSE_FLAGS, **checks,
        'scope': 'Temporary full Pool65fb candidate diagnostic on candidate parent abbe; candidate is not accepted owner production or native evidence',
        'production_source_and_proof_owner': 'A2/owner',
        'source_path': str(SOURCE), 'source_sha256': sha(original), 'source_bytes': len(original),
        'source_candidate_head': SOURCE_CANDIDATE_HEAD, 'source_candidate_tree': SOURCE_CANDIDATE_TREE, 'source_git_blob': SOURCE_BLOB,
        'base_owner_head': BASE_OWNER_HEAD, 'base_owner_tree': BASE_OWNER_TREE,
        'base_owner_source_git_blob': BASE_OWNER_SOURCE_BLOB,
        'source_candidate_accepted_by_owner': False,
        'fintype_cache_owner_approval_comment': FINTYPE_CACHE_APPROVAL_COMMENT,
        'diagnostic_script_sha256': sha(Path(__file__).read_bytes()),
        'executor_base_script_sha256': EXECUTOR_BASE_SCRIPT_SHA256,
        'executor_base_function_sha256': EXECUTOR_BASE_FUNCTION_SHA256,
        'executor_adapted_function_sha256': EXECUTOR_ADAPTED_FUNCTION_SHA256,
        'executor_adaptations': EXECUTOR_ADAPTATIONS,
        'external_wrapper_imported_or_rebound': False,
        'production_approval_flag_scope': 'This diagnostic does not grant production approval.',
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'heartbeat_override': None, 'lean_async_override': None, 'profiler_override': None,
        'stderr_option_override': False,
        'stderr_option_reason': 'Diagnostic marker transport only; no linter or normal verifier option changes',
        'warning_option_override': None, 'other_warning_option_override': None,
        'global_warning_option_override': None,
        'timeout_seconds': TIMEOUT_SECONDS, 'kill_after_seconds': KILL_AFTER_SECONDS,
        'lean_job_count': 2, 'started': False, 'status': 'prepared_only', 'timed_out': False,
        'marker_times_are_observed_arrival_only': True,
        'marker_interpretation': 'run_cmd waits for preceding checked environments but can follow compiler error recovery, so it does not alone prove successful checking. run_tac shows tactic return only. Quoted warning echoes are not actual events; inspect the complete log.',
    }
    write_json(evidence / 'result.json', result)
    try:
        if args.run:
            assert os.environ.get('LEAN_NUM_THREADS') == '2', 'Expected normal workflow thread setting'
            execute(repo, evidence, marked, result)
    except BaseException as exc:
        result.update(status='diagnostic_harness_error', harness_error=repr(exc))
        raise
    finally:
        result['original_source_unchanged'] = (repo / SOURCE).read_bytes() == original
        assert result['original_source_unchanged']
        result.update(FALSE_FLAGS)
        write_json(evidence / 'result.json', result)
    print(json.dumps({key: result[key] for key in [
        'status', 'source_sha256', 'diagnostic_source_sha256', 'marker_count',
        'byte_reversal_verified', 'all_original_linters_default', 'original_source_unchanged',
        'acceptance_evidence', 'original_module_acceptance', 'production_approval',
        'fresh_axiom_audit_performed']}, ensure_ascii=False), flush=True)
    if args.run and result.get('timed_out'):
        return 124
    code = result.get('diagnostic_exit_code', 0)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
