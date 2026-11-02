import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Finite aggregation of the four actual nonnegative terminal terms -/

noncomputable section
open scoped BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

structure ScalarLedger where
  firstZero : ℝ
  secondZero : ℝ
  exceptional : ℝ
  tail : ℝ
  firstZero_nonneg : 0 ≤ firstZero
  secondZero_nonneg : 0 ≤ secondZero
  exceptional_nonneg : 0 ≤ exceptional
  tail_nonneg : 0 ≤ tail

namespace ScalarLedger

def total (s : ScalarLedger) : ℝ :=
  s.firstZero + s.secondZero + s.exceptional + s.tail

theorem total_nonneg (s : ScalarLedger) : 0 ≤ s.total := by
  sorry

def zero : ScalarLedger where
  firstZero := 0
  secondZero := 0
  exceptional := 0
  tail := 0
  firstZero_nonneg := le_rfl
  secondZero_nonneg := le_rfl
  exceptional_nonneg := le_rfl
  tail_nonneg := le_rfl

@[simp] theorem total_zero : zero.total = 0 := by
  sorry

def add (s t : ScalarLedger) : ScalarLedger where
  firstZero := s.firstZero + t.firstZero
  secondZero := s.secondZero + t.secondZero
  exceptional := s.exceptional + t.exceptional
  tail := s.tail + t.tail
  firstZero_nonneg := add_nonneg s.firstZero_nonneg t.firstZero_nonneg
  secondZero_nonneg := add_nonneg s.secondZero_nonneg t.secondZero_nonneg
  exceptional_nonneg := add_nonneg s.exceptional_nonneg t.exceptional_nonneg
  tail_nonneg := add_nonneg s.tail_nonneg t.tail_nonneg

@[simp] theorem total_add (s t : ScalarLedger) : (s.add t).total = s.total + t.total := by
  sorry

def scale (r : ℝ) (hr : 0 ≤ r) (s : ScalarLedger) : ScalarLedger where
  firstZero := r * s.firstZero
  secondZero := r * s.secondZero
  exceptional := r * s.exceptional
  tail := r * s.tail
  firstZero_nonneg := mul_nonneg hr s.firstZero_nonneg
  secondZero_nonneg := mul_nonneg hr s.secondZero_nonneg
  exceptional_nonneg := mul_nonneg hr s.exceptional_nonneg
  tail_nonneg := mul_nonneg hr s.tail_nonneg

@[simp] theorem total_scale (r : ℝ) (hr : 0 ≤ r) (s : ScalarLedger) :
    (scale r hr s).total = r * s.total := by
  sorry

def sum {I : Type*} [Fintype I] (s : I → ScalarLedger) : ScalarLedger where
  firstZero := ∑ i : I, (s i).firstZero
  secondZero := ∑ i : I, (s i).secondZero
  exceptional := ∑ i : I, (s i).exceptional
  tail := ∑ i : I, (s i).tail
  firstZero_nonneg := Finset.sum_nonneg (fun i _ => (s i).firstZero_nonneg)
  secondZero_nonneg := Finset.sum_nonneg (fun i _ => (s i).secondZero_nonneg)
  exceptional_nonneg := Finset.sum_nonneg (fun i _ => (s i).exceptional_nonneg)
  tail_nonneg := Finset.sum_nonneg (fun i _ => (s i).tail_nonneg)

@[simp] theorem total_sum {I : Type*} [Fintype I] (s : I → ScalarLedger) :
    (sum s).total = ∑ i : I, (s i).total := by
  sorry

theorem sum_bound {I : Type*} [Fintype I] (s : I → ScalarLedger)
    (bound : I → ℝ) (h : ∀ i, (s i).total ≤ bound i) :
    (sum s).total ≤ ∑ i : I, bound i := by
  sorry

theorem total_le (s : ScalarLedger) (b₁ b₂ b₃ b₄ : ℝ)
    (h₁ : s.firstZero ≤ b₁) (h₂ : s.secondZero ≤ b₂)
    (h₃ : s.exceptional ≤ b₃) (h₄ : s.tail ≤ b₄) :
    s.total ≤ b₁ + b₂ + b₃ + b₄ := by
  sorry

end ScalarLedger
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.ScalarLedger.total_sum
#print axioms HeckeSkeleton.Moments.EngineStepV2.ScalarLedger.sum_bound
