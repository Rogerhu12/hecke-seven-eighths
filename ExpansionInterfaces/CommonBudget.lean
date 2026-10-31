import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-!
# One budget and one cutoff pair for a finite family

This is the elementary quantifier-order lemma used by EX-HEIGHT-BUDGET and
EX-CUTOFFS.  It proves no analytic estimate.  It combines independently proved
component estimates, retaining the order `degree, ceiling` before `tau` and
`threshold, constant` after `tau`.  All constituent hypotheses remain explicit.
-/

namespace ExpansionInterfaces

structure HeightBudget where
  degree : ℝ
  ceiling : ℝ
  degree_nonneg : 0 ≤ degree
  ceiling_pos : 0 < ceiling

structure Cutoffs where
  threshold : ℝ
  constant : ℝ
  threshold_two : 2 ≤ threshold
  constant_nonneg : 0 ≤ constant

namespace HeightBudget

def merge (a b : HeightBudget) : HeightBudget where
  degree := max a.degree b.degree
  ceiling := min a.ceiling b.ceiling
  degree_nonneg := a.degree_nonneg.trans (le_max_left _ _)
  ceiling_pos := lt_min a.ceiling_pos b.ceiling_pos

/-- `larger` can be used wherever `smaller` is allowed. -/
def Dominates (larger smaller : HeightBudget) : Prop :=
  smaller.degree ≤ larger.degree ∧ larger.ceiling ≤ smaller.ceiling

theorem merge_dominates_left (a b : HeightBudget) : (merge a b).Dominates a :=
  ⟨le_max_left _ _, min_le_left _ _⟩

theorem merge_dominates_right (a b : HeightBudget) : (merge a b).Dominates b :=
  ⟨le_max_right _ _, min_le_right _ _⟩

theorem Dominates.trans {a b c : HeightBudget}
    (hab : a.Dominates b) (hbc : b.Dominates c) : a.Dominates c :=
  ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩

def joinList : List HeightBudget → HeightBudget
  | [] => ⟨0, 1, le_rfl, zero_lt_one⟩
  | b :: bs => merge b (joinList bs)

theorem joinList_dominates {b : HeightBudget} {bs : List HeightBudget}
    (hb : b ∈ bs) : (joinList bs).Dominates b := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with heq | hmem
    · subst b
      exact merge_dominates_left a (joinList bs)
    · exact (merge_dominates_right a (joinList bs)).trans (ih hmem)

def common {n : ℕ} (budgets : Fin n → HeightBudget) : HeightBudget :=
  joinList (List.ofFn budgets)

theorem common_dominates {n : ℕ} (budgets : Fin n → HeightBudget) (i : Fin n) :
    (common budgets).Dominates (budgets i) := by
  apply joinList_dominates
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

end HeightBudget

namespace Cutoffs

def merge (a b : Cutoffs) : Cutoffs where
  threshold := max a.threshold b.threshold
  constant := max a.constant b.constant
  threshold_two := a.threshold_two.trans (le_max_left _ _)
  constant_nonneg := a.constant_nonneg.trans (le_max_left _ _)

def Dominates (larger smaller : Cutoffs) : Prop :=
  smaller.threshold ≤ larger.threshold ∧ smaller.constant ≤ larger.constant

theorem merge_dominates_left (a b : Cutoffs) : (merge a b).Dominates a :=
  ⟨le_max_left _ _, le_max_left _ _⟩

theorem merge_dominates_right (a b : Cutoffs) : (merge a b).Dominates b :=
  ⟨le_max_right _ _, le_max_right _ _⟩

theorem Dominates.trans {a b c : Cutoffs}
    (hab : a.Dominates b) (hbc : b.Dominates c) : a.Dominates c :=
  ⟨hbc.1.trans hab.1, hbc.2.trans hab.2⟩

def joinList : List Cutoffs → Cutoffs
  | [] => ⟨2, 0, le_rfl, le_rfl⟩
  | b :: bs => merge b (joinList bs)

theorem joinList_dominates {b : Cutoffs} {bs : List Cutoffs}
    (hb : b ∈ bs) : (joinList bs).Dominates b := by
  induction bs with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with heq | hmem
    · subst b
      exact merge_dominates_left a (joinList bs)
    · exact (merge_dominates_right a (joinList bs)).trans (ih hmem)

def common {n : ℕ} (cuts : Fin n → Cutoffs) : Cutoffs := joinList (List.ofFn cuts)

theorem common_dominates {n : ℕ} (cuts : Fin n → Cutoffs) (i : Fin n) :
    (common cuts).Dominates (cuts i) := by
  apply joinList_dominates
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

end Cutoffs

/-- All five expansion inequalities may use the exact same data selectors.
The `scale i Z` may differ between components, including sums of powers. -/
theorem finite_simultaneous_bound {n : ℕ}
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (value : Fin n → ℝ → ℝ → ℝ) (scale : Fin n → ℝ → ℝ)
    (hscale : ∀ i Z, 2 ≤ Z → 0 ≤ scale i Z)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z →
        value i Z (Z ^ τ) ≤ (cuts τ i).constant * scale i Z *
          (1 + Z ^ τ) ^ (budgets i).degree)
    (τ : ℝ) (hτ : 0 < τ) (hceiling : τ ≤ (HeightBudget.common budgets).ceiling)
    (Z : ℝ) (hZ : (Cutoffs.common (cuts τ)).threshold ≤ Z) (i : Fin n) :
    value i Z (Z ^ τ) ≤ (Cutoffs.common (cuts τ)).constant * scale i Z *
      (1 + Z ^ τ) ^ (HeightBudget.common budgets).degree := by
  have hbd := HeightBudget.common_dominates budgets i
  have hcd := Cutoffs.common_dominates (cuts τ) i
  have hZtwo : 2 ≤ Z := (Cutoffs.common (cuts τ)).threshold_two.trans hZ
  have hbase : 1 ≤ 1 + Z ^ τ := by
    have hh := Real.rpow_nonneg (by linarith : 0 ≤ Z) τ
    linarith
  have hb := hcomponent i τ hτ (hceiling.trans hbd.2) Z (hcd.1.trans hZ)
  have hweight := hscale i Z hZtwo
  have hleft : (cuts τ i).constant * scale i Z ≤
      (Cutoffs.common (cuts τ)).constant * scale i Z :=
    mul_le_mul_of_nonneg_right hcd.2 hweight
  have hright : (1 + Z ^ τ) ^ (budgets i).degree ≤
      (1 + Z ^ τ) ^ (HeightBudget.common budgets).degree :=
    Real.rpow_le_rpow_of_exponent_le hbase hbd.1
  exact hb.trans (mul_le_mul hleft hright
    (Real.rpow_nonneg (by linarith) _)
    (mul_nonneg (Cutoffs.common (cuts τ)).constant_nonneg hweight))

/-- The existential package makes the order of choices completely explicit. -/
theorem finite_simultaneous_package {n : ℕ}
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (value : Fin n → ℝ → ℝ → ℝ) (scale : Fin n → ℝ → ℝ)
    (hscale : ∀ i Z, 2 ≤ Z → 0 ≤ scale i Z)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z →
        value i Z (Z ^ τ) ≤ (cuts τ i).constant * scale i Z *
          (1 + Z ^ τ) ^ (budgets i).degree) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 2 ≤ Z₀ ∧ 0 ≤ C ∧
        ∀ Z, Z₀ ≤ Z → ∀ i,
          value i Z (Z ^ τ) ≤ C * scale i Z * (1 + Z ^ τ) ^ A := by
  let b := HeightBudget.common budgets
  refine ⟨b.degree, b.ceiling, b.degree_nonneg, b.ceiling_pos, ?_⟩
  intro τ hτ hc
  let c := Cutoffs.common (cuts τ)
  refine ⟨c.threshold, c.constant, c.threshold_two, c.constant_nonneg, ?_⟩
  intro Z hZ i
  exact finite_simultaneous_bound budgets cuts value scale hscale hcomponent τ hτ hc Z hZ i

/-- A false height flag keeps count estimates free of any height factor. -/
def budgetExponent (heightful : Bool) (A : ℝ) : ℝ := if heightful then A else 0

/-- Mixed version: principal/small/large estimates carry a height degree,
while block and witness counts retain exponent zero in the height. -/
theorem finite_simultaneous_mixed_bound {n : ℕ}
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (heightful : Fin n → Bool)
    (value : Fin n → ℝ → ℝ → ℝ) (scale : Fin n → ℝ → ℝ)
    (hscale : ∀ i Z, 2 ≤ Z → 0 ≤ scale i Z)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z →
        value i Z (Z ^ τ) ≤ (cuts τ i).constant * scale i Z *
          (1 + Z ^ τ) ^ budgetExponent (heightful i) (budgets i).degree)
    (τ : ℝ) (hτ : 0 < τ) (hceiling : τ ≤ (HeightBudget.common budgets).ceiling)
    (Z : ℝ) (hZ : (Cutoffs.common (cuts τ)).threshold ≤ Z) (i : Fin n) :
    value i Z (Z ^ τ) ≤ (Cutoffs.common (cuts τ)).constant * scale i Z *
      (1 + Z ^ τ) ^ budgetExponent (heightful i) (HeightBudget.common budgets).degree := by
  have hbd := HeightBudget.common_dominates budgets i
  have hcd := Cutoffs.common_dominates (cuts τ) i
  have hZtwo : 2 ≤ Z := (Cutoffs.common (cuts τ)).threshold_two.trans hZ
  have hbase : 1 ≤ 1 + Z ^ τ := by
    have hh := Real.rpow_nonneg (by linarith : 0 ≤ Z) τ
    linarith
  have hb := hcomponent i τ hτ (hceiling.trans hbd.2) Z (hcd.1.trans hZ)
  have hweight := hscale i Z hZtwo
  have hleft : (cuts τ i).constant * scale i Z ≤
      (Cutoffs.common (cuts τ)).constant * scale i Z :=
    mul_le_mul_of_nonneg_right hcd.2 hweight
  have he : budgetExponent (heightful i) (budgets i).degree ≤
      budgetExponent (heightful i) (HeightBudget.common budgets).degree := by
    unfold budgetExponent
    split_ifs
    · exact hbd.1
    · exact le_rfl
  have hright := Real.rpow_le_rpow_of_exponent_le hbase he
  exact hb.trans (mul_le_mul hleft hright
    (Real.rpow_nonneg (by linarith) _)
    (mul_nonneg (Cutoffs.common (cuts τ)).constant_nonneg hweight))

/-- The exact common-selector order, allowing height-free counts. -/
theorem finite_simultaneous_mixed_package {n : ℕ}
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (heightful : Fin n → Bool)
    (value : Fin n → ℝ → ℝ → ℝ) (scale : Fin n → ℝ → ℝ)
    (hscale : ∀ i Z, 2 ≤ Z → 0 ≤ scale i Z)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z →
        value i Z (Z ^ τ) ≤ (cuts τ i).constant * scale i Z *
          (1 + Z ^ τ) ^ budgetExponent (heightful i) (budgets i).degree) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 2 ≤ Z₀ ∧ 0 ≤ C ∧
        ∀ Z, Z₀ ≤ Z → ∀ i,
          value i Z (Z ^ τ) ≤ C * scale i Z *
            (1 + Z ^ τ) ^ budgetExponent (heightful i) A := by
  let b := HeightBudget.common budgets
  refine ⟨b.degree, b.ceiling, b.degree_nonneg, b.ceiling_pos, ?_⟩
  intro τ hτ hc
  let c := Cutoffs.common (cuts τ)
  refine ⟨c.threshold, c.constant, c.threshold_two, c.constant_nonneg, ?_⟩
  intro Z hZ i
  exact finite_simultaneous_mixed_bound budgets cuts heightful value scale hscale
    hcomponent τ hτ hc Z hZ i

end ExpansionInterfaces
