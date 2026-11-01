import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.CountingPowerTail
import Expansion.PhysicalRowSupport

/-!
# Genuine infinite tails of the complete physical row set

The original row cutoff contains every sixth-unit sector and every
sixth-power-free exterior ideal.  Its proved linear count supplies actual
summability and a quantitative strict power tail.  No summability or tail
estimate is a field of an auxiliary input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.LargeRows

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem finite_frequencyRowNorm_cutoff (H : ℝ) :
    Set.Finite {u : FrequencyRow K S | frequencyRowNorm K S u ≤ H} := by
  apply (frequencyRows K S (max 0 H)).finite_toSet.subset
  intro u hu
  exact (_root_.Expansion.Project.mem_frequencyRows_iff K S (max 0 H)
    (le_max_left _ _) u).mpr (hu.trans (le_max_right _ _))

/-- The actual finite row count in the form used by the dyadic tail lemma. -/
theorem exists_frequencyRowNorm_cutoff_count :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 0 ≤ H →
      (Nat.card {u : FrequencyRow K S // frequencyRowNorm K S u ≤ H} : ℝ) ≤ D * (1 + H) := by
  obtain ⟨D, hD, hcount⟩ := frequencyRows_linear_count K S
  refine ⟨D, hD, ?_⟩
  intro H hH
  have hcard : Nat.card {u : FrequencyRow K S // frequencyRowNorm K S u ≤ H} =
      (frequencyRows K S H).card :=
    Nat.subtype_card (frequencyRows K S H)
      (_root_.Expansion.Project.mem_frequencyRows_iff K S H hH)
  have hsub : frequencyRows K S H ⊆ frequencyRows K S (max 1 H) := by
    intro u hu
    apply (_root_.Expansion.Project.mem_frequencyRows_iff K S (max 1 H)
      (zero_le_one.trans (le_max_left _ _)) u).mpr
    exact ((_root_.Expansion.Project.mem_frequencyRows_iff K S H hH u).mp hu).trans
      (le_max_right _ _)
  rw [hcard]
  calc
    _ ≤ ((frequencyRows K S (max 1 H)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ D * max 1 H := hcount _ (le_max_left _ _)
    _ ≤ D * (1 + H) := mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hD.le

/-- The infinite power tail is genuinely summable and has the expected
linear-count exponent.  The constant precedes every cutoff. -/
theorem exists_frequencyRowNorm_power_tail_bound {p : ℝ} (hp : p < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      Summable (fun u : {u : FrequencyRow K S // U < frequencyRowNorm K S u} =>
        frequencyRowNorm K S u.val ^ p) ∧
      (∑' u : {u : FrequencyRow K S // U < frequencyRowNorm K S u},
        frequencyRowNorm K S u.val ^ p) ≤ C * U ^ (p + 1) := by
  obtain ⟨D, hD, hcount⟩ := exists_frequencyRowNorm_cutoff_count K S
  have hA : 1 < -p := by linarith
  have htailC : 0 < countingPowerTailConstant (-p) := countingPowerTailConstant_pos hA
  refine ⟨2 * countingPowerTailConstant (-p) * D,
    by positivity, ?_⟩
  intro U hU
  have hsum := summable_neg_rpow_tail_of_linear_count (frequencyRowNorm K S)
    (finite_frequencyRowNorm_cutoff K S) D hcount (-p) 1 U hA (by norm_num) hU
  have hbound := tsum_neg_rpow_tail_le_of_linear_count (frequencyRowNorm K S)
    (finite_frequencyRowNorm_cutoff K S) D hcount (-p) 1 U hA (by norm_num) hU
  let e : {u : FrequencyRow K S // U < frequencyRowNorm K S u} ≃
      {u : FrequencyRow K S // U < 1 * frequencyRowNorm K S u} :=
    { toFun := fun u => ⟨u.val, by simpa only [one_mul] using u.property⟩
      invFun := fun u => ⟨u.val, by simpa only [one_mul] using u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he (u : {u : FrequencyRow K S // U < frequencyRowNorm K S u}) :
      (e u).val = u.val := rfl
  constructor
  · simpa only [Function.comp_def, he, one_mul, neg_neg] using hsum.comp_injective e.injective
  · have hexp : 1 - -p = p + 1 := by ring
    rw [← e.tsum_eq (fun u => (1 * frequencyRowNorm K S u.val) ^ (- -p))] at hbound
    simpa only [he, one_mul, neg_neg, inv_one, hexp, show (1 : ℝ) + 1 = 2 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using hbound

/-- The entire original row power is summable too, including the bounded
rows.  This is used for the all-scale absolute clause of the large input. -/
theorem summable_frequencyRowNorm_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun u : FrequencyRow K S => frequencyRowNorm K S u ^ p) := by
  obtain ⟨D, hD, hcount⟩ := exists_frequencyRowNorm_cutoff_count K S
  simpa only [one_mul, neg_neg] using
    summable_neg_rpow_of_linear_count (frequencyRowNorm K S)
      (finite_frequencyRowNorm_cutoff K S) D hcount (-p) 1 (by linarith) (by norm_num)

end HeckeSkeleton.Expansion.LargeRows

#print axioms HeckeSkeleton.Expansion.LargeRows.exists_frequencyRowNorm_power_tail_bound
#print axioms HeckeSkeleton.Expansion.LargeRows.summable_frequencyRowNorm_rpow
