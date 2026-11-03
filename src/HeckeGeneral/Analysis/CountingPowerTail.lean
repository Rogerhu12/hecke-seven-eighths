import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Power tails from actual linear counting

Every finite set of tail indices is partitioned into dyadic shells. The
actual finite cutoff bounds the cardinality of each shell, and monotonicity
of a negative real power bounds its summands. A convergent geometric series
then bounds all finite sums and supplies actual summability. No tail estimate
or summability hypothesis is an input, and the index type need not be given
a countability instance.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped Classical BigOperators

/-- The explicit constant produced by the dyadic decomposition. -/
def countingPowerTailConstant (A : ℝ) : ℝ :=
  2 * (1 - (2 : ℝ) ^ (1 - A))⁻¹

theorem countingPowerTailConstant_pos {A : ℝ} (hA : 1 < A) :
    0 < countingPowerTailConstant A := by
  have hb : (2 : ℝ) ^ (1 - A) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact mul_pos (by norm_num) (inv_pos.mpr (sub_pos.mpr hb))

variable {ι : Type*}

/-- Every finite portion of the strict tail has the same explicit bound.
The cutoff cardinality is the actual cardinality of the supplied finite set. -/
theorem finite_sum_neg_rpow_tail_le_of_linear_count
    (q : ι → ℝ) (hfinite : ∀ H : ℝ, Set.Finite {i | q i ≤ H})
    (D : ℝ)
    (hcount : ∀ H : ℝ, 0 ≤ H →
      (Nat.card {i : ι // q i ≤ H} : ℝ) ≤ D * (1 + H))
    (A ρ X : ℝ) (hA : 1 < A) (hρ : 0 < ρ) (hX : 1 ≤ X)
    (t : Finset {i : ι // X < ρ * q i}) :
    (∑ i ∈ t, (ρ * q i.val) ^ (-A)) ≤
      countingPowerTailConstant A * D * (1 + ρ⁻¹) * X ^ (1 - A) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hD : 0 ≤ D := by
    have hc := hcount 0 (by norm_num)
    have hn : 0 ≤ (Nat.card {i : ι // q i ≤ 0} : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hnegA : -A ≤ 0 := by linarith
  let b : ℝ := (2 : ℝ) ^ (1 - A)
  have hbpos : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hblt : b < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbSummable : Summable (fun n : ℕ => b ^ n) :=
    summable_geometric_of_lt_one hbpos.le hblt
  have hbSum : (∑' n : ℕ, b ^ n) = (1 - b)⁻¹ :=
    tsum_geometric_of_lt_one hbpos.le hblt
  let J := {i : ι // X < ρ * q i}
  have near (i : J) : ∃ n : ℕ,
      X * (2 : ℝ) ^ n ≤ ρ * q i.val ∧
        ρ * q i.val < X * (2 : ℝ) ^ (n + 1) := by
    have hratio : 1 ≤ (ρ * q i.val) / X :=
      (le_div_iff₀ hXpos).mpr (by simpa using i.property.le)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio (by norm_num : 1 < (2 : ℝ))
    refine ⟨n, ?_, ?_⟩
    · simpa only [mul_comm] using (le_div_iff₀ hXpos).mp hn
    · simpa only [mul_comm] using (div_lt_iff₀ hXpos).mp hn'
  let level : J → ℕ := fun i => (near i).choose
  have hlevel (i : J) : X * (2 : ℝ) ^ level i ≤ ρ * q i.val ∧
      ρ * q i.val < X * (2 : ℝ) ^ (level i + 1) := (near i).choose_spec
  let K : ℝ := 2 * D * (1 + ρ⁻¹) * X ^ (1 - A)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hshell (n : ℕ) :
      (∑ i ∈ t with level i = n, (ρ * q i.val) ^ (-A)) ≤ K * b ^ n := by
    let s : Finset J := t.filter (fun i => level i = n)
    let L : ℝ := X * (2 : ℝ) ^ n
    let U : ℝ := X * (2 : ℝ) ^ (n + 1)
    have hLpos : 0 < L := mul_pos hXpos (pow_pos (by norm_num) _)
    have hLone : 1 ≤ L := by
      have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le hX hp
    have hUpos : 0 < U := mul_pos hXpos (pow_pos (by norm_num) _)
    have hsub : s.image (fun i : J => i.val) ⊆ (hfinite (U / ρ)).toFinset := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hjn : level j = n := (Finset.mem_filter.mp hj).2
      apply (hfinite (U / ρ)).mem_toFinset.mpr
      apply (le_div_iff₀ hρ).mpr
      have hh := (hlevel j).2.le
      rw [hjn] at hh
      simpa only [U, mul_comm] using hh
    have hcardNat : s.card ≤ (hfinite (U / ρ)).toFinset.card := by
      rw [← Finset.card_image_of_injective s Subtype.val_injective]
      exact Finset.card_le_card hsub
    have hcutoff : ((hfinite (U / ρ)).toFinset.card : ℝ) ≤ D * (1 + U / ρ) := by
      rw [← Nat.card_eq_card_finite_toFinset (hfinite (U / ρ))]
      exact hcount (U / ρ) (div_nonneg hUpos.le hρ.le)
    have hcard : (s.card : ℝ) ≤ D * (1 + U / ρ) :=
      (Nat.cast_le.mpr hcardNat).trans hcutoff
    have hcoarse : 1 + U / ρ ≤ 2 * (1 + ρ⁻¹) * L := by
      dsimp only [U, L]
      rw [pow_succ, div_eq_mul_inv]
      dsimp only [L] at hLone
      nlinarith
    have hpower : L * L ^ (-A) = X ^ (1 - A) * b ^ n := by
      have hLpow : L * L ^ (-A) = L ^ (1 - A) := by
        rw [sub_eq_add_neg, Real.rpow_add hLpos, Real.rpow_one]
      rw [hLpow]
      change (X * (2 : ℝ) ^ n) ^ (1 - A) = X ^ (1 - A) * b ^ n
      rw [Real.mul_rpow hXpos.le (pow_nonneg (by norm_num) _)]
      congr 1
      dsimp only [b]
      rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
        mul_comm (n : ℝ) (1 - A), Real.rpow_mul_natCast (by norm_num)]
    change (∑ i ∈ s, (ρ * q i.val) ^ (-A)) ≤ _
    calc
      _ ≤ ∑ _i ∈ s, L ^ (-A) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin := (Finset.mem_filter.mp hi).2
        have hh := (hlevel i).1
        rw [hin] at hh
        exact Real.rpow_le_rpow_of_nonpos hLpos hh hnegA
      _ = (s.card : ℝ) * L ^ (-A) := by simp
      _ ≤ (D * (1 + U / ρ)) * L ^ (-A) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hLpos.le _)
      _ ≤ (D * (2 * (1 + ρ⁻¹) * L)) * L ^ (-A) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoarse hD)
          (Real.rpow_nonneg hLpos.le _)
      _ = K * b ^ n := by
        calc
          _ = (2 * D * (1 + ρ⁻¹)) * (L * L ^ (-A)) := by ring
          _ = _ := by rw [hpower]; dsimp only [K]; ring
  have hpartition :
      (∑ n ∈ t.image level, ∑ i ∈ t with level i = n, (ρ * q i.val) ^ (-A)) =
        ∑ i ∈ t, (ρ * q i.val) ^ (-A) :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem level hi) _
  calc
    _ = ∑ n ∈ t.image level, ∑ i ∈ t with level i = n,
        (ρ * q i.val) ^ (-A) := hpartition.symm
    _ ≤ ∑ n ∈ t.image level, K * b ^ n := Finset.sum_le_sum (fun n _ => hshell n)
    _ = K * (∑ n ∈ t.image level, b ^ n) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (∑' n : ℕ, b ^ n) :=
      mul_le_mul_of_nonneg_left
        (hbSummable.sum_le_tsum (t.image level) (fun n _ => pow_nonneg hbpos.le n)) hK
    _ = countingPowerTailConstant A * D * (1 + ρ⁻¹) * X ^ (1 - A) := by
      rw [hbSum]
      dsimp only [K, b, countingPowerTailConstant]
      ring

/-- Actual summability of the strict power tail, obtained from bounded finite sums. -/
theorem summable_neg_rpow_tail_of_linear_count
    (q : ι → ℝ) (hfinite : ∀ H : ℝ, Set.Finite {i | q i ≤ H})
    (D : ℝ)
    (hcount : ∀ H : ℝ, 0 ≤ H →
      (Nat.card {i : ι // q i ≤ H} : ℝ) ≤ D * (1 + H))
    (A ρ X : ℝ) (hA : 1 < A) (hρ : 0 < ρ) (hX : 1 ≤ X) :
    Summable (fun i : {i : ι // X < ρ * q i} => (ρ * q i.val) ^ (-A)) := by
  apply summable_of_sum_le (fun i => Real.rpow_nonneg (by linarith [i.property]) _)
  exact finite_sum_neg_rpow_tail_le_of_linear_count q hfinite D hcount A ρ X hA hρ hX

/-- The quantitative tail estimate has no convergence premise. -/
theorem tsum_neg_rpow_tail_le_of_linear_count
    (q : ι → ℝ) (hfinite : ∀ H : ℝ, Set.Finite {i | q i ≤ H})
    (D : ℝ)
    (hcount : ∀ H : ℝ, 0 ≤ H →
      (Nat.card {i : ι // q i ≤ H} : ℝ) ≤ D * (1 + H))
    (A ρ X : ℝ) (hA : 1 < A) (hρ : 0 < ρ) (hX : 1 ≤ X) :
    (∑' i : {i : ι // X < ρ * q i}, (ρ * q i.val) ^ (-A)) ≤
      countingPowerTailConstant A * D * (1 + ρ⁻¹) * X ^ (1 - A) := by
  apply Real.tsum_le_of_sum_le (fun i => Real.rpow_nonneg (by linarith [i.property]) _)
  exact finite_sum_neg_rpow_tail_le_of_linear_count q hfinite D hcount A ρ X hA hρ hX

/-- Finite cutoffs and linear counting give summability of the entire scaled
negative power, including its finite portion below the first tail cutoff. -/
theorem summable_neg_rpow_of_linear_count
    (q : ι → ℝ)
    (hfinite : ∀ H : ℝ, Set.Finite {i | q i ≤ H})
    (D : ℝ)
    (hcount : ∀ H : ℝ, 0 ≤ H →
      (Nat.card {i : ι // q i ≤ H} : ℝ) ≤ D * (1 + H))
    (A ρ : ℝ) (hA : 1 < A) (hρ : 0 < ρ) :
    Summable (fun i : ι => (ρ * q i) ^ (-A)) := by
  let s : Set ι := {i | 1 < ρ * q i}
  have hs : Summable (fun i : s => (ρ * q i.val) ^ (-A)) :=
    summable_neg_rpow_tail_of_linear_count q hfinite D hcount A ρ 1 hA hρ le_rfl
  have hcfinite : sᶜ.Finite := by
    apply (hfinite (ρ⁻¹)).subset
    intro i hi
    have hi' : ρ * q i ≤ 1 := le_of_not_gt hi
    rw [← one_div]
    exact (le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using hi')
  have hc : Summable (fun i : ↥(sᶜ) => (ρ * q i.val) ^ (-A)) :=
    hcfinite.summable (fun i : ι => (ρ * q i) ^ (-A))
  exact (summable_subtype_and_compl (s := s)).mp ⟨hs, hc⟩

end HeckeGeneral.Analysis
