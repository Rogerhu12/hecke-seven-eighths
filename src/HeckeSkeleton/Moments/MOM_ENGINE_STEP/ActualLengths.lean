module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The multiplicity ledger at actual ideal norms

The logarithmic lengths in this file are computed from the complete
ideal products.  In particular the active radical contains exactly the
primes whose two multiplicities differ modulo six.  The first-transform
allowance is therefore a consequence of the local multiplicity proof
with the actual prime norms, without an equal-prime-norm approximation.
-/

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

variable {K : Type*} [Field K] [NumberField K]

/-- Logarithmic norm length at the external scale. -/
def idealLogLength (Z : ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm I : ℝ) / Real.log Z

theorem idealLogLength_nonneg (Z : ℝ) (hZ : 1 < Z)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) : 0 ≤ idealLogLength Z I := by
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le

theorem idealLogLength_pow (Z : ℝ) (I : Ideal (𝓞 K)) (n : ℕ) :
    idealLogLength Z (I ^ n) = (n : ℝ) * idealLogLength Z I := by
  simp only [idealLogLength, map_pow, Nat.cast_pow, Real.log_pow]
  ring

theorem idealLogLength_prod {ι : Type*} (Z : ℝ) (S : Finset ι)
    (P : ι → Ideal (𝓞 K)) (hP : ∀ p ∈ S, P p ≠ 0) :
    idealLogLength Z (∏ p ∈ S, P p) = ∑ p ∈ S, idealLogLength Z (P p) := by
  have hn (p : ι) (hp : p ∈ S) : (Ideal.absNorm (P p) : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => hP p hp (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [idealLogLength, map_prod, Nat.cast_prod]
  rw [Real.log_prod hn, Finset.sum_div]

theorem idealLogLength_powerProduct {ι : Type*} (Z : ℝ) (S : Finset ι)
    (P : ι → Ideal (𝓞 K)) (n : ι → ℕ) (hP : ∀ p ∈ S, P p ≠ 0) :
    idealLogLength Z (∏ p ∈ S, (P p) ^ n p) =
      ∑ p ∈ S, idealLogLength Z (P p) * (n p : ℝ) := by
  rw [idealLogLength_prod Z S (fun p => (P p) ^ n p)
    (fun p hp => pow_ne_zero _ (hP p hp))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [idealLogLength_pow, mul_comm]

theorem idealLogLength_activeRadical {ι : Type*} (Z : ℝ) (S : Finset ι)
    (P : ι → Ideal (𝓞 K)) (i j : ι → ℕ) (hP : ∀ p ∈ S, P p ≠ 0) :
    idealLogLength Z (∏ p ∈ S.filter (fun p => i p % 6 ≠ j p % 6), P p) =
      ∑ p ∈ S, idealLogLength Z (P p) * exponentRadical (i p) (j p) := by
  rw [idealLogLength_prod Z _ P (fun p hp => hP p (Finset.mem_filter.mp hp).1),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : i p % 6 = j p % 6 <;> simp [exponentRadical, he]

/-- The actual first-transform Cauchy allowances fit inside the complete
common-support saving, including every nonprimitive multiplicity. -/
theorem actual_ideal_paired_allowance {ι : Type*} (Z : ℝ) (hZ : 1 < Z)
    (S : Finset ι) (P : ι → Ideal (𝓞 K)) (i j : ι → ℕ)
    (_hinj : Set.InjOn P S)
    (hP : ∀ p ∈ S, Prime (P p))
    (hi : ∀ p ∈ S, 1 ≤ i p) (hj : ∀ p ∈ S, 1 ≤ j p) :
    let C := ∏ p ∈ S, (P p) ^ i p
    let D := ∏ p ∈ S, (P p) ^ j p
    let radical := ∏ p ∈ S, P p
    let active := ∏ p ∈ S.filter (fun p => i p % 6 ≠ j p % 6), P p
    firstAllowance (idealLogLength Z C) (idealLogLength Z D) (idealLogLength Z active) +
        firstAllowance (idealLogLength Z D) (idealLogLength Z C) (idealLogLength Z active) ≤
      idealLogLength Z C + idealLogLength Z D -
        2 * idealLogLength Z radical - idealLogLength Z active := by
  dsimp only
  have hne : ∀ p ∈ S, P p ≠ 0 := fun p hp => (hP p hp).ne_zero
  rw [idealLogLength_powerProduct Z S P i hne,
    idealLogLength_powerProduct Z S P j hne,
    idealLogLength_prod Z S P hne, idealLogLength_activeRadical Z S P i j hne]
  exact weighted_paired_allowance S (fun p => idealLogLength Z (P p)) i j
    (fun p hp => idealLogLength_nonneg Z hZ (P p) (hne p hp)) hi hj

/-- The central outer exponent is at most the parent width at the literal
norm lengths of the common pieces. -/
theorem actual_ideal_outer_allowance {ι : Type*} (Z : ℝ) (hZ : 1 < Z)
    (S : Finset ι) (P : ι → Ideal (𝓞 K)) (i j : ι → ℕ) (M : ℝ)
    (hinj : Set.InjOn P S)
    (hP : ∀ p ∈ S, Prime (P p))
    (hi : ∀ p ∈ S, 1 ≤ i p) (hj : ∀ p ∈ S, 1 ≤ j p) :
    let c := idealLogLength Z (∏ p ∈ S, (P p) ^ i p)
    let d := idealLogLength Z (∏ p ∈ S, (P p) ^ j p)
    let p := idealLogLength Z (∏ p ∈ S, P p)
    let R := idealLogLength Z (∏ p ∈ S.filter (fun p => i p % 6 ≠ j p % 6), P p)
    M + (firstAllowance c d R + firstAllowance d c R - (c + d - 2 * p - R)) / 2 ≤ M := by
  exact first_outer_allowance M _ _ _ _
    (actual_ideal_paired_allowance Z hZ S P i j hinj hP hi hj)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_ideal_outer_allowance
