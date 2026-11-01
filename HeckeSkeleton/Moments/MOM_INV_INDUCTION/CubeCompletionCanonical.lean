import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletion
import HeckeSkeleton.Moments.MOM_BASE.CubeInversion

/-!
# The short and reopened parts of the actual canonical completion

The short part remains a completed sum at scale `X / N(H)^3`. The long
part is reopened on `b = H * B`; its only extra coefficient is the
selected divisor sum. Arbitrary whole-index marks and completely
multiplicative original zero masks survive both identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOM_BASE

variable {K : Type} [Field K] [NumberField K]

/-- One extracted term of the proved canonical cube inversion. -/
def extractedCubeTerm (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ) (H : Ideal (𝓞 K)) : ℂ :=
  (moebius H : ℂ) * tau H ^ 3 / (cubeIdealNorm H : ℂ) *
    canonicalCompletedSum gamma tau (fun A => d (H ^ 3 * A)) V
      (X / cubeIdealNorm H ^ 3)

theorem extractedCubeTerm_eq_dilation
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ) (H : Ideal (𝓞 K)) :
    extractedCubeTerm gamma tau d V X H =
      (moebius H : ℂ) * ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K),
        canonicalCompletedTerm gamma tau d V X (C, H * B) := by
  simp_rw [← canonicalCompletedTerm_cube_extract gamma tau d V X H]
  simp only [extractedCubeTerm, canonicalCompletedSum, tsum_mul_left]
  ring

theorem extractedCubeTerm_summable
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X U : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic U) :
    Summable (extractedCubeTerm gamma tau d V X) :=
  canonicalCubeInversion_summable gamma tau d V X U hX hV

/-- Every nonzero extracted term comes from a divisor of an actual
cube coordinate in the finite completed source support. -/
theorem extractedCubeTerm_finite_support
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X U : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic U) :
    Function.HasFiniteSupport (extractedCubeTerm gamma tau d V X) := by
  classical
  let F := canonicalCompletedTerm gamma tau d V X
  have hF : Function.HasFiniteSupport F := canonicalCompletedTerm_finite_support gamma tau d V X U hX hV
  let T := hF.toFinset
  let A := cubeDivisorPool (T.image Prod.snd)
  apply A.finite_toSet.subset
  intro H hH
  by_contra hnot
  have hz (C B : Ideal (𝓞 K)) : F (C, H * B) = 0 := by
    by_contra hn
    have hmem : (C, H * B) ∈ T := (Set.Finite.mem_toFinset hF).mpr hn
    have hHB : H * B ≠ ⊥ := by
      intro he
      exact hn (by simpa only [he] using canonicalCompletedTerm_bot_right gamma tau d V X C)
    exact hnot (cubeDivisorPool_mem (Finset.mem_image_of_mem Prod.snd hmem)
      hHB (dvd_mul_right H B))
  apply hH
  rw [extractedCubeTerm_eq_dilation]
  change (moebius H : ℂ) * ∑' C : Ideal (𝓞 K), ∑' B : Ideal (𝓞 K), F (C, H * B) = 0
  simp only [hz, tsum_zero, mul_zero]

/-- The selected extracted cubes reopen on the same ideal polynomial,
including `d(C * b^3)` and every zero in the multiplicative mask `tau`. -/
theorem canonical_selected_cubes_reopen
    (P : Ideal (𝓞 K) → Prop) (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' H : Ideal (𝓞 K), if P H then extractedCubeTerm gamma tau d V X H else 0) =
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient P CB.2 * canonicalCompletedTerm gamma tau d V X CB := by
  simp_rw [extractedCubeTerm_eq_dilation]
  exact selected_cube_dilates_reopen P (canonicalCompletedTerm gamma tau d V X)
    (canonicalCompletedTerm_finite_support gamma tau d V X U hX hV)
    (canonicalCompletedTerm_bot_right gamma tau d V X)

/-- Partition the actual completion by any extracted-ideal condition.
No triangle inequality or lost scalar is built into this exact identity. -/
theorem canonical_completion_partition
    (P : Ideal (𝓞 K) → Prop) (gamma : Ideal (𝓞 K) → ℂ)
    (tau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X U : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' H : Ideal (𝓞 K), extractedCubeTerm gamma tau d V X H) =
      (∑' H : Ideal (𝓞 K), if P H then extractedCubeTerm gamma tau d V X H else 0) +
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient (fun H => ¬ P H) CB.2 *
          canonicalCompletedTerm gamma tau d V X CB := by
  classical
  have hs := extractedCubeTerm_finite_support gamma tau d V X U hX hV
  let A := hs.toFinset
  have ha (H : Ideal (𝓞 K)) (hH : H ∉ A) : extractedCubeTerm gamma tau d V X H = 0 := by
    by_contra hn
    exact hH ((Set.Finite.mem_toFinset hs).mpr hn)
  have hp (H : Ideal (𝓞 K)) (hH : H ∉ A) :
      (if P H then extractedCubeTerm gamma tau d V X H else 0) = 0 := by
    simp only [ha H hH, ite_self]
  have hn (H : Ideal (𝓞 K)) (hH : H ∉ A) :
      (if ¬ P H then extractedCubeTerm gamma tau d V X H else 0) = 0 := by
    simp only [ha H hH, ite_self]
  calc
    _ = ∑ H ∈ A, extractedCubeTerm gamma tau d V X H := tsum_eq_sum ha
    _ = (∑ H ∈ A, if P H then extractedCubeTerm gamma tau d V X H else 0) +
        ∑ H ∈ A, if ¬ P H then extractedCubeTerm gamma tau d V X H else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro H hH
      by_cases h : P H <;> simp only [h, not_true_eq_false, not_false_eq_true,
        ite_true, ite_false, zero_add, add_zero]
    _ = (∑' H, if P H then extractedCubeTerm gamma tau d V X H else 0) +
        ∑' H, if ¬ P H then extractedCubeTerm gamma tau d V X H else 0 := by
      congr 1
      · exact (tsum_eq_sum hp).symm
      · exact (tsum_eq_sum hn).symm
    _ = _ := by
      congr 1
      refine Eq.trans ?_
        (canonical_selected_cubes_reopen (fun H => ¬ P H) gamma tau d V X U hX hV)
      apply tsum_congr
      intro H
      by_cases h : P H <;> simp only [h, not_true_eq_false, not_false_eq_true,
        ite_true, ite_false]

/-- The geometric short/long split used before the two-transform step. -/
theorem canonical_completion_short_long
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (d : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X U T : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) :
    (∑' H : Ideal (𝓞 K), extractedCubeTerm gamma tau d V X H) =
      (∑' H : Ideal (𝓞 K), if cubeIdealNorm H < T then
        extractedCubeTerm gamma tau d V X H else 0) +
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient (fun H => T ≤ cubeIdealNorm H) CB.2 *
          canonicalCompletedTerm gamma tau d V X CB := by
  simpa only [not_lt] using canonical_completion_partition
    (fun H : Ideal (𝓞 K) => cubeIdealNorm H < T) gamma tau d V X U hX hV

/-- The reopened scalar contains only the cube, its selected divisors,
and a fixed multiplicative coefficient. The moving row stays separate. -/
def reopenedCubeWeight (P : Ideal (𝓞 K) → Prop)
    (staticTau : Ideal (𝓞 K) →* ℂ) (b : Ideal (𝓞 K)) : ℂ :=
  reopenedCubeCoefficient P b * staticTau b ^ 3 / (cubeIdealNorm b : ℂ)

theorem reopenedCubeWeight_norm_le (P : Ideal (𝓞 K) → Prop)
    (staticTau : Ideal (𝓞 K) →* ℂ) (b : Ideal (𝓞 K))
    (hstatic : ‖staticTau b‖ ≤ 1) :
    ‖reopenedCubeWeight P staticTau b‖ ≤
      ((idealDivisors b).card : ℝ) / cubeIdealNorm b := by
  have hN : 0 ≤ cubeIdealNorm b := by unfold cubeIdealNorm; positivity
  have hpow : ‖staticTau b‖ ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hstatic 3
  rw [reopenedCubeWeight, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  apply div_le_div_of_nonneg_right _ hN
  calc
    ‖reopenedCubeCoefficient P b‖ * ‖staticTau b‖ ^ 3 ≤
        ‖reopenedCubeCoefficient P b‖ * 1 :=
      mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ ≤ ((idealDivisors b).card : ℝ) := by
      simpa only [mul_one] using reopenedCubeCoefficient_norm_le P b

/-- All row dependence is exactly the original cubic row character and
the original squarefree row character. The mark still sees `C * b^3`. -/
theorem reopenedCubeTerm_factor
    (P : Ideal (𝓞 K) → Prop) (gamma : Ideal (𝓞 K) → ℂ)
    (staticTau rowTau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (C b : Ideal (𝓞 K)) :
    reopenedCubeCoefficient P b *
        canonicalCompletedTerm gamma (staticTau * rowTau) d V X (C, b) =
      if Squarefree C then
        reopenedCubeWeight P staticTau b * rowTau b ^ 3 *
          (gamma C * staticTau C * rowTau C / (Real.sqrt (cubeIdealNorm C) : ℂ)) *
          d (C * b ^ 3) * V (cubeIdealNorm C * cubeIdealNorm b ^ 3 / X)
      else 0 := by
  by_cases hC : Squarefree C
  · simp only [canonicalCompletedTerm, hC, if_true, reopenedCubeWeight,
      MonoidHom.mul_apply, map_mul, map_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [canonicalCompletedTerm, hC, if_false, mul_zero]

/-- The central normalization of a reopened cube is exactly
`sqrt(N(b))/sqrt(X)`, before replacing its cube norm by an annular scale. -/
theorem completedVstar_cube_normalization (u b X : ℝ)
    (hu : 0 < u) (hb : 0 < b) (hX : 0 < X) :
    (Real.sqrt (u * b ^ 3 / X) : ℂ) /
        ((Real.sqrt u : ℂ) * (b : ℂ)) =
      (Real.sqrt b : ℂ) / (Real.sqrt X : ℂ) := by
  have hcube : Real.sqrt (b ^ 3) = b * Real.sqrt b := by
    rw [show b ^ 3 = b ^ 2 * b by ring, Real.sqrt_mul (sq_nonneg b),
      Real.sqrt_sq hb.le]
  have hroot : Real.sqrt (u * b ^ 3 / X) =
      Real.sqrt u * (b * Real.sqrt b) / Real.sqrt X := by
    rw [Real.sqrt_div (mul_nonneg hu.le (pow_nonneg hb.le 3)),
      Real.sqrt_mul hu.le, hcube]
  have hsu : (Real.sqrt u : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hu).ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hroot, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
  field_simp [hsu, hbC]

/-- The literal normalized long-cube polynomial, with its common joint
profile still present. This is the input to `CubeCompletionMellin`. -/
theorem reopenedCubeTerm_vstar
    (P : Ideal (𝓞 K) → Prop) (gamma : Ideal (𝓞 K) → ℂ)
    (staticTau rowTau : Ideal (𝓞 K) →* ℂ) (d : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (C b : Ideal (𝓞 K))
    (hC : C ≠ ⊥) (hb : b ≠ ⊥) (hX : 0 < X) :
    reopenedCubeCoefficient P b *
        canonicalCompletedTerm gamma (staticTau * rowTau) d (canonicalVstar W) X (C, b) =
      if Squarefree C then
        (Real.sqrt (cubeIdealNorm b) : ℂ) / (Real.sqrt X : ℂ) *
          reopenedCubeCoefficient P b * staticTau b ^ 3 * rowTau b ^ 3 *
          gamma C * staticTau C * rowTau C * d (C * b ^ 3) *
          W (cubeIdealNorm C * cubeIdealNorm b ^ 3 / X)
      else 0 := by
  by_cases hsf : Squarefree C
  · have hs := completedVstar_cube_normalization (cubeIdealNorm C) (cubeIdealNorm b) X
      (cubeIdealNorm_pos hC) (cubeIdealNorm_pos hb) hX
    simp only [canonicalCompletedTerm, hsf, if_true, canonicalVstar,
      MonoidHom.mul_apply, map_mul, map_pow]
    calc
      _ = ((Real.sqrt (cubeIdealNorm C * cubeIdealNorm b ^ 3 / X) : ℂ) /
            ((Real.sqrt (cubeIdealNorm C) : ℂ) * (cubeIdealNorm b : ℂ))) *
          (reopenedCubeCoefficient P b * staticTau b ^ 3 * rowTau b ^ 3 *
            gamma C * staticTau C * rowTau C * d (C * b ^ 3) *
            W (cubeIdealNorm C * cubeIdealNorm b ^ 3 / X)) := by ring
      _ = _ := by rw [hs]; ring
  · simp only [canonicalCompletedTerm, hsf, if_false, mul_zero]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
