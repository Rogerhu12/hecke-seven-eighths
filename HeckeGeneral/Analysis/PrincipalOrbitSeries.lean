import HeckeGeneral.Arithmetic.PrincipalOrbitCounting

/-!
# Absolute convergence of integral generator-orbit sums

All fibers are actual generator quotients. The finite-index unit-sector
multiplicity is retained in the Dedekind majorant. This is the integral
case; the S-integer orbit unfolding is a separate construction.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Ideal NumberField HeckeGeneral.Arithmetic
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

abbrev IntegralGeneratorSectors (Γ : Subgroup (𝓞 K)ˣ) :=
  Σ I : (Ideal (𝓞 K))⁰, GeneratorOrbits Γ I.val

theorem tsum_generatorFiber_const (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex]
    (I : (Ideal (𝓞 K))⁰) (c : ℝ) :
    (∑' _ : GeneratorOrbits Γ I.val, c) =
      (if I.val.IsPrincipal then (Γ.index : ℝ) else 0) * c := by
  letI : NeZero I.val := ⟨nonZeroDivisors.coe_ne_zero I⟩
  rw [tsum_const, nsmul_eq_mul, card_generatorOrbits_eq_indicator]
  split_ifs <;> simp

theorem summable_integralGeneratorSectors_norm_rpow
    (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun x : IntegralGeneratorSectors K Γ => (absNorm x.1.val : ℝ) ^ (-σ)) := by
  unfold IntegralGeneratorSectors
  apply (summable_sigma_of_nonneg (fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simp_rw [tsum_generatorFiber_const]
  apply ((summable_nonzeroIdeal_norm_rpow K hσ).mul_left (Γ.index : ℝ)).of_nonneg_of_le
  · intro I
    split_ifs <;> positivity
  · intro I
    split_ifs
    · exact le_rfl
    · simp only [zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem tsum_integralGeneratorSectors_norm_rpow
    (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] {σ : ℝ} (hσ : 1 < σ) :
    (∑' x : IntegralGeneratorSectors K Γ, (absNorm x.1.val : ℝ) ^ (-σ)) =
      ∑' I : (Ideal (𝓞 K))⁰,
        (if I.val.IsPrincipal then (Γ.index : ℝ) else 0) * (absNorm I.val : ℝ) ^ (-σ) := by
  rw [(summable_integralGeneratorSectors_norm_rpow K Γ hσ).tsum_sigma]
  refine tsum_congr fun I => ?_
  simpa only using tsum_generatorFiber_const K Γ I ((absNorm I.val : ℝ) ^ (-σ))

theorem tsum_integralGeneratorSectors_norm_rpow_le
    (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] {σ : ℝ} (hσ : 1 < σ) :
    (∑' x : IntegralGeneratorSectors K Γ, (absNorm x.1.val : ℝ) ^ (-σ)) ≤
      (Γ.index : ℝ) * ∑' I : (Ideal (𝓞 K))⁰, (absNorm I.val : ℝ) ^ (-σ) := by
  rw [tsum_integralGeneratorSectors_norm_rpow K Γ hσ, ← tsum_mul_left]
  have hsmall := ((summable_sigma_of_nonneg
      (fun x : IntegralGeneratorSectors K Γ => Real.rpow_nonneg
        (show 0 ≤ (absNorm x.1.val : ℝ) from Nat.cast_nonneg _) (-σ))).1
    (summable_integralGeneratorSectors_norm_rpow K Γ hσ)).2
  simp_rw [tsum_generatorFiber_const] at hsmall
  apply hsmall.tsum_le_tsum ?_
    ((summable_nonzeroIdeal_norm_rpow K hσ).mul_left (Γ.index : ℝ))
  intro I
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    positivity

/-- A power-decaying actual sector profile has an absolutely convergent orbit sum. -/
theorem summable_integralGeneratorSectors_of_norm_le
    (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] {σ C : ℝ} (hσ : 1 < σ)
    (f : IntegralGeneratorSectors K Γ → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ C * (absNorm x.1.val : ℝ) ^ (-σ)) : Summable f := by
  exact ((summable_integralGeneratorSectors_norm_rpow K Γ hσ).mul_left C).of_norm_bounded hf

end HeckeGeneral.Analysis
