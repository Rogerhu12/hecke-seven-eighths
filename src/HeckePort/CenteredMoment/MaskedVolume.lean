import HeckePort.CenteredMoment.Volume

/-!
# Volume of masked ideal sums

Port of `OAI.SevenEighths.CenteredMomentMaskedVolume` (openai/math,
`OAI/NumberTheory/DirichletL/Moments/MaskedVolume.lean`, revision `fd4aeeb2`).
openai states it for the primary-generator character `primaryIdealCharacter c χ`
and its lattice volume estimate. Here `Ψ` is any multiplicative function on
ideals bounded by one, with an `IdealVolumeInput`; the allowed-generator
character of `Generator.lean` is the general-field instance.
-/

noncomputable section

namespace HeckePort.CenteredMomentMaskedVolume

open scoped NumberField Classical BigOperators SchwartzMap
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.IdealMobiusDivisorSum HeckePort.CenteredMomentMask HeckePort.CenteredMomentVolume

variable {K : Type*} [Field K] [NumberField K]

theorem masked_ideal_volume_error (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W : 𝓢(ℝ, ℂ)) (b X : ℝ)
    (hX : 0 < X) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    ‖(∑' I : Ideal (𝓞 K), (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) *
        V.density W‖ ≤
      ((idealDivisors R).card : ℝ) * V.error W := by
  classical
  let v := V.density W
  let B := V.error W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal (𝓞 K), Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hnD (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ ⊥ := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B :=
    V.volume W (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
  have hcoef (D : Ideal (𝓞 K)) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (hΨ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal (𝓞 K), (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end HeckePort.CenteredMomentMaskedVolume
