import HeckePort.CenteredMoment.MaskedVolume
import HeckePort.CenteredMoment.Basic

/-!
# Centered cancellation of masked ideal sums

Port of `OAI.SevenEighths.CenteredMomentCancellation` (openai/math,
`OAI/NumberTheory/DirichletL/Moments/Cancellation.lean`, revision `fd4aeeb2`).
The density splits as the divisor sum `maskedDensity Ψ R` times the
`IdealVolumeInput` density of the weight; openai's second factor is
`|c|⁻² · ∑ primaryResidueValue · paperRadialFourier W 0`.
-/

noncomputable section

namespace HeckePort.CenteredMomentCancellation

open scoped NumberField Classical BigOperators SchwartzMap
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.CenteredMomentVolume HeckePort.CenteredMomentMaskedVolume

variable {K : Type*} [Field K] [NumberField K]

def maskedSum (Ψ : Ideal (𝓞 K) → ℂ) (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal (𝓞 K), (if IsCoprime I R then (1 : ℂ) else 0) *
    (Ψ I * W ((Ideal.absNorm I : ℝ) / X))

def maskedDensity (Ψ : Ideal (𝓞 K) → ℂ) (R : Ideal (𝓞 K)) : ℂ :=
  ∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)

def maskedError {Ψ : Ideal (𝓞 K) → ℂ} (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K))
    (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((idealDivisors R).card : ℝ) * V.error W

lemma maskedError_nonneg {Ψ : Ideal (𝓞 K) → ℂ} (V : IdealVolumeInput K Ψ)
    (R : Ideal (𝓞 K)) (W : 𝓢(ℝ, ℂ)) : 0 ≤ maskedError V R W :=
  mul_nonneg (Nat.cast_nonneg _) (V.error_nonneg W)

theorem maskedSum_volume (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W : 𝓢(ℝ, ℂ)) (b X : ℝ)
    (hX : 0 < X) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    ‖maskedSum Ψ R W X - (X : ℂ) * (maskedDensity Ψ R * V.density W)‖ ≤
      maskedError V R W := by
  have h := masked_ideal_volume_error Ψ hΨ V R hR W b X hX hs
  convert h using 1
  unfold maskedSum maskedDensity
  congr 1
  ring
  all_goals rfl

theorem masked_rectangle_saving (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W₁ W₂ : 𝓢(ℝ, ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError V R W₁ + maskedError V R W₂
    let C := ‖maskedDensity Ψ R * V.density W₁‖ + ‖maskedDensity Ψ R * V.density W₂‖ + E
    ‖maskedSum Ψ R W₁ X₁ * maskedSum Ψ R W₂ X₂ -
      maskedSum Ψ R W₁ Y₁ * maskedSum Ψ R W₂ Y₂‖ ≤ 4 * E * C * (T / L) := by
  let E := maskedError V R W₁ + maskedError V R W₂
  let v₁ := maskedDensity Ψ R * V.density W₁
  let v₂ := maskedDensity Ψ R * V.density W₂
  let C := ‖v₁‖ + ‖v₂‖ + E
  have hE₁ := maskedError_nonneg V R W₁
  have hE₂ := maskedError_nonneg V R W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE
  have hL0 : 0 < L := by linarith
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖maskedSum Ψ R W₁ X - (X : ℂ) * v₁‖ ≤ E :=
    (maskedSum_volume Ψ hΨ V R hR W₁ b₁ X (lt_of_lt_of_le hL0 hX) hs₁).trans
      (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum Ψ R W₂ X - (X : ℂ) * v₂‖ ≤ E :=
    (maskedSum_volume Ψ hΨ V R hR W₂ b₂ X (lt_of_lt_of_le hL0 hX) hs₂).trans
      (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X : ℂ) * v₁‖ ≤ C * X := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg v₂]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum Ψ R W₂ X‖ ≤ C * X := by
    have hb := norm_le_norm_sub_add (maskedSum Ψ R W₂ X) ((X : ℂ) * v₂)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E * X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    dsimp only [C]
    nlinarith [mul_nonneg (norm_nonneg v₁) (le_trans hL0.le hX)]
  have hmain : ((X₁ : ℂ) * v₁) * ((X₂ : ℂ) * v₂) =
      ((Y₁ : ℂ) * v₁) * ((Y₂ : ℂ) * v₂) := by
    have hp : (X₁ : ℂ) * X₂ = (Y₁ : ℂ) * Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁ : ℂ) * X₂) * (v₁ * v₂) := by ring
      _ = ((Y₁ : ℂ) * Y₂) * (v₁ * v₂) := by rw [hp]
      _ = _ := by ring
  exact HeckePort.CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end HeckePort.CenteredMomentCancellation
