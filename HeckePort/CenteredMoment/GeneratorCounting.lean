import HeckePort.CenteredMoment.Counting
import HeckePort.CenteredMoment.Generator

/-!
# Masked sums of the allowed-generator character

The field-free results of `Counting` and `Cancellation` for the general-field
character of `Generator`. The trivial bound needs no further input; the
centered saving needs the `IdealVolumeInput` of the character.
-/

noncomputable section

namespace HeckePort.CenteredMomentGenerator

open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical SchwartzMap
open HeckePort.CenteredMomentVolume HeckePort.CenteredMomentCancellation
open HeckePort.CenteredMomentCounting

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D)
variable (c : S.integer K) (hc : c ≠ 0)
variable (χ : MulChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ)
variable (hχ : SixthPowerTrivial K S c χ)

include hc in
theorem generator_maskedSum_absolute (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b M X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X) (hW : ∀ y, ‖W y‖ ≤ M)
    (hs : Function.support W ⊆ Set.Iic b) :
    ‖maskedSum (generatorIdealHom K S D c χ hD hχ) R W X‖ ≤
      (idealCountConstant K * b * M) * X :=
  maskedSum_absolute _ (norm_generatorCharacter_le_one K S D c χ hc)
    (generatorCharacter_bot K S D c χ) R W b M X hb hM hX hW hs

include hc in
theorem generator_masked_rectangle_saving
    (V : IdealVolumeInput K (generatorIdealHom K S D c χ hD hχ))
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W₁ W₂ : 𝓢(ℝ, ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let Ψ := generatorIdealHom K S D c χ hD hχ
    let E := maskedError V R W₁ + maskedError V R W₂
    let C := ‖maskedDensity Ψ R * V.density W₁‖ + ‖maskedDensity Ψ R * V.density W₂‖ + E
    ‖maskedSum Ψ R W₁ X₁ * maskedSum Ψ R W₂ X₂ -
      maskedSum Ψ R W₁ Y₁ * maskedSum Ψ R W₂ Y₂‖ ≤ 4 * E * C * (T / L) :=
  masked_rectangle_saving _ (norm_generatorCharacter_le_one K S D c χ hc) V R hR W₁ W₂ b₁ b₂
    hs₁ hs₂ X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end HeckePort.CenteredMomentGenerator
