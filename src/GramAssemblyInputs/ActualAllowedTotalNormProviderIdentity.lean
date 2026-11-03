import ActualChoiceMaskedTotalNorm
import ActualAllowedGeneratorColumnMask
import ActualOriginalAnnularUnitReconstruction

/-!
UNCOMPILED / native 0. For an actual allowed generator d, the existing
corrected whole-column provider is exactly the column-mask expression
used by the actual ideal/unit enumeration. No restriction of a complex
sum or independently supplied weight identity is involved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedTotalNormProviderDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open ActualGeneratorChoiceDraft ActualProbeGaussFourierDraft
open ActualChoiceMaskedAnnularDraft ActualChoiceMaskedTotalNormDraft
open ActualAllowedColumnMaskDraft ActualOriginalAnnularUnitDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "E" => ExteriorIdeal K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ (w.S : Set (HeightOneSpectrum (𝓞 K))))

/-- Literal identification with the previously constructed total-norm
estimate provider, including both actual choice masks and finite norms. -/
theorem choiceMaskedTotalNormAnnularJointSummand_allowedGenerator
    (a : ℝ → ℝ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (c k : NZ) (D : E) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) (m : NZ × NZ) :
    choiceMaskedTotalNormAnnularJointSummand K w ζ hζ σ hS6 a ψ c k
      (probeGenerator K S w.D D) ν φ R N m =
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.1).2 *
        choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.2).2 *
        originalTotalNormAnnularSummand K S ζ hζ σ hS6 a ψ c k
          (probeGenerator K S w.D D) ν φ R N m := by
  unfold choiceMaskedTotalNormAnnularJointSummand choiceMaskedAnnularSummand
  rw [choiceColumnMask_probeGenerator, choiceColumnMask_probeGenerator]
  rfl

end HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedTotalNormProviderDraft
