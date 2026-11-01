import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalTerminalPowers

/-!
# Exact first-profile powers of the original primitive source

The selected physical divisor, active radical and full-support radius
are the original arithmetic objects. The first profile formula is
computed from them before any second stage or child normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => (atoms).raw Y₁ Y₂

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

/-- The exact original first-profile shift for the already selected
normalization. Both original ideal lengths remain in the expression. -/
def literalPrimitiveFirstProfileShift
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (total : ℝ) : ℝ :=
  total - (internal).q -
    idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val -
    idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) +
      δ₁ * (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val +
        idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) - (internal).m)

/-- This is the weight of the same actual first source used by every
second-stage factory. No row-weight estimate is assumed. -/
theorem literalPrimitiveFirstSource_weightBound
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (total : ℝ) :
    ((source).pieces DE D).weightBound =
      orbitalFieldFactor K * Z ^ ((a.m + a.q) - total +
        Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
          hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D total) := by
  have h := ((source).block DE).rowWeightBound_eq_original_ideal_lengths
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
    (source).radius D.val Z (internal).m δ₁ hZ
    (Q.literalPrimitiveFirstSource_radius μv ν C hroot hemb W ξ a Z t Y₁ Y₂
      hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half)
  change ((source).pieces DE D).weightBound = _ at h
  rw [h]
  unfold literalPrimitiveFirstProfileShift
  congr 2
  rw [← Q.fullSupportParameters_width a Z]
  ring

/-- At the actual normalization, the physical-mask and active lengths
cancel from the shift, and remain in the actual allowance itself. -/
theorem literalPrimitiveFirstProfileShift_normalization
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
      hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D
      (Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ a Z t Y₁ Y₂
        hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D) =
      (internal).n₁ + (internal).n₂ + (internal).z +
        δ₁ * (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val +
          idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) - (internal).m) := by
  unfold literalPrimitiveFirstProfileShift literalPrimitiveFirstTotal
  ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource_weightBound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstProfileShift_normalization
