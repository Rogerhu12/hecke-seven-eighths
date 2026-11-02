import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalGeometry

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Actual first allowances in the original second-terminal ledger

The same original common ideals determine the physical cutoff,
first normalization and first profile. Their left and right orientations
are identified before either terminal sum. Only the original length
box and the padded parent core enter the numerical estimate.
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

include μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

variable (step : ℝ) (DE : (source).CommonLabel)
variable (D : (((source).block DE).mask (source).mask).powerset) (negative : Bool)
variable (G : OriginalNominalGeometry (K := K) internal Z step)
variable (hcoordinates : G.ideals = if negative then
  ((source).block DE).literalRightCoordinates D.val else
  ((source).block DE).literalLeftCoordinates D.val)

include hcoordinates

/-- The original physical and active lengths are bounded in either
orientation of the very same first common block. -/
theorem literalPrimitiveGeometry_ideal_lengths
    (columnBound : ℝ)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ columnBound) :
    idealLogLength Z G.ideals.first.val ≤ columnBound ∧
      idealLogLength Z G.ideals.complementary.val ≤ columnBound ∧
      idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val) ≤ columnBound := by
  sorry

/-- Reversing the original columns leaves the actual first-profile
shift unchanged, by the common-support identity of the active radical. -/
theorem literalPrimitiveGeometry_profileShift (total : ℝ) :
    G.firstProfileShiftForTotal total δ₁ =
      Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
        hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D total := by
  sorry

/-- The raw sharp second amplitude is combined with the original
first profile before the common ideals are summed. -/
theorem literalPrimitiveGeometry_zero_ledger
    (hstep : 0 ≤ step) (lengthBound columnBound : ℝ)
    (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ columnBound)
    {floor padding : ℝ}
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
    (loss ε productExponent total : ℝ) (hloss : loss ≤ 1) (hε : 0 ≤ ε)
    (hproduct : productExponent ≤ 2 * (max lengthBound columnBound + 1)) :
    G.sharpZeroExponent loss δ₁ + productExponent * ε ≤
      (total - idealLogLength Z G.ideals.first.val + G.boundary) +
        (padding + 5 * step / 3 + G.supportError + 2 * loss +
          (4 * max lengthBound columnBound + 2) * δ₁ +
            2 * (max lengthBound columnBound + 1) * ε) -
      Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
        hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D total := by
  sorry

/-- The fixed physical tail saving pays the same original allowance;
no additional inverse power of a moving common ideal is requested. -/
theorem literalPrimitiveGeometry_tail_ledger
    (columnBound : ℝ)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ columnBound)
    (loss saving total : ℝ) (hloss : 0 ≤ loss) (hsaving : 2 * columnBound ≤ saving) :
    -saving ≤ (total - idealLogLength Z G.ideals.first.val + G.boundary) + loss -
      Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
        hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D total := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveGeometry_ideal_lengths
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveGeometry_profileShift
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveGeometry_zero_ledger
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveGeometry_tail_ledger
