import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalIdealWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalTerminalPowers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance

/-!
# Fixed original second-terminal geometry

An actual first common label contains an original Cartesian column,
and hence an original paired row. The complete joint budget then proves
the internal row length is nonnegative. This supplies the missing
premise for a uniform physical inverse-radius bound even when some
second sources have no nonzero coefficients or no physical rows.
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
local notation "raw" => atoms.raw Y₁ Y₂

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

include μv ν C hroot hemb W ξ a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

/-- A genuine first common label supplies its own admitted original row.
No second-source activity or nonempty-row premise is imposed. -/
theorem literalPrimitiveCommon_m_nonneg (DE : source.CommonLabel) :
    0 ≤ (Q.fullSupportParameters a Z).m := by
  obtain ⟨ij, hij, _⟩ := Finset.mem_image.mp DE.property
  have hi : ij.1 ∈ raw.exteriorColumns := (Finset.mem_product.mp hij).1
  have hc : ij.1 ∈ raw.columns := (Finset.mem_filter.mp hi).1
  have hplain := Finset.mem_product.mp (Finset.mem_product.mp hc).1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  have hu' : u ∈ pairedRows (data ξ) a Z := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hu
  exact Q.fullSupportParameters_m_nonneg_of_pairedRow a Z hZ hbudget ξ u hu'

/-- Every nominal tag uses the same original coordinate bounds. The
right orientation uses the proved symmetry of the actual active radical. -/
theorem literalPrimitiveGeometry_inverse_bound
    (step : ℝ) (hstep : 0 ≤ step) (lengthBound columnBound : ℝ)
    (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hN : ∀ i ∈ source.columns, (Ideal.absNorm (source.ideal i).val : ℝ) ≤ Z ^ columnBound)
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (negative : Bool)
    (G : OriginalNominalGeometry (K := K) (Q.fullSupportParameters a Z) Z step)
    (hcoordinates : G.ideals = if negative then
      (source.block DE).literalRightCoordinates D.val else
      (source.block DE).literalLeftCoordinates D.val) :
    G.retainedLength + G.enlargement ≤
      4 * max lengthBound columnBound + G.supportError + 2 * step := by
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound hN DE D
  have hm := Q.literalPrimitiveCommon_m_nonneg μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE
  have htotal' : (Q.fullSupportParameters a Z).n₁ +
      (Q.fullSupportParameters a Z).n₂ + (Q.fullSupportParameters a Z).z ≤
        max lengthBound columnBound := htotal.trans (le_max_left _ _)
  apply G.inverse_radius_exponent_le hZ hstep (max lengthBound columnBound) hm htotal'
  · cases negative <;> simp only [Bool.false_eq_true,
      if_false, if_true] at hcoordinates
    · simpa only [hcoordinates, FirstCommonCharacterBlock.literalLeftCoordinates_complementary]
        using hlengths.2.2.2.trans (le_max_right lengthBound columnBound)
    · simpa only [hcoordinates, FirstCommonCharacterBlock.literalRightCoordinates_complementary]
        using hlengths.2.2.2.trans (le_max_right lengthBound columnBound)
  · cases negative <;> simp only [Bool.false_eq_true,
      if_false, if_true] at hcoordinates
    · simpa only [hcoordinates, FirstCommonCharacterBlock.literalLeftCoordinates_first,
        FirstCommonCharacterBlock.literalLeftCoordinates_opposite]
        using hlengths.2.2.1.trans (le_max_right lengthBound columnBound)
    · simpa only [hcoordinates, FirstCommonCharacterBlock.literalRightCoordinates_first,
        FirstCommonCharacterBlock.literalRightCoordinates_opposite,
        firstActiveRadical_swap_of_support DE.val.1 DE.val.2 (source.block DE).common_support_eq]
        using hlengths.2.2.1.trans (le_max_right lengthBound columnBound)

end CompleteMovingRowRecipe

namespace CanonicalOriginalTerminalPowers

/-- A common fixed degree for the direct, main and all three valuation
sources. The full sevenfold frozen prime power is included. -/
def primitiveDegree (cap : ℕ) (lengthBound columnBound step loss cutoffExponent : ℝ) : ℝ :=
  tailDegree (2 * (cap + 2)) lengthBound columnBound (columnBound + 7 * (step / 3))
    (4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step)

def primitiveCutoff (cap : ℕ) (lengthBound columnBound step loss cutoffExponent
    Nsave decay Z : ℝ) : ℝ :=
  Z ^ firstTailCutoffExponent
    (primitiveDegree cap lengthBound columnBound step loss cutoffExponent) Nsave decay

theorem primitiveCutoff_ge_one (cap : ℕ)
    (lengthBound columnBound step loss cutoffExponent Nsave decay Z : ℝ)
    (hZ : 1 ≤ Z) (hdecay : 1 < decay) :
    1 ≤ primitiveCutoff cap lengthBound columnBound step loss cutoffExponent Nsave decay Z :=
  Real.one_le_rpow hZ (firstTailCutoffExponent_nonneg _ _ _ hdecay)

end CanonicalOriginalTerminalPowers
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveCommon_m_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveGeometry_inverse_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one
