import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNormalizedLabelWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ArithmeticNormalizedLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridGeometry

/-!
# Original pointwise weights on the combined live-leaf family

The public finite carrier is the original live leaf times its two
Boolean rectangle choices. The projection below uses the already
selected capacity children; proof irrelevance identifies their local
and combined presentations.

The arithmetic theorem inserts only original scalar identities and
individual length, profile and atom windows. Its pointwise conclusion
is consumed internally by the finite-image mass theorem. It introduces
neither a total mass hypothesis nor a new child choice.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable [IsPrincipalIdealRing A.R]
variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (leaves : J → ActualHybridLeaf K H U E)
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)

/-- The exact scalar of the same selected pair is unchanged by
combining the original finite leaf carrier. -/
theorem weight_eq (parentWidth : ℝ)
    (b : (normalizedFamily leaves N).active Finset.univ) :
    (normalizedFamily leaves N).weight Finset.univ parentWidth b =
      (N b.val.1).family.weight Finset.univ parentWidth
        (activeRectangle leaves N b) := rfl

/-- The measure, including the original outer weight, is also the
literal local measure of the same chosen rectangle. -/
theorem kernel_eq [MeasurableSpace (WithLp 2 (U × E))]
    (parentWidth : ℝ)
    (b : (normalizedFamily leaves N).active Finset.univ) :
    (normalizedFamily leaves N).kernel Finset.univ
      (actualNestedLabelMeasure (firstKernels leaves) (secondKernels leaves)
        (outerWeights leaves)) parentWidth b =
      (N b.val.1).family.kernel Finset.univ
        (actualNestedLabelMeasure (fun _ => (leaves b.val.1).firstKernel)
          (fun _ => (leaves b.val.1).secondKernel)
          (fun _ => (leaves b.val.1).weight)) parentWidth
        (activeRectangle leaves N b) := rfl

variable (arithmetic : ∀ j, (N j).ArithmeticInput)

local notation "chosen" => fun j => (N j).withArithmetic (arithmetic j)

variable (b : (normalizedFamily leaves chosen).active Finset.univ)
local notation "raw" => N b.val.1
local notation "costs" => arithmetic b.val.1
local notation "rectangle" => activeRectangle leaves chosen b
local notation "leftFrame" => raw.rectangles.leftFrame C b.val.2.1
local notation "rightFrame" => raw.rectangles.rightFrame C b.val.2.2

variable {firstNormalization remaining : ℝ}
variable (L : OriginalPairAllowanceWindow leftFrame rightFrame
  (raw.left b.val.2.1).calibration (raw.right b.val.2.2).calibration
  costs.rowMass (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
  ((raw.withArithmetic costs).left b.val.2.1).capacity
  ((raw.withArithmetic costs).right b.val.2.2).capacity
  Z firstNormalization remaining)
variable {branch : TwoDivisorCommonBranch (K := K)}
variable {Ray₁ Ray₂ : Type*}
  [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

/-- The local original-label bound belongs to the exact full finite
family used by the parent estimate. The remaining factor includes the
original first orbital fibre, and, where present, the single pool
density and actual valuation tag. These are retained by equality. -/
theorem arithmetic_outer_index_weight
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (atoms : CanonicalCapacityKernelMass.OriginalAtomWindow
      leftFrame rightFrame costs.rowMass
      (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
      (raw.left b.val.2.1).bounds (raw.right b.val.2.2).bounds cap B)
    (j : branch.Index)
    (hleft : costs.rowMass.leftIdeal = j.2.2.1.val.1.1)
    (hright : costs.rowMass.rightIdeal = j.2.2.1.val.1.2)
    (hdivisor : leftFrame.source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupport : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (factor : ℝ) (hfactor : 0 ≤ factor)
    (houter : (leaves b.val.1).weight / Z ^ parentWidth =
      factor *
        (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
          ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
          ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) /
        firstNormalization) :
    outerWeights leaves b.val *
        (normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      factor *
        (firstCost * ((costs.rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
          orbitalFieldFactor K) * Z ^ remaining * branch.indexWeight j) := by
  rw [weight_eq leaves chosen parentWidth b]
  exact raw.arithmeticCosts_family_outer_index_weight costs.rowMass
    costs.leftAtoms costs.rightAtoms rectangle L hZ cap B hB atoms j
    hleft hright hdivisor parentWidth total rawProfile firstCost hfirst hprofile
    hD hE hsupport phase₁ χ₁ phase₂ χ₂ factor hfactor houter

end ActualHybridFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.weight_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.kernel_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.arithmetic_outer_index_weight

