import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ArithmeticChildProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointNormalizedLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityMassBridge

/-!
# Choose the true arithmetic costs on the original normalized leaf

Only the original row mass dictionary and frozen single-atom bounds
are additional input. The four original side normalizations are rebuilt
with those proved costs before the family chooses its capacity children.

The source, rows, original cutoffs and both Fourier kernels remain the
same. Parent geometry and the original joint row-mask dictionaries
transport directly. The selected normalized children are then compared
with the canonical arithmetic kernel by the exact same-choice bridge.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace ActualHybridLeaf.NormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {leaf : ActualHybridLeaf K H U E}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- These fields describe actual original row and single-atom factors.
Neither a chosen child nor an estimate for a kernel mass is an input. -/
structure ArithmeticInput where
  commonLeftSlots : ℕ
  commonRightSlots : ℕ
  rowMass : ActualSecondRowMass (N.rows.restrictRows (fun h => ¬leaf.exceptional h))
    C commonLeftSlots commonRightSlots
  leftAtoms : ∀ r, (N.rectangles.leftFrame C r).source.FrozenAtomBounds
  rightAtoms : ∀ r, (N.rectangles.rightFrame C r).source.FrozenAtomBounds

variable (arithmetic : N.ArithmeticInput)

/-- The actual cost replacement happens before any capacity choice. -/
def withArithmetic : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
    rowDomain heightDomain window seminorms :=
  { N with
    left r := (N.left r).arithmeticCalibration arithmetic.rowMass (arithmetic.leftAtoms r)
    right r := (N.right r).arithmeticCalibration arithmetic.rowMass (arithmetic.rightAtoms r)
    left_height := N.left_height
    right_height := N.right_height }

@[simp] theorem withArithmetic_rows : (N.withArithmetic arithmetic).rows = N.rows := rfl

@[simp] theorem withArithmetic_sourcePair (parentWidth : ℝ) (b : Bool × Bool)
    (ξ : WithLp 2 (U × E)) :
    (N.withArithmetic arithmetic).family.sourcePair parentWidth b ξ =
      N.family.sourcePair parentWidth b ξ := rfl

/-- Original nominal widths, gaps, characters and slot caps survive the
cost choice. No property of a produced child is assumed. -/
def ParentGeometry.withArithmetic
    {d : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
    (raw : N.ParentGeometry d a step) :
    (N.withArithmetic arithmetic).ParentGeometry d a step where
  left_parent := raw.left_parent
  right_parent := raw.right_parent
  left_gap := raw.left_gap
  right_gap := raw.right_gap
  left_kappa := raw.left_kappa
  right_kappa := raw.right_kappa
  left_slots := raw.left_slots
  right_slots := raw.right_slots
  left_theta := raw.left_theta
  right_theta := raw.right_theta

/-- The joint budget remains a primitive original-row statement after
the arithmetic calibration is chosen. -/
def JointRowInput.withArithmetic (J : N.JointRowInput) :
    (N.withArithmetic arithmetic).JointRowInput where
  leftMask r := (N.left r).arithmeticCalibration_maskRecipe
    arithmetic.rowMass (arithmetic.leftAtoms r) (J.leftMask r)
  rightMask r := (N.right r).arithmeticCalibration_maskRecipe
    arithmetic.rowMass (arithmetic.rightAtoms r) (J.rightMask r)
  left_budget := J.left_budget
  right_budget := J.right_budget

/-- Filtering the moment-row enumeration leaves all original source
and frozen-atom data used in the arithmetic calibration unchanged. -/
def ArithmeticInput.withJointRows (J : N.JointRowInput) :
    (N.withJointRows J).ArithmeticInput where
  commonLeftSlots := arithmetic.commonLeftSlots
  commonRightSlots := arithmetic.commonRightSlots
  rowMass := arithmetic.rowMass
  leftAtoms := arithmetic.leftAtoms
  rightAtoms := arithmetic.rightAtoms

theorem withArithmetic_withJointRows (J : N.JointRowInput) :
    (N.withArithmetic arithmetic).withJointRows (J.withArithmetic N arithmetic) =
      (N.withJointRows J).withArithmetic (arithmetic.withJointRows N J) := rfl

/-- The raw presentation is reconstructed from this exact normalized
choice. In particular its deletion is not chosen again. -/
def leftRawChild (b : (N.withArithmetic arithmetic).family.active Finset.univ) :
    ((N.withArithmetic arithmetic).left b.val.1).calibration.CapacityChild
      ((N.withArithmetic arithmetic).left b.val.1).capacity :=
  ((N.withArithmetic arithmetic).left b.val.1).capacity.rawChild
    (N.left b.val.1).amplitude (N.left b.val.1).amplitude_pos
    (N.left b.val.1).bounds (N.left b.val.1).bounds_nonneg (N.left b.val.1).factor
    ((N.withArithmetic arithmetic).family.leftChild Finset.univ b)

def rightRawChild (b : (N.withArithmetic arithmetic).family.active Finset.univ) :
    ((N.withArithmetic arithmetic).right b.val.2).calibration.CapacityChild
      ((N.withArithmetic arithmetic).right b.val.2).capacity :=
  ((N.withArithmetic arithmetic).right b.val.2).capacity.rawChild
    (N.right b.val.2).amplitude (N.right b.val.2).amplitude_pos
    (N.right b.val.2).bounds (N.right b.val.2).bounds_nonneg (N.right b.val.2).factor
    ((N.withArithmetic arithmetic).family.rightChild Finset.univ b)

@[simp] theorem leftRawChild_removed
    (b : (N.withArithmetic arithmetic).family.active Finset.univ) :
    (N.leftRawChild arithmetic b).removed =
      ((N.withArithmetic arithmetic).family.leftChild Finset.univ b).removed := rfl

@[simp] theorem rightRawChild_removed
    (b : (N.withArithmetic arithmetic).family.active Finset.univ) :
    (N.rightRawChild arithmetic b).removed =
      ((N.withArithmetic arithmetic).family.rightChild Finset.univ b).removed := rfl

/-- This is the weight of the same concrete family on the original
Boolean rectangle carrier, not an independently produced bound. -/
theorem arithmetic_family_weight (parentWidth : ℝ) (hZ : 0 < Z)
    (b : (N.withArithmetic arithmetic).family.active Finset.univ) :
    (N.withArithmetic arithmetic).family.weight Finset.univ parentWidth b =
      actualCapacityPairWeight (N.rectangles.leftFrame C b.val.1)
        (N.rectangles.rightFrame C b.val.2)
        (N.left b.val.1).calibration (N.right b.val.2).calibration arithmetic.rowMass
        (arithmetic.leftAtoms b.val.1) (arithmetic.rightAtoms b.val.2)
        (N.leftRawChild arithmetic b) (N.rightRawChild arithmetic b)
        (N.left b.val.1).bounds (N.right b.val.2).bounds Z parentWidth :=
  CanonicalCapacityKernelMass.chosen_weight_eq
    (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
    (N.left b.val.1).calibration (N.right b.val.2).calibration arithmetic.rowMass
    (arithmetic.leftAtoms b.val.1) (arithmetic.rightAtoms b.val.2)
    ((N.withArithmetic arithmetic).left b.val.1).capacity
    ((N.withArithmetic arithmetic).right b.val.2).capacity
    (N.left b.val.1).amplitude (N.right b.val.2).amplitude
    (N.left b.val.1).amplitude_pos (N.right b.val.2).amplitude_pos
    (N.left b.val.1).bounds (N.right b.val.2).bounds
    (N.left b.val.1).bounds_nonneg (N.right b.val.2).bounds_nonneg
    (N.left b.val.1).factor (N.right b.val.2).factor
    ((N.withArithmetic arithmetic).family.leftChild Finset.univ b)
    ((N.withArithmetic arithmetic).family.rightChild Finset.univ b) Z parentWidth hZ

variable [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- The canonical arithmetic kernel mass theorem applies directly to
the actual retained pair and its unchanged original Fourier kernels. -/
theorem arithmetic_family_kernel_mass
    (parentWidth : ℝ) (hZ : 0 < Z)
    (b : (N.withArithmetic arithmetic).family.active Finset.univ)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ)
    (hleftRadius : ∀ z, (N.left b.val.1).amplitude (WithLp.toLp 2 z) =
      polynomialProfileRadius B₁ J₁ J₂ z)
    (hrightRadius : ∀ z, (N.right b.val.2).amplitude (WithLp.toLp 2 z) =
      polynomialProfileRadius B₂ J₁ J₂ z) :
    ((N.withArithmetic arithmetic).family.kernel Finset.univ
      (actualNestedLabelMeasure (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel)
        (fun _ => leaf.weight)) parentWidth b).real Set.univ =
    (CanonicalCapacityKernelMass.kernel
      (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
      (N.left b.val.1).calibration (N.right b.val.2).calibration arithmetic.rowMass
      (arithmetic.leftAtoms b.val.1) (arithmetic.rightAtoms b.val.2)
      (N.leftRawChild arithmetic b) (N.rightRawChild arithmetic b)
      (N.left b.val.1).bounds (N.right b.val.2).bounds
      leaf.weight Z parentWidth leaf.firstKernel leaf.secondKernel B₁ B₂ J₁ J₂).real Set.univ := by
  rw [(N.withArithmetic arithmetic).family.kernel_actualNestedLabelMeasure Finset.univ
    (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel) (fun _ => leaf.weight)
    parentWidth b]
  exact CanonicalCapacityKernelMass.chosen_kernel_mass_eq
    (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
    (N.left b.val.1).calibration (N.right b.val.2).calibration arithmetic.rowMass
    (arithmetic.leftAtoms b.val.1) (arithmetic.rightAtoms b.val.2)
    ((N.withArithmetic arithmetic).left b.val.1).capacity
    ((N.withArithmetic arithmetic).right b.val.2).capacity
    (N.left b.val.1).amplitude (N.right b.val.2).amplitude
    (N.left b.val.1).amplitude_pos (N.right b.val.2).amplitude_pos
    (N.left b.val.1).bounds (N.right b.val.2).bounds
    (N.left b.val.1).bounds_nonneg (N.right b.val.2).bounds_nonneg
    (N.left b.val.1).factor (N.right b.val.2).factor
    ((N.withArithmetic arithmetic).family.leftChild Finset.univ b)
    ((N.withArithmetic arithmetic).family.rightChild Finset.univ b)
    leaf.weight Z parentWidth leaf.weight_nonneg hZ
    leaf.firstKernel leaf.secondKernel B₁ B₂ hB₁ hB₂ J₁ J₂ hleftRadius hrightRadius

end ActualHybridLeaf.NormalizationData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.withArithmetic
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.withArithmetic_withJointRows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmetic_family_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmetic_family_kernel_mass

