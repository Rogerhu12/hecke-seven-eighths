import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalHybridMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFiniteKernelMass

/-!
# The actual hybrid family projects to the canonical mass theorem

The raw-child reconstruction, exact normalizer identity and kernel-mass
proof live in NormalizedCapacityRawBridge and CanonicalHybridMass.
This file only instantiates those results at the two children actually
chosen by a hybrid leaf after its arithmetic costs have been selected.

The outer leaf weight, both original Fourier kernels and the Boolean
rectangle label are literal projections of that same family. No new
capacity choice or aggregate mass hypothesis is introduced.
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
variable {H : Type} {ι U E : Type*} [Fintype ι] [DecidableEq ι]
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

variable {leaf : ActualHybridLeaf K H U E}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)
variable {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass (N.rows.restrictRows (fun h => ¬leaf.exceptional h))
  C kLeft kRight)
variable (BL : ∀ r, (N.rectangles.leftFrame C r).source.FrozenAtomBounds)
variable (BR : ∀ r, (N.rectangles.rightFrame C r).source.FrozenAtomBounds)

/-- The canonical raw presentation of the already selected left child. -/
def arithmeticCosts_leftRawChild
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ) :
    ((N.withArithmeticCosts W BL BR).left b.val.1).calibration.CapacityChild
      ((N.withArithmeticCosts W BL BR).left b.val.1).capacity :=
  ((N.withArithmeticCosts W BL BR).left b.val.1).capacity.rawChild
    (N.left b.val.1).amplitude (N.left b.val.1).amplitude_pos
    (N.left b.val.1).bounds (N.left b.val.1).bounds_nonneg (N.left b.val.1).factor
    ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b)

/-- The canonical raw presentation of the already selected right child. -/
def arithmeticCosts_rightRawChild
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ) :
    ((N.withArithmeticCosts W BL BR).right b.val.2).calibration.CapacityChild
      ((N.withArithmeticCosts W BL BR).right b.val.2).capacity :=
  ((N.withArithmeticCosts W BL BR).right b.val.2).capacity.rawChild
    (N.right b.val.2).amplitude (N.right b.val.2).amplitude_pos
    (N.right b.val.2).bounds (N.right b.val.2).bounds_nonneg (N.right b.val.2).factor
    ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b)

@[simp] theorem arithmeticCosts_leftRawChild_removed
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ) :
    (N.arithmeticCosts_leftRawChild W BL BR b).removed =
      ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b).removed := rfl

@[simp] theorem arithmeticCosts_rightRawChild_removed
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ) :
    (N.arithmeticCosts_rightRawChild W BL BR b).removed =
      ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b).removed := rfl

/-- The literal family weight uses the same raw presentation as the
canonical arithmetic theorem. -/
theorem arithmeticCosts_family_weight (parentWidth : ℝ) (hZ : 0 < Z)
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ) :
    (N.withArithmeticCosts W BL BR).family.weight Finset.univ parentWidth b =
      actualCapacityPairWeight (N.rectangles.leftFrame C b.val.1)
        (N.rectangles.rightFrame C b.val.2)
        (N.left b.val.1).calibration (N.right b.val.2).calibration W
        (BL b.val.1) (BR b.val.2)
        (N.arithmeticCosts_leftRawChild W BL BR b)
        (N.arithmeticCosts_rightRawChild W BL BR b)
        (N.left b.val.1).bounds (N.right b.val.2).bounds Z parentWidth :=
  normalized_pair_weight_eq_canonical
    (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
    (N.left b.val.1).calibration (N.right b.val.2).calibration W
    (BL b.val.1) (BR b.val.2)
    ((N.withArithmeticCosts W BL BR).left b.val.1).capacity
    ((N.withArithmeticCosts W BL BR).right b.val.2).capacity
    (N.left b.val.1).amplitude (N.right b.val.2).amplitude
    (N.left b.val.1).amplitude_pos (N.right b.val.2).amplitude_pos
    (N.left b.val.1).bounds (N.right b.val.2).bounds
    (N.left b.val.1).bounds_nonneg (N.right b.val.2).bounds_nonneg
    (N.left b.val.1).factor (N.right b.val.2).factor
    ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b)
    ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b) Z parentWidth hZ

variable [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- Project the original outer-weighted kernel of the actual family
to the canonical kernel on its unchanged two Fourier measures. -/
theorem arithmeticCosts_family_kernel_mass
    (parentWidth : ℝ) (hZ : 0 < Z)
    (b : (N.withArithmeticCosts W BL BR).family.active Finset.univ)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ)
    (hleftRadius : ∀ z, (N.left b.val.1).amplitude (WithLp.toLp 2 z) =
      polynomialProfileRadius B₁ J₁ J₂ z)
    (hrightRadius : ∀ z, (N.right b.val.2).amplitude (WithLp.toLp 2 z) =
      polynomialProfileRadius B₂ J₁ J₂ z) :
    ((N.withArithmeticCosts W BL BR).family.kernel Finset.univ
      (actualNestedLabelMeasure (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel)
        (fun _ => leaf.weight)) parentWidth b).real Set.univ =
    (CanonicalCapacityKernelMass.kernel
      (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
      (N.left b.val.1).calibration (N.right b.val.2).calibration W
      (BL b.val.1) (BR b.val.2)
      (N.arithmeticCosts_leftRawChild W BL BR b)
      (N.arithmeticCosts_rightRawChild W BL BR b)
      (N.left b.val.1).bounds (N.right b.val.2).bounds
      leaf.weight Z parentWidth leaf.firstKernel leaf.secondKernel B₁ B₂ J₁ J₂).real Set.univ := by
  rw [(N.withArithmeticCosts W BL BR).family.kernel_actualNestedLabelMeasure Finset.univ
    (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel) (fun _ => leaf.weight)
    parentWidth b]
  exact normalized_family_kernel_mass_eq_canonical
    (N.rectangles.leftFrame C b.val.1) (N.rectangles.rightFrame C b.val.2)
    (N.left b.val.1).calibration (N.right b.val.2).calibration W
    (BL b.val.1) (BR b.val.2)
    ((N.withArithmeticCosts W BL BR).left b.val.1).capacity
    ((N.withArithmeticCosts W BL BR).right b.val.2).capacity
    (N.left b.val.1).amplitude (N.right b.val.2).amplitude
    (N.left b.val.1).amplitude_pos (N.right b.val.2).amplitude_pos
    (N.left b.val.1).bounds (N.right b.val.2).bounds
    (N.left b.val.1).bounds_nonneg (N.right b.val.2).bounds_nonneg
    (N.left b.val.1).factor (N.right b.val.2).factor
    ((N.withArithmeticCosts W BL BR).family.leftChild Finset.univ b)
    ((N.withArithmeticCosts W BL BR).family.rightChild Finset.univ b)
    leaf.weight Z parentWidth leaf.weight_nonneg hZ
    leaf.firstKernel leaf.secondKernel B₁ B₂ hB₁ hB₂ J₁ J₂ hleftRadius hrightRadius

end ActualHybridLeaf.NormalizationData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmeticCosts_family_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.arithmeticCosts_family_kernel_mass

