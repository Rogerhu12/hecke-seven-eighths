import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass

/-!
# Exact payment of the original column-constant profile factors

A constant multiplier on each complete column can be put into the
same correlation row. The source carrier, its complete correlation,
its original ideal fibres and all arithmetic classes are unchanged.
The actual row-mass calculation pays the product of the two norms
exactly once, instead of repeating it for every normalized profile.

The two constant extractions compose on the original leaf. This keeps
the existing source-to-normalized-family interface and both original
Fourier kernels, including when an earlier extracted scalar is zero.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualSecondCorrelationRows

/-- Only the original row's column-constant multiplier is moved. -/
def withColumnConstants (R : ActualSecondCorrelationRows A σ H ι) (a b : ℂ) :
    ActualSecondCorrelationRows A σ H ι :=
  { R with weight := fun h => R.weight h * a * star b }

@[simp] theorem withColumnConstants_rows (R : ActualSecondCorrelationRows A σ H ι)
    (a b : ℂ) : (R.withColumnConstants a b).rows = R.rows := rfl

@[simp] theorem withColumnConstants_live (R : ActualSecondCorrelationRows A σ H ι)
    (a b : ℂ) : (R.withColumnConstants a b).live = R.live := rfl

theorem withColumnConstants_restrictRows (R : ActualSecondCorrelationRows A σ H ι)
    (a b : ℂ) (keep : H → Prop) :
    (R.withColumnConstants a b).restrictRows keep =
      (R.restrictRows keep).withColumnConstants a b := rfl

end ActualSecondCorrelationRows

namespace ActualSecondRowMass

private theorem columnConstants_weight (s p x y a b : ℂ) :
    s * p * x * y * a * b = s * (p * a * b) * x * y := by
  ring

private theorem columnConstants_envelope (p a b x y : ℝ) :
    (p * a * b) * x * y = (a * b) * (p * x * y) := by
  ring

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- The new profile and its bound are calculated from the old original
profile. No new row, correlation, fibre or total-mass bound is assumed. -/
def withColumnConstants (a b : ℂ) :
    ActualSecondRowMass (R.withColumnConstants a b) C kLeft kRight where
  leftAtoms := W.leftAtoms
  rightAtoms := W.rightAtoms
  left_ideal := W.left_ideal
  right_ideal := W.right_ideal
  radius := W.radius
  mask := W.mask
  rowProfile h := W.rowProfile h * a * star b
  profileBound := W.profileBound * ‖a‖ * ‖b‖
  profileBound_nonneg := mul_nonneg
    (mul_nonneg W.profileBound_nonneg (norm_nonneg _)) (norm_nonneg _)
  profile_bound h hh := by
    simp only [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (W.profile_bound h hh) (norm_nonneg _)) (norm_nonneg _)
  weight_eq h hh := by
    change R.weight h * a * star b = _
    exact (congrArg (fun z : ℂ => z * a * star b) (W.weight_eq h hh)).trans
      (columnConstants_weight (secondOrbitalScalar (K := K) (S := A.Sf) W.radius W.mask)
        (W.rowProfile h) (W.leftAtoms.value h) (star (W.rightAtoms.value h)) a (star b))
  unitIdeal := W.unitIdeal
  unit_ideal := W.unit_ideal
  nonunitIdeal := W.nonunitIdeal
  nonunit_ideal := W.nonunit_ideal
  left_positive := W.left_positive
  originalFiber := W.originalFiber
  original_fibers := W.original_fibers

@[simp] theorem withColumnConstants_originalFiber (a b : ℂ) :
    (W.withColumnConstants a b).originalFiber = W.originalFiber := rfl

theorem withColumnConstants_commonEnvelope (a b : ℂ) :
    (W.withColumnConstants a b).commonEnvelope = (‖a‖ * ‖b‖) * W.commonEnvelope := by
  change (W.profileBound * ‖a‖ * ‖b‖) * Real.sqrt W.leftAtoms.envelope *
      Real.sqrt W.rightAtoms.envelope =
    (‖a‖ * ‖b‖) *
      (W.profileBound * Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope)
  exact columnConstants_envelope W.profileBound ‖a‖ ‖b‖
    (Real.sqrt W.leftAtoms.envelope) (Real.sqrt W.rightAtoms.envelope)

theorem withColumnConstants_rowBound (a b : ℂ) :
    (W.withColumnConstants a b).rowBound = (‖a‖ * ‖b‖) * W.rowBound := by
  unfold rowBound
  rw [W.withColumnConstants_commonEnvelope]
  change ‖secondOrbitalScalar (K := K) (S := A.Sf) W.radius W.mask‖ *
    ((‖a‖ * ‖b‖) * W.commonEnvelope) / W.commonDenominator * W.correlationBound = _
  ring

end ActualSecondRowMass

namespace ActualHybridLeaf

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (B : ActualHybridLeaf K H U V)

/-- This inverse form is only used on a live source after the actual
scalar normal form has proved both original constants nonzero. -/
def stripColumnConstants (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    B.ConstantAtomExtraction where
  leftScalar := a
  rightScalar := b
  leftResidual h i := a⁻¹ * B.leftCoefficient h i
  rightResidual h i := b⁻¹ * B.rightCoefficient h i
  left _ _ _ _ := by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  right _ _ _ _ := by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]

namespace ConstantAtomExtraction

variable {B} (X : B.ConstantAtomExtraction) (Y : X.leaf.ConstantAtomExtraction)

/-- Constant extraction is associative on the same original columns.
All source identities are composed before the two positive energies. -/
def trans : B.ConstantAtomExtraction where
  leftScalar := X.leftScalar * Y.leftScalar
  rightScalar := X.rightScalar * Y.rightScalar
  leftResidual := Y.leftResidual
  rightResidual := Y.rightResidual
  left h hh i hi := by
    calc
      B.leftCoefficient h i = X.leftScalar * X.leftResidual h i := X.left h hh i hi
      _ = X.leftScalar * (Y.leftScalar * Y.leftResidual h i) := by
        rw [show X.leftResidual h i = Y.leftScalar * Y.leftResidual h i from Y.left h hh i hi]
      _ = _ := (mul_assoc _ _ _).symm
  right h hh i hi := by
    calc
      B.rightCoefficient h i = X.rightScalar * X.rightResidual h i := X.right h hh i hi
      _ = X.rightScalar * (Y.rightScalar * Y.rightResidual h i) := by
        rw [show X.rightResidual h i = Y.rightScalar * Y.rightResidual h i from Y.right h hh i hi]
      _ = _ := (mul_assoc _ _ _).symm

theorem trans_leaf : (X.trans Y).leaf = Y.leaf := by
  unfold trans leaf withConstantAtoms
  congr 1
  funext h
  simp only [star_mul']
  ring

@[simp] theorem trans_firstKernel : (X.trans Y).leaf.firstKernel = B.firstKernel := rfl
@[simp] theorem trans_secondKernel : (X.trans Y).leaf.secondKernel = B.secondKernel := rfl
@[simp] theorem trans_weight : (X.trans Y).leaf.weight = B.weight := rfl

end ConstantAtomExtraction
end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.withColumnConstants
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.withColumnConstants_rowBound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.stripColumnConstants
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.trans_leaf
