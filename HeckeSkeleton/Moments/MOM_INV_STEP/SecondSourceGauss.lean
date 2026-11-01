import HeckeSkeleton.Moments.MOM_INV_STEP.FirstInversePoisson
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualInverseFactors
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCrossLabels

/-!
# The genuine second source has conductor z₁z₂ and returns a₀

The source is the fresh pair of the first positive inverse norm, with
unit cube factors. Its actual primitive conductor and complementary
principal mask are computed from the original columns. The signed CRT
factorization has only the two coprime residual blocks; their cross
factor is proved to equal one.

The resulting Γ₁(z₁)Γ₅(z₂) multiplies the inverse-oriented coefficient
conj(A(x₁)) A(x₂). Applying the actual common/residual factorization in
that same orientation gives conj(a₀νG⁻¹(z₁)) a₀νG⁻¹(z₂). No coefficient,
conductor, or Gauss identity is an input to these conclusions.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceGauss

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global
open IdealMobiusMask FirstSourceDecomposition FirstInversePoisson
open ConductorMasks PrimitivePoissonSource PrimitiveFourier PrimitivePacketCRT
  CanonicalConductor CanonicalGroupedGauss
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "e" => unitIdeal K S

theorem leftIdeal_eq_residual (x₁ x₂ : Ext) :
    leftIdeal K S D x₁ x₂ e e = ActualInverseFactors.residual K Sset x₁ x₂ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [leftIdeal_val, u₁_eq_residual, ActualInverseFactors.residual_val]
  simp only [u, residualSupport, pairResidual, unitIdeal_nonzeroIdeal,
    one_mul, primeSupport, primeExponents_one, Finsupp.support_zero, Finset.sdiff_empty]

theorem rightIdeal_eq_residual (x₁ x₂ : Ext) :
    rightIdeal K S D x₁ x₂ e e = ActualInverseFactors.residual K Sset x₂ x₁ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [rightIdeal_val, u₂_eq_residual, ActualInverseFactors.residual_val]
  simp only [u, residualSupport, pairResidual, unitIdeal_nonzeroIdeal,
    one_mul, primeSupport, primeExponents_one, Finsupp.support_zero, Finset.sdiff_empty]

theorem cube_support_empty (x₁ x₂ : Ext) :
    (cubeBlock K S D x₁ x₂ e e).support = ∅ := by
  change SupportPartition.cubeActive _ _ _ _ = ∅
  rw [cubeActive_eq]
  simp only [CubeLabels.cubePrimeSupport, unitIdeal_nonzeroIdeal, one_mul,
    primeExponents_one, Finsupp.support_zero, Finset.filter_empty]

theorem cube_R1_one (x₁ x₂ : Ext) :
    CubeLabels.R1 (unitIdeal K S).val (unitIdeal K S).val
      (squarefreeBit K S x₁) (squarefreeBit K S x₂) = 1 := by
  simp only [CubeLabels.R1, CubeLabels.cubePrimeSupport, unitIdeal_nonzeroIdeal,
    one_mul, primeExponents_one, Finsupp.support_zero, Finset.filter_empty,
    IdealMobiusMask.primeProduct, Finset.prod_empty]

/-- The actual primitive conductor of the fresh inverse pair. -/
theorem primitive_conductor (x₁ x₂ : Ext) :
    primitiveIdeal (pairSupport K S D x₁ x₂ e e).support (pairExponent K S x₁ x₂ e e) =
      (ActualInverseFactors.residual K Sset x₁ x₂).val.val *
        (ActualInverseFactors.residual K Sset x₂ x₁).val.val := by
  rw [primitiveIdeal_eq_u₁_mul_u₂_mul_R1, cube_R1_one, mul_one,
    ← leftIdeal_val, ← rightIdeal_val, leftIdeal_eq_residual, rightIdeal_eq_residual]

/-- The entire remaining principal zero mask is the actual common
factor g′; no common-prime zeros have been discarded. -/
theorem principal_mask (x₁ x₂ : Ext) :
    principalIdeal (pairSupport K S D x₁ x₂ e e).support (pairExponent K S x₁ x₂ e e) =
      (ActualInverseFactors.common K Sset x₁ x₂).val.val := by
  rw [principalIdeal_eq_common_mul_cube, commonResidualIdeal_eq_C,
    ActualInverseFactors.common_val]
  simp only [C, commonSupport, cubePrincipalIdeal, CubeLabels.cubePrimeSupport,
    unitIdeal_nonzeroIdeal, one_mul, primeSupport, primeExponents_one,
    Finsupp.support_zero, Finset.sdiff_empty, Finset.filter_empty,
    IdealMobiusMask.primeProduct, Finset.prod_empty, mul_one, pairCommon]

theorem left_gauss (x₁ x₂ : Ext) :
    normalizedPrimitiveGauss K S D (leftBlock K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) =
      thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) 1 := by
  rw [← leftIdeal_eq_residual K S D x₁ x₂]
  apply normalizedPrimitiveGauss_uniform K S D _ _ 1
  intro p hp
  rw [left_digit K S D x₁ x₂ e e p (Finset.mem_filter.mp hp).1]
  rfl

theorem right_gauss (x₁ x₂ : Ext) :
    normalizedPrimitiveGauss K S D (rightBlock K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) =
      thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) 5 := by
  rw [← rightIdeal_eq_residual K S D x₁ x₂]
  apply normalizedPrimitiveGauss_uniform K S D _ _ 5
  intro p hp
  rw [right_digit K S D x₁ x₂ e e p (Finset.mem_filter.mp hp).1]
  rfl

theorem genuine_second_gauss (hallowed : AllowedGeneratorInput K Sset D) (x₁ x₂ : Ext) :
    normalizedPrimitiveGauss K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e) =
      thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) 1 *
        thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) 5 := by
  let L := leftBlock K S D x₁ x₂ e e
  let R := rightBlock K S D x₁ x₂ e e
  let t := pairExponent K S x₁ x₂ e e
  have hactive : activeSupport (pairSupport K S D x₁ x₂ e e).support t =
      activeSupport (unionBlock K S L R).support t := by
    rw [activeSupport_union, left_active, right_active, source_active_partition,
      cube_support_empty, Finset.union_empty]
  calc
    _ = normalizedPrimitiveGauss K S D (unionBlock K S L R) t :=
      normalizedGauss_eq_of_activeSupport_eq K S D _ _ t hactive
    _ = crossFactor K S D L R t * normalizedPrimitiveGauss K S D L t *
        normalizedPrimitiveGauss K S D R t :=
      normalizedPrimitiveGauss_union K S D hallowed L R
        (left_right_disjoint K S D x₁ x₂ e e) t
    _ = _ := by
      rw [ActualCrossLabels.residual_cross_eq_one K S D hallowed x₁ x₂ e e,
        left_gauss, right_gauss, one_mul]

/-- The true second finite Gauss factor acts in the inverse source's
conjugation order. The computed common factor cancels exactly, leaving
the two literal canonical child base coefficients. -/
theorem inverse_pair_returns_canonical (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K ν p)
    (x₁ x₂ : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val) :
    conj ((moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val) *
        ((moebius x₂.val.val : ℂ) * heckeIdealCoefficient K ν x₂.val) *
        normalizedPrimitiveGauss K S D (pairSupport K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e) =
      conj (CoefficientCycle.canonicalCoefficient K Sset D Λ
          (ActualInverseFactors.residual K Sset x₁ x₂) *
        heckeIdealCoefficient K (ν * G⁻¹) (ActualInverseFactors.residual K Sset x₁ x₂).val) *
      (CoefficientCycle.canonicalCoefficient K Sset D Λ
          (ActualInverseFactors.residual K Sset x₂ x₁) *
        heckeIdealCoefficient K (ν * G⁻¹) (ActualInverseFactors.residual K Sset x₂ x₁).val) := by
  rw [genuine_second_gauss K S D hallowed]
  have hconj : conj (thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) 5) =
      thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) 1 := by
    rw [SexticEvenness.thetaGamma_five_eq_conj, Complex.conj_conj]
  calc
    _ = ((moebius x₂.val.val : ℂ) * heckeIdealCoefficient K ν x₂.val *
          thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₂ x₁) 5) *
        conj ((moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val *
          thetaGamma K Sset D (ActualInverseFactors.residual K Sset x₁ x₂) 5) := by
      simp only [map_mul, hconj]
      ring
    _ = _ := by
      rw [ActualInverseFactors.actual_pair_coefficient K Sset D hcal ν hν x₂ x₁ hx₂ hx₁]
      exact mul_comm _ _

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceGauss

end
