import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourcePartition
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale

/-!
# Exact physical normalization of the first retained source

The original Poisson prefactor and the actual finite Fourier coefficient
supply the inverse square-root norm factors in both residual columns.
The common radius is computed from the actual frequency ideal and the
frozen cube conductor; no physical scale identity is an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstPoissonNormalization

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
open PrimitivePoissonSource PrimitiveFourier CanonicalGroupedGauss CanonicalConductor ConductorMasks
  FirstSourceColumns FirstSourceFrozen CanonicalFirstEnergy FirstSourceEnergy
open ActualPoissonScale
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

def cubeNorm (n₁ n₂ b₁ b₂ : Ext) : ℝ :=
  ((cubeIdeal K S D n₁ n₂ b₁ b₂).val.val.absNorm : ℝ)

theorem cubeNorm_pos (n₁ n₂ b₁ b₂ : Ext) : 0 < cubeNorm K S D n₁ n₂ b₁ b₂ := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (cubeIdeal K S D n₁ n₂ b₁ b₂).val

theorem cubeNorm_eq (n₁ n₂ r₁ r₂ b₁ b₂ : Ext)
    (h : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂) :
    cubeNorm K S D n₁ n₂ b₁ b₂ = cubeNorm K S D r₁ r₂ b₁ b₂ := by
  obtain ⟨ha, ht⟩ := cube_packet_data K S D n₁ n₂ r₁ r₂ b₁ b₂ h
  exact congrArg (fun P : Finset (HeightOneSpectrum (𝓞 K)) =>
    ((IdealMobiusMask.primeProduct P).absNorm : ℝ)) ha

theorem conductorNorm (n₁ n₂ b₁ b₂ : Ext) :
    ((primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂)).absNorm : ℝ) =
      ((residualIdeal K S D n₁ n₂ b₁ b₂ false).val.val.absNorm : ℝ) *
        ((residualIdeal K S D n₁ n₂ b₁ b₂ true).val.val.absNorm : ℝ) *
          cubeNorm K S D n₁ n₂ b₁ b₂ := by
  rw [primitiveIdeal_eq_u₁_mul_u₂_mul_R1]
  simp only [map_mul, Nat.cast_mul, residualIdeal, Bool.false_eq_true,
    if_false, if_true, leftIdeal_val, rightIdeal_val, cubeNorm, cubeIdeal_val]

def outerFactor (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ : Ext) : ℝ :=
  fieldConstant K / (r.val * (sIntegerElementNorm K Sset d).val *
    Real.sqrt (cubeNorm K S D r₁ r₂ b₁ b₂))

theorem outerFactor_nonneg (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ : Ext) : 0 ≤ outerFactor K S D r d r₁ r₂ b₁ b₂ :=
  div_nonneg (fieldConstant_nonneg K) (by
    exact (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property)
      (Real.sqrt_pos.mpr (cubeNorm_pos K S D r₁ r₂ b₁ b₂))).le)

private theorem scalar_normalization (C r d x y c : ℝ) (A : ℂ)
    (hr : 0 < r) (hd : 0 < d) (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) :
    ((r * d : ℝ) : ℂ)⁻¹ * (C : ℂ) * ((x * y * c : ℝ) : ℂ)⁻¹ * A =
      ((C / (r * d * Real.sqrt c) : ℝ) : ℂ) *
        (A / (Real.sqrt (x * y * c) : ℂ)) *
          (Real.sqrt x : ℂ)⁻¹ * conj ((Real.sqrt y : ℂ)⁻¹) := by
  have hx0 : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have hy0 : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hy).ne'
  have hc0 : (Real.sqrt c : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hx2 : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast Real.sq_sqrt hx.le
  have hy2 : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast Real.sq_sqrt hy.le
  have hc2 : (Real.sqrt c : ℂ) ^ 2 = (c : ℂ) := by exact_mod_cast Real.sq_sqrt hc.le
  rw [Real.sqrt_mul (mul_nonneg hx.le hy.le), Real.sqrt_mul hx.le]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, map_inv₀, Complex.conj_ofReal]
  rw [← hx2, ← hy2, ← hc2]
  field_simp [hx0, hy0, hc0, hr0, hd0] <;> ring

/-- Signed equality, retaining the actual divisor phase even at nonunits. -/
theorem prefactor_fourier (n₁ n₂ b₁ b₂ : Ext)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (a : OS) :
    sIntegerMaskPoissonFactor K S
        (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂))
        (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂)) r d *
      sIntegerPeriodicDivisorFourier K Sset D.different_outside
        (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂))
        (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂))
        (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂)) d.val (Ideal.Quotient.mk _ a) =
      (outerFactor K S D r d n₁ n₂ b₁ b₂ : ℂ) *
        pairFourier K S D n₁ n₂ b₁ b₂ d.val a *
          normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ false).val *
          conj (normWeight K (residualIdeal K S D n₁ n₂ b₁ b₂ true).val) := by
  unfold sIntegerMaskPoissonFactor outerFactor pairFourier normWeight
  simp only [sIntegerMaskDilationRadius, primitiveModulus_norm]
  simp only [conductorNorm]
  apply scalar_normalization
  · exact r.property
  · exact (sIntegerElementNorm K Sset d).property
  · exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ false).val
  · exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ true).val
  · exact cubeNorm_pos K S D n₁ n₂ b₁ b₂

def outerRadius (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ z : Ext) (X Y : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨(z.val.val.absNorm : ℝ) /
    (r.val * (sIntegerElementNorm K Sset d).val * cubeNorm K S D r₁ r₂ b₁ b₂ * X.val * Y.val),
    div_pos (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors z.val)
      (mul_pos (mul_pos (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property)
        (cubeNorm_pos K S D r₁ r₂ b₁ b₂)) X.property) Y.property)⟩

theorem dualRadius_normalized (n₁ n₂ r₁ r₂ b₁ b₂ z : Ext)
    (hslice : SameExtraction K S n₁ n₂ r₁ r₂ b₁ b₂)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (X Y : {r : ℝ // 0 < r}) :
    (sIntegerMaskDualRadius K S
      (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂)) r d).val * (z.val.val.absNorm : ℝ) =
      (outerRadius K S D r d r₁ r₂ b₁ b₂ z X Y).val /
        ((normScale K X (residualIdeal K S D n₁ n₂ b₁ b₂ false).val).val *
          (normScale K Y (residualIdeal K S D n₁ n₂ b₁ b₂ true).val).val) := by
  rw [primitive_dual_radius, conductorNorm, cubeNorm_eq K S D n₁ n₂ r₁ r₂ b₁ b₂ hslice]
  simp only [outerRadius, normScale]
  have hu : ((residualIdeal K S D n₁ n₂ b₁ b₂ false).val.val.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ false).val).ne'
  have hv : ((residualIdeal K S D n₁ n₂ b₁ b₂ true).val.val.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
      (residualIdeal K S D n₁ n₂ b₁ b₂ true).val).ne'
  field_simp [r.property.ne', (sIntegerElementNorm K Sset d).property.ne',
    (cubeNorm_pos K S D r₁ r₂ b₁ b₂).ne', X.property.ne', Y.property.ne', hu, hv] <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstPoissonNormalization

end

