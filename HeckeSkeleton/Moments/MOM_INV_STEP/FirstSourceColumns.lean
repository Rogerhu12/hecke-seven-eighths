import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCrossLabels
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualInverseFactors
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGaussCalibration

/-!
# The actual first-source coefficients and their residual columns

The common and residual ideals are computed from the original source.
The canonical source coefficient is then calibrated on that actual
factorization. The original label contributes both an explicit outer
factor and the square in the new inverse row. A mask-divisor character
is retained as a moving-column factor until an explicit absorption
identity applies to it.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open PrimitivePoissonSource PrimitiveFourier CanonicalGroupedGauss CanonicalConductor
  ActualCrossLabels
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S

def commonIdeal (n₁ n₂ b₁ b₂ : Ext) : Ext :=
  ActualInverseFactors.productExterior K Sset
    (FirstSourceDecomposition.commonSupport n₁.val n₂.val b₁.val b₂.val) (by
      intro p hp
      exact n₁.property p ((FirstSourceDecomposition.mem_primeSupport n₁.val p).mp
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp hp).1).1))

@[simp] theorem commonIdeal_val (n₁ n₂ b₁ b₂ : Ext) :
    (commonIdeal K S n₁ n₂ b₁ b₂).val.val =
      FirstSourceDecomposition.C n₁.val n₂.val b₁.val b₂.val := rfl

def commonFactor (n₁ n₂ b₁ b₂ : Ext) : E :=
  CanonicalIdealRow.ofExterior K S (commonIdeal K S n₁ n₂ b₁ b₂)

def sourceIdeal (n₁ n₂ : Ext) (side : Bool) : Ext := if side then n₂ else n₁

def extractedFactor (n₁ n₂ b₁ b₂ : Ext) (side : Bool) : E :=
  CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S (sourceIdeal K S n₁ n₂ side)) *
    commonFactor K S n₁ n₂ b₁ b₂

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def residualIdeal (n₁ n₂ b₁ b₂ : Ext) (side : Bool) : Ext :=
  if side then rightIdeal K S D n₁ n₂ b₁ b₂ else leftIdeal K S D n₁ n₂ b₁ b₂

theorem extractedFactor_val (n₁ n₂ b₁ b₂ : Ext) (side : Bool) :
    (extractedFactor K S n₁ n₂ b₁ b₂ side).val.val =
      FirstSourceDecomposition.A (sourceIdeal K S n₁ n₂ side).val b₁.val b₂.val *
        commonResidualIdeal K S D n₁ n₂ b₁ b₂ := by
  change (CanonicalCubeLabels.A K S b₁ b₂
    (squarefreeBit K S (sourceIdeal K S n₁ n₂ side))).val.val *
      (commonIdeal K S n₁ n₂ b₁ b₂).val.val = _
  rw [CanonicalCubeLabels.A_val_eq_extracted, commonIdeal_val, commonResidualIdeal_eq_C]

theorem source_factorization (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val) (side : Bool) :
    exteriorMul K Sset
      (CanonicalIdealRow.toExterior K S (extractedFactor K S n₁ n₂ b₁ b₂ side))
      (residualIdeal K S D n₁ n₂ b₁ b₂ side) = sourceIdeal K S n₁ n₂ side := by
  apply Subtype.ext
  apply Subtype.ext
  change (extractedFactor K S n₁ n₂ b₁ b₂ side).val.val *
    (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val = (sourceIdeal K S n₁ n₂ side).val.val
  rw [extractedFactor_val K S D]
  cases side with
  | false =>
    simp only [sourceIdeal, residualIdeal, Bool.false_eq_true, if_false, leftIdeal_val]
    exact (first_source_decomposition K S D n₁ n₂ b₁ b₂ hn₁ hn₂).1.symm
  | true =>
    simp only [sourceIdeal, residualIdeal, if_true, rightIdeal_val]
    exact (first_source_decomposition K S D n₁ n₂ b₁ b₂ hn₁ hn₂).2.symm

theorem residual_squarefree (n₁ n₂ b₁ b₂ : Ext) (side : Bool) :
    Squarefree (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val := by
  cases side with
  | false => exact ConductorMasks.primitiveIdeal_squarefree _ _
  | true => exact ConductorMasks.primitiveIdeal_squarefree _ _

theorem residual_coprime_cube (n₁ n₂ b₁ b₂ : Ext) (side : Bool) :
    IsCoprime (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val
      (b₁.val.val * b₂.val.val).radical := by
  have h := (first_source_coprime K S D n₁ n₂ b₁ b₂).2.2
  cases side with
  | false =>
    change IsCoprime (leftIdeal K S D n₁ n₂ b₁ b₂).val.val _
    rw [leftIdeal_val]
    exact h.of_mul_left_left.of_mul_left_right
  | true =>
    change IsCoprime (rightIdeal K S D n₁ n₂ b₁ b₂).val.val _
    rw [rightIdeal_val]
    exact h.of_mul_left_right

theorem common_coprime_residual (n₁ n₂ b₁ b₂ : Ext) (side : Bool) :
    IsCoprime (commonFactor K S n₁ n₂ b₁ b₂).val.val
      (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val := by
  have h := (first_source_coprime K S D n₁ n₂ b₁ b₂).2.1
  have hC : (commonFactor K S n₁ n₂ b₁ b₂).val.val =
      commonResidualIdeal K S D n₁ n₂ b₁ b₂ := by
    rw [commonResidualIdeal_eq_C]
    rfl
  rw [hC]
  cases side with
  | false =>
    change IsCoprime _ (leftIdeal K S D n₁ n₂ b₁ b₂).val.val
    rw [leftIdeal_val]
    exact h.of_mul_right_left
  | true =>
    change IsCoprime _ (rightIdeal K S D n₁ n₂ b₁ b₂).val.val
    rw [rightIdeal_val]
    exact h.of_mul_right_right

theorem extracted_coprime_residual (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val) (side : Bool) :
    IsCoprime (extractedFactor K S n₁ n₂ b₁ b₂ side).val.val
      (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val := by
  have hn : Squarefree (sourceIdeal K S n₁ n₂ side).val.val := by
    cases side <;> assumption
  have hd : (CanonicalCubeLabels.A K S b₁ b₂
      (squarefreeBit K S (sourceIdeal K S n₁ n₂ side))).val.val ∣
      (b₁.val.val * b₂.val.val).radical := by
    rw [CanonicalCubeLabels.A_val_eq_gcd K S (sourceIdeal K S n₁ n₂ side) b₁ b₂ hn]
    exact gcd_dvd_right _ _
  exact ((residual_coprime_cube K S D n₁ n₂ b₁ b₂ side).symm.of_isCoprime_of_dvd_left hd).mul_left
    (common_coprime_residual K S D n₁ n₂ b₁ b₂ side)

def sourceCoefficient (Λ ν : HeckeCharacter K) (n : Ext) (f : E) : ℂ :=
  CoefficientCycle.canonicalCoefficient K Sset D Λ n * heckeIdealCoefficient K ν n.val *
    idealSymbol K Sset D n (CanonicalIdealRow.generator K S D f) ^ 4

def outerCoefficient (Λ ν : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (side : Bool) (f : E) : ℂ :=
  sourceCoefficient K S D Λ ν
    (CanonicalIdealRow.toExterior K S (extractedFactor K S n₁ n₂ b₁ b₂ side)) f

/-- The canonical inverse part after the old fourth-power label has
entered the row. The q₀ zero remains a literal coprimality mask. -/
def inverseCoefficient (ν G : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (side : Bool) (f z : E) : ℂ :=
  let u := residualIdeal K S D n₁ n₂ b₁ b₂ side
  ((UniqueFactorizationMonoid.moebius u.val.val : ℂ) *
      heckeIdealCoefficient K ν u.val * heckeIdealCoefficient K G u.val) *
    (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D
      (commonFactor K S n₁ n₂ b₁ b₂ *
        CanonicalCubeLabels.J K S b₁ b₂ (squarefreeBit K S n₁) (squarefreeBit K S n₂))) ^ 4 *
      (if IsCoprime u.val.val
        (CanonicalCubeLabels.q0 K S b₁ b₂ (squarefreeBit K S n₁) (squarefreeBit K S n₂)).val.val
          then 1 else 0)) *
    conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D
      (z * f ^ 2 * CanonicalCubeLabels.dilation K S b₁ b₂
        (squarefreeBit K S n₁) (squarefreeBit K S n₂))))

/-- A mask-divisor numerator is still a moving-column character. This
definition deliberately does not absorb it into the outer coefficient. -/
def divisorInverseCoefficient (ν G : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (side : Bool) (f z : E) (d : OS) : ℂ :=
  idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side) d *
    inverseCoefficient K S D ν G n₁ n₂ b₁ b₂ side f z

/-- The original n, rather than a supplied factorization, enters this
coefficient identity. Its old label is split by proved denominator
multiplicativity before its residual part enters the new row. -/
theorem source_column (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (side : Bool) (f z : E) :
    sourceCoefficient K S D Λ ν (sourceIdeal K S n₁ n₂ side) f *
      thetaGamma K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side) 1 *
      idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) side)) *
      conj (idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side)
        (CanonicalIdealRow.generator K S D z)) =
      outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ side f *
        inverseCoefficient K S D ν G n₁ n₂ b₁ b₂ side f z := by
  have hc := CanonicalGaussCalibration.first_cube_coefficient_with_common_factor
    K S D hallowed hcal ν (residualIdeal K S D n₁ n₂ b₁ b₂ side)
      (residual_squarefree K S D n₁ n₂ b₁ b₂ side)
      (CanonicalCubeLabels.prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂)
      (CubeLabels.cubeMultiplicity_pos b₁.val b₂.val) side
      (commonFactor K S n₁ n₂ b₁ b₂) f z
      (by
        convert extracted_coprime_residual K S D n₁ n₂ b₁ b₂ hn₁ hn₂ side using 1 <;>
          cases side <;> rfl)
  have hL : CubeAlgebra.aLabel (CanonicalCubeLabels.prime K S)
      (CubeLabels.cubePrimeSupport b₁.val b₂.val)
      (if side then squarefreeBit K S n₂ else squarefreeBit K S n₁) *
        commonFactor K S n₁ n₂ b₁ b₂ = extractedFactor K S n₁ n₂ b₁ b₂ side := by
    cases side <;> rfl
  have hmask : IsCoprime (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val
      (CubeAlgebra.cubeRadical (CanonicalCubeLabels.prime K S)
        (CubeLabels.cubePrimeSupport b₁.val b₂.val)).val.val := by
    change IsCoprime _ (CanonicalCubeLabels.radical K S b₁ b₂).val.val
    rw [CanonicalCubeLabels.radical_val]
    exact residual_coprime_cube K S D n₁ n₂ b₁ b₂ side
  simp only [hL, if_pos hmask, one_mul,
    source_factorization K S D n₁ n₂ b₁ b₂ hn₁ hn₂ side] at hc
  have hf : idealSymbol K Sset D (sourceIdeal K S n₁ n₂ side)
      (CanonicalIdealRow.generator K S D f) ^ 4 =
    idealSymbol K Sset D (CanonicalIdealRow.toExterior K S
      (extractedFactor K S n₁ n₂ b₁ b₂ side)) (CanonicalIdealRow.generator K S D f) ^ 4 *
      idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side)
        (CanonicalIdealRow.generator K S D f) ^ 4 := by
    rw [← source_factorization K S D n₁ n₂ b₁ b₂ hn₁ hn₂ side,
      ThetaGaussCRT.idealSymbol_mul_denominator, mul_pow]
  have hc' := congrArg (fun w : ℂ =>
    idealSymbol K Sset D (CanonicalIdealRow.toExterior K S
      (extractedFactor K S n₁ n₂ b₁ b₂ side)) (CanonicalIdealRow.generator K S D f) ^ 4 * w) hc
  simp only [outerCoefficient, sourceCoefficient, inverseCoefficient]
  rw [hf]
  convert hc' using 1 <;>
    simp only [CanonicalCubeLabels.crt, CanonicalCubeLabels.J, CanonicalCubeLabels.q0,
      CanonicalCubeLabels.dilation, CanonicalIdealRow.generator,
      CanonicalIdealRow.toExterior_val] <;> ring

/-- The same genuine column identity keeps an arbitrary mask-divisor
character in the moving residual column. It is never made an outer scalar. -/
theorem source_column_with_divisor (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (side : Bool) (f z : E) (d : OS) :
    sourceCoefficient K S D Λ ν (sourceIdeal K S n₁ n₂ side) f *
      thetaGamma K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side) 1 *
      idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) side)) *
      idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side) d *
      conj (idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side)
        (CanonicalIdealRow.generator K S D z)) =
      outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ side f *
        divisorInverseCoefficient K S D ν G n₁ n₂ b₁ b₂ side f z d := by
  have h := congrArg (fun w : ℂ =>
    idealSymbol K Sset D (residualIdeal K S D n₁ n₂ b₁ b₂ side) d * w)
      (source_column K S D hallowed hcal ν n₁ n₂ b₁ b₂ hn₁ hn₂ side f z)
  unfold divisorInverseCoefficient
  convert h using 1 <;> ring

/-- The actual pair packet, evaluated at any S-integer, splits into
its two residual rows and its actual cube coefficient, including zeros. -/
theorem primitive_pair_coefficient (n₁ n₂ b₁ b₂ : Ext) (a : OS) :
    primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) =
      idealSymbol K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) a *
        conj (idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) a) *
        primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) := by
  have hprod : primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) =
    primitiveCoefficient K S D (leftBlock K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) *
      primitiveCoefficient K S D (rightBlock K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) *
      primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) := by
    simp only [PrimitivePacketCRT.primitiveCoefficient_mk_eq_product,
      left_active, right_active, cube_active]
    rw [source_active_partition,
      Finset.prod_union (residuals_cube_disjoint K S D n₁ n₂ b₁ b₂),
      Finset.prod_union (left_right_disjoint K S D n₁ n₂ b₁ b₂)]
  have hleft : ∀ p ∈ ConductorMasks.activeSupport (leftBlock K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂), (pairExponent K S n₁ n₂ b₁ b₂ p).val = 1 := by
    intro p hp
    rw [left_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  have hright : ∀ p ∈ ConductorMasks.activeSupport (rightBlock K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂), (pairExponent K S n₁ n₂ b₁ b₂ p).val = 5 := by
    intro p hp
    rw [right_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  rw [hprod, PrimitivePacketCRT.primitiveCoefficient_uniform K S D _ _ 1 hleft,
    PrimitivePacketCRT.primitiveCoefficient_uniform K S D _ _ 5 hright, pow_one]
  have hz : idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) a ^ 6 = 0 ∨
      idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) a ^ 6 = 1 :=
    LocalSource.actualRow_zero_or_one K Sset D.root6 D.primitive6 D.embedding
      (rightIdeal K S D n₁ n₂ b₁ b₂).val.val
      (nonZeroDivisors.coe_ne_zero (rightIdeal K S D n₁ n₂ b₁ b₂).val)
      (rightIdeal K S D n₁ n₂ b₁ b₂).property
      (fun p hp => D.away_six p ((rightIdeal K S D n₁ n₂ b₁ b₂).property p hp)) a
  change idealSymbol K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) a *
    idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) a ^ 5 *
    primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a) = _
  rw [GaussConjugation.pow_five_eq_conj _ hz]

/-- The actual finite divisor Fourier coefficient with its conductor
square-root normalization. The divisor may meet the active conductor. -/
def pairFourier (n₁ n₂ b₁ b₂ : Ext) (d a : OS) : ℂ :=
  let B := pairSupport K S D n₁ n₂ b₁ b₂
  let t := pairExponent K S n₁ n₂ b₁ b₂
  sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) d (Ideal.Quotient.mk _ a) /
    (Real.sqrt ((ConductorMasks.primitiveIdeal B.support t).absNorm : ℝ) : ℂ)

theorem pairFourier_eq (n₁ n₂ b₁ b₂ : Ext) (d a : OS) :
    pairFourier K S D n₁ n₂ b₁ b₂ d a =
      primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ d) *
        conj (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a)) *
        normalizedPrimitiveGauss K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) := by
  unfold pairFourier
  dsimp only
  rw [divisor_fourier]
  simp only [normalizedPrimitiveGauss, Complex.star_def, div_eq_mul_inv]
  ring

/-- The only Gauss and dual-row factor left outside the residual
columns is the actual cube packet, with both its possible zeros kept. -/
def cubeFourierScalar (n₁ n₂ b₁ b₂ : Ext) (d a : OS) : ℂ :=
  primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ d) *
    conj (primitiveCoefficient K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) (Ideal.Quotient.mk _ a)) *
    normalizedPrimitiveGauss K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂)

theorem idealSymbol_norm_le_one (I : Ext) (a : OS) :
    ‖idealSymbol K Sset D I a‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K Sset D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem sourceCoefficient_norm_le_one {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (n : Ext) (hn : Squarefree n.val.val) (f : E) :
    ‖sourceCoefficient K S D Λ ν n f‖ ≤ 1 := by
  simp only [sourceCoefficient, norm_mul, norm_pow,
    CoefficientCycle.canonicalCoefficient_norm hcal n hn, one_mul]
  exact mul_le_one₀ (norm_heckeIdealCoefficient_le_one K ν n.val)
    (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _)
      (idealSymbol_norm_le_one K S D n _))

theorem outerCoefficient_norm_le_one {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K Sset D Λ G) (ν : HeckeCharacter K)
    (n₁ n₂ b₁ b₂ : Ext) (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (side : Bool) (f : E) :
    ‖outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ side f‖ ≤ 1 := by
  have hn : Squarefree (sourceIdeal K S n₁ n₂ side).val.val := by cases side <;> assumption
  have he := congrArg (fun I : Ext => I.val.val)
    (source_factorization K S D n₁ n₂ b₁ b₂ hn₁ hn₂ side)
  change (extractedFactor K S n₁ n₂ b₁ b₂ side).val.val *
    (residualIdeal K S D n₁ n₂ b₁ b₂ side).val.val = _ at he
  rw [← he] at hn
  exact sourceCoefficient_norm_le_one K S D hcal ν _ hn.of_mul_left f

theorem primitiveCoefficient_norm_le_one (B : ActualFiniteSource.PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (q : PrincipalQuotient K S D B t) :
    ‖primitiveCoefficient K S D B t q‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [PrimitivePacketCRT.primitiveCoefficient_mk_eq_product, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro p hp
  rw [norm_pow, ActualCrossLabels.primeScalar_eq_idealSymbol K S D
    ⟨p, B.outside p (Finset.mem_filter.mp hp).1⟩ a]
  exact pow_le_one₀ (norm_nonneg _) (idealSymbol_norm_le_one K S D _ a)

/-- Taking absolute values only after the exact source identity costs
at most one for the cube packet, including its actual bad-prime zeros. -/
theorem cubeFourierScalar_norm_le_one (n₁ n₂ b₁ b₂ : Ext) (d a : OS) :
    ‖cubeFourierScalar K S D n₁ n₂ b₁ b₂ d a‖ ≤ 1 := by
  simp only [cubeFourierScalar, norm_mul, Complex.norm_conj,
    normalizedPrimitiveGauss_norm, mul_one]
  exact mul_le_one₀ (primitiveCoefficient_norm_le_one K S D _ _ _)
    (norm_nonneg _) (primitiveCoefficient_norm_le_one K S D _ _ _)

/-- The first Poisson coefficient multiplied by the two original
canonical source coefficients. No Gauss-factorization or source-column
identification is assumed. The arbitrary divisor d remains explicitly
inside each residual column. -/
theorem first_source_pair (hallowed : AllowedGeneratorInput K Sset D)
    {Λ G : HeckeCharacter K} (hcal : ThetaCalibrationInput K Sset D Λ G)
    (ν : HeckeCharacter K) (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (f₁ f₂ z : E) (d : OS) :
    sourceCoefficient K S D Λ ν n₁ f₁ *
      conj (sourceCoefficient K S D Λ ν n₂ f₂) *
      pairFourier K S D n₁ n₂ b₁ b₂ d (CanonicalIdealRow.generator K S D z) =
    cubeFourierScalar K S D n₁ n₂ b₁ b₂ d (CanonicalIdealRow.generator K S D z) *
      (outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ false f₁ *
        divisorInverseCoefficient K S D ν G n₁ n₂ b₁ b₂ false f₁ z d) *
      conj (outerCoefficient K S D Λ ν n₁ n₂ b₁ b₂ true f₂ *
        divisorInverseCoefficient K S D ν G n₁ n₂ b₁ b₂ true f₂ z d) := by
  have h₁ := source_column_with_divisor K S D hallowed hcal ν
    n₁ n₂ b₁ b₂ hn₁ hn₂ false f₁ z d
  have h₂ := source_column_with_divisor K S D hallowed hcal ν
    n₁ n₂ b₁ b₂ hn₁ hn₂ true f₂ z d
  simp only [sourceIdeal, residualIdeal, Bool.false_eq_true, if_false, if_true] at h₁ h₂
  rw [← h₁, ← h₂, pairFourier_eq,
    primitive_pair_coefficient K S D n₁ n₂ b₁ b₂ d,
    primitive_pair_coefficient K S D n₁ n₂ b₁ b₂ (CanonicalIdealRow.generator K S D z),
    pair_normalizedGauss_eq_column_factors K S D hallowed]
  simp only [cubeFourierScalar, Complex.star_def, map_mul, starRingEnd_self_apply]
  ring

/-- When a selected divisor is actually a factor of the common label,
its residual character moves to the row with exponent one and removes
that divisor from the label. The identity remains valid at zeros. -/
theorem absorb_common_divisor (hallowed : AllowedGeneratorInput K Sset D)
    (u : Ext) (C d J y : E) :
    idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (C * d * J)) ^ 4 *
      idealSymbol K Sset D u (CanonicalIdealRow.generator K S D d) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D y)) =
    idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (C * J)) ^ 4 *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (d * y))) := by
  let χ := CanonicalIdealRow.row K S D hallowed u
  have hfive : χ d ^ 5 = conj (χ d) :=
    GaussConjugation.pow_five_eq_conj _ (CanonicalIdealRow.row_zero_or_one K S D hallowed u d)
  simp only [← CanonicalIdealRow.row_apply K S D hallowed]
  change χ (C * d * J) ^ 4 * χ d * conj (χ y) =
    χ (C * J) ^ 4 * conj (χ (d * y))
  simp only [map_mul, mul_pow]
  calc
    _ = χ C ^ 4 * χ J ^ 4 * χ d ^ 5 * conj (χ y) := by ring
    _ = _ := by rw [hfive]; ring

/-- An arbitrary selected divisor can also be absorbed into the row,
but its fifth power is explicit. This formula makes its norm cost
visible; it does not assert that that cost fits the descent budget. -/
theorem absorb_arbitrary_divisor (hallowed : AllowedGeneratorInput K Sset D)
    (u : Ext) (d y : E) :
    idealSymbol K Sset D u (CanonicalIdealRow.generator K S D d) *
      conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D y)) =
    conj (idealSymbol K Sset D u (CanonicalIdealRow.generator K S D (y * d ^ 5))) := by
  let χ := CanonicalIdealRow.row K S D hallowed u
  have hfive : χ d ^ 5 = conj (χ d) :=
    GaussConjugation.pow_five_eq_conj _ (CanonicalIdealRow.row_zero_or_one K S D hallowed u d)
  simp only [← CanonicalIdealRow.row_apply K S D hallowed]
  change χ d * conj (χ y) = conj (χ (y * d ^ 5))
  rw [map_mul, map_pow, hfive, map_mul, starRingEnd_self_apply, mul_comm]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceColumns
