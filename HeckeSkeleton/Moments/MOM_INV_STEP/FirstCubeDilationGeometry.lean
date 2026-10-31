import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRows
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMaskGeometry

/-!
# The actual cube dilation and conductor norm budget

At every cube prime the dilation exponent, the active-conductor bit
and the retained-label bit are paid by twice the original multiplicity
and the two extracted squarefree bits. Multiplication gives an actual
ideal divisibility, hence the norm estimate used by the first row cap.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCubeDilationGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubeAlgebra CanonicalNormPools FirstPoissonNormalization ConductorMasks
open scoped Classical BigOperators nonZeroDivisors

theorem digit_budget (parityBit ε₁ ε₂ : Bool) :
    dilationExponent parityBit ε₁ ε₂ +
      (if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else 1) +
      bit (retained parityBit ε₁ ε₂) ≤ 2 + bit ε₁ + bit ε₂ := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem multiplicity_budget (m : ℕ) (hm : 0 < m) (ε₁ ε₂ : Bool) :
    dilationExponent (parity m) ε₁ ε₂ +
      (if conductorExponent (parity m) ε₁ ε₂ = 0 then 0 else 1) +
      bit (retained (parity m) ε₁ ε₂) ≤ 2 * m + bit ε₁ + bit ε₂ := by
  have h := digit_budget (parity m) ε₁ ε₂
  omega

theorem product_budget {R ι : Type*} [CommMonoid R]
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) :
    dilationLabel p B v ε₁ ε₂ *
      CubeAlgebra.primeProduct p B
        (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i) = 0 then 0 else 1) *
      jLabel p B v ε₁ ε₂ ∣
      CubeAlgebra.primeProduct p B v ^ 2 * aLabel p B ε₁ * aLabel p B ε₂ := by
  unfold dilationLabel jLabel aLabel CubeAlgebra.primeProduct
  rw [← Finset.prod_pow]
  repeat rw [← Finset.prod_mul_distrib]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  simp only [← pow_add, ← pow_mul]
  apply pow_dvd_pow
  simpa only [Nat.mul_comm] using multiplicity_budget (v i) (hv i hi) (ε₁ i) (ε₂ i)

theorem ideal_budget {R : Type*} [CommRing R] [IsDedekindDomain R]
    (b₁ b₂ : (Ideal R)⁰) (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    dilationLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁ b₂)
        (CubeLabels.cubeMultiplicity b₁ b₂) ε₁ ε₂ * CubeLabels.R1 b₁ b₂ ε₁ ε₂ *
      CubeLabels.J b₁ b₂ ε₁ ε₂ ∣
      (b₁.val * b₂.val) ^ 2 *
        aLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁ b₂) ε₁ *
        aLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁ b₂) ε₂ := by
  have hR : CubeLabels.R1 b₁ b₂ ε₁ ε₂ =
      CubeAlgebra.primeProduct HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁ b₂)
        (fun p => if conductorExponent (parity (CubeLabels.cubeMultiplicity b₁ b₂ p))
          (ε₁ p) (ε₂ p) = 0 then 0 else 1) := by
    simp only [CubeLabels.R1, IdealMobiusMask.primeProduct, Finset.prod_filter,
      CubeAlgebra.primeProduct]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases ht : conductorExponent (parity (CubeLabels.cubeMultiplicity b₁ b₂ p))
      (ε₁ p) (ε₂ p) = 0 <;> simp [ht]
  have hrec : CubeAlgebra.primeProduct HeightOneSpectrum.asIdeal
      (CubeLabels.cubePrimeSupport b₁ b₂) (CubeLabels.cubeMultiplicity b₁ b₂) =
      b₁.val * b₂.val := by
    change (idealOfPrimeExponents (primeExponents (b₁ * b₂))).val = _
    rw [idealOfPrimeExponents_primeExponents]
    rfl
  rw [hR, CubeLabels.J, ← hrec]
  exact product_budget HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁ b₂)
    (CubeLabels.cubeMultiplicity b₁ b₂) ε₁ ε₂ (CubeLabels.cubeMultiplicity_pos b₁ b₂)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem dilation_value (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    (CanonicalCubeLabels.dilation K S b₁ b₂ ε₁ ε₂).val.val =
      dilationLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁.val b₂.val)
        (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂ :=
  CanonicalCubeLabels.product_value K S b₁ b₂ _

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The dilation, active cube conductor and retained cube label are
the actual ones used by the first source coefficient identity. -/
theorem ideal_dvd (r₁ r₂ b₁ b₂ : Ext) :
    (FirstParentRows.cubeDilation K S r₁ r₂ b₁ b₂).val.val *
      (CanonicalGroupedGauss.cubeIdeal K S D r₁ r₂ b₁ b₂).val.val *
      (CanonicalCubeLabels.J K S b₁ b₂ (squarefreeBit K S r₁) (squarefreeBit K S r₂)).val.val ∣
      (b₁.val.val * b₂.val.val) ^ 2 *
        (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₁)).val.val *
        (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₂)).val.val := by
  change (CanonicalCubeLabels.dilation K S b₁ b₂
      (squarefreeBit K S r₁) (squarefreeBit K S r₂)).val.val * _ * _ ∣ _
  rw [dilation_value, CanonicalGroupedGauss.cubeIdeal_val, CanonicalCubeLabels.J_val,
    CanonicalCubeLabels.A_val, CanonicalCubeLabels.A_val]
  exact ideal_budget b₁.val b₂.val (squarefreeBit K S r₁) (squarefreeBit K S r₂)

theorem norm_bound (r₁ r₂ b₁ b₂ : Ext) :
    height K Sset (FirstParentRows.cubeDilation K S r₁ r₂ b₁ b₂) *
      cubeNorm K S D r₁ r₂ b₁ b₂ *
      ((CanonicalCubeLabels.J K S b₁ b₂
        (squarefreeBit K S r₁) (squarefreeBit K S r₂)).val.val.absNorm : ℝ) ≤
      (height K Sset b₁ * height K Sset b₂) ^ 2 *
        ((CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₁)).val.val.absNorm : ℝ) *
        ((CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₂)).val.val.absNorm : ℝ) := by
  have hnonzero : (b₁.val.val * b₂.val.val) ^ 2 *
      (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₁)).val.val *
      (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₂)).val.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (mul_ne_zero (nonZeroDivisors.coe_ne_zero b₁.val)
        (nonZeroDivisors.coe_ne_zero b₂.val)))
      (nonZeroDivisors.coe_ne_zero (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₁)).val))
      (nonZeroDivisors.coe_ne_zero (CanonicalCubeLabels.A K S b₁ b₂ (squarefreeBit K S r₂)).val)
  have h := FirstMaskGeometry.absNorm_le_of_dvd K _ _ hnonzero
    (ideal_dvd K S D r₁ r₂ b₁ b₂)
  simpa only [height, cubeNorm, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCubeDilationGeometry

end
