import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalConductor
import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitiveFourier

/-!
# The exact principal locus and its surviving zero frequency

The active conductor is the actual ideal `u₁ * u₂ * R₁`. It is trivial
exactly when all three factors are the unit ideal. On this locus the
primitive coefficient, its Gauss factor and every divisor Fourier
coefficient are one. The original source still carries its full
complementary coprimality mask. Thus the zero frequency is retained as an
explicit principal term, rather than discarded by a nonprincipal argument.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalLocus

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
open scoped Classical BigOperators nonZeroDivisors

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem primeProduct_eq_one_iff (B : Finset (HeightOneSpectrum R)) :
    IdealMobiusMask.primeProduct B = 1 ↔ B = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hd : p.asIdeal ∣ IdealMobiusMask.primeProduct B :=
      Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum R => q.asIdeal) hp
    rw [h] at hd
    exact p.irreducible.not_isUnit (isUnit_of_dvd_one hd)
  · rintro rfl
    simp only [IdealMobiusMask.primeProduct, Finset.prod_empty]

theorem ideal_mul_eq_one_iff (I J : Ideal R) :
    I * J = 1 ↔ I = 1 ∧ J = 1 := by
  constructor
  · intro h
    constructor
    · rw [Ideal.one_eq_top]
      apply le_antisymm le_top
      simpa only [h, Ideal.one_eq_top] using (Ideal.mul_le_left : I * J ≤ I)
    · rw [Ideal.one_eq_top]
      apply le_antisymm le_top
      simpa only [h, Ideal.one_eq_top] using (Ideal.mul_le_right : I * J ≤ J)
  · rintro ⟨rfl, rfl⟩
    exact one_mul _

theorem activeSupport_eq_empty_iff_primitiveIdeal_eq_one
    (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6) :
    activeSupport B t = ∅ ↔ primitiveIdeal B t = 1 :=
  (primeProduct_eq_one_iff (activeSupport B t)).symm

theorem principalIdeal_eq_period_of_empty
    (B : Finset (HeightOneSpectrum R)) (t : HeightOneSpectrum R → ZMod 6)
    (hempty : activeSupport B t = ∅) :
    principalIdeal B t = IdealMobiusMask.primeProduct B := by
  have h := support_union B t
  rw [hempty, Finset.empty_union] at h
  exact congrArg IdealMobiusMask.primeProduct h

end Ideals

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The principal locus is expressed in the actual manuscript labels,
not in an independently supplied conductor. -/
theorem pair_active_empty_iff (n₁ n₂ b₁ b₂ : Ext) :
    activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) = ∅ ↔
      CanonicalConductor.u₁ K S D n₁ n₂ b₁ b₂ = 1 ∧
      CanonicalConductor.u₂ K S D n₁ n₂ b₁ b₂ = 1 ∧
      CubeLabels.R1 b₁.val b₂.val
        (CanonicalConductor.squarefreeBit K S n₁)
        (CanonicalConductor.squarefreeBit K S n₂) = 1 := by
  rw [activeSupport_eq_empty_iff_primitiveIdeal_eq_one,
    CanonicalConductor.primitiveIdeal_eq_u₁_mul_u₂_mul_R1]
  simp only [ideal_mul_eq_one_iff, and_assoc]

/-- With empty active support the actual primitive quotient function
is identically one, including at its zero element. -/
theorem primitiveCoefficient_eq_one_of_empty (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅)
    (q : PrincipalQuotient K S D B t) :
    primitiveCoefficient K S D B t q = 1 := by
  letI : IsEmpty (activeSupport B.support t) :=
    ⟨fun p => Finset.notMem_empty p.val (hempty ▸ p.property)⟩
  rw [primitiveCoefficient_eq_tensor]
  simp only [ProductGauss.tensorCoefficient, Finset.univ_eq_empty, Finset.prod_empty]

theorem primitiveGauss_eq_one_of_empty (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅) :
    primitiveGauss K S D B t = 1 := by
  letI : IsEmpty (activeSupport B.support t) :=
    ⟨fun p => Finset.notMem_empty p.val (hempty ▸ p.property)⟩
  simp only [primitiveGauss, ProductGauss.gaussProduct,
    Finset.univ_eq_empty, Finset.prod_empty]

theorem normalizedPrimitiveGauss_eq_one_of_empty (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅) :
    normalizedPrimitiveGauss K S D B t = 1 := by
  rw [normalizedPrimitiveGauss, primitiveGauss_eq_one_of_empty K S D B t hempty,
    (activeSupport_eq_empty_iff_primitiveIdeal_eq_one B.support t).mp hempty]
  simp

/-- Every frequency of the unit primitive quotient has coefficient one;
this includes the zero frequency for every divisor dilation. -/
theorem divisor_fourier_eq_one_of_empty (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (hempty : activeSupport B.support t = ∅) (d : OS)
    (k : PrincipalQuotient K S D B t) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) d k = 1 := by
  rw [divisor_fourier,
    primitiveCoefficient_eq_one_of_empty K S D B t hempty,
    primitiveCoefficient_eq_one_of_empty K S D B t hempty,
    primitiveGauss_eq_one_of_empty K S D B t hempty]
  simp only [star_one, one_mul]

/-- The finite dual zero term is exactly the principal-locus indicator.
The divisor is arbitrary and may meet the conductor. -/
theorem divisor_fourier_zero (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (d : OS) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) d 0 =
      if activeSupport B.support t = ∅ then 1 else 0 := by
  by_cases hempty : activeSupport B.support t = ∅
  · rw [if_pos hempty]
    exact divisor_fourier_eq_one_of_empty K S D B t hempty d 0
  · rw [if_neg hempty]
    exact divisor_fourier_zero_of_active K S D B t
      (Finset.nonempty_iff_ne_empty.mpr hempty) d

theorem pair_divisor_fourier_zero (n₁ n₂ b₁ b₂ : Ext) (d : OS) :
    sIntegerPeriodicDivisorFourier K Sset D.different_outside
      (primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂))
      (primitiveCoefficient K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂)) d 0 =
      if CanonicalConductor.u₁ K S D n₁ n₂ b₁ b₂ = 1 ∧
          CanonicalConductor.u₂ K S D n₁ n₂ b₁ b₂ = 1 ∧
          CubeLabels.R1 b₁.val b₂.val
            (CanonicalConductor.squarefreeBit K S n₁)
            (CanonicalConductor.squarefreeBit K S n₂) = 1 then 1 else 0 := by
  simpa only [pair_active_empty_iff] using
    divisor_fourier_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
      (pairExponent K S n₁ n₂ b₁ b₂) d

/-- On the principal locus the original source retains the entire
complementary prime mask. It is not replaced by a vanishing term. -/
theorem pair_source_eq_principal_mask
    (Γ : Subgroup ((Sset).unit K)) (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (hempty : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅)
    (a : NonzeroRingElements OS) :
    CanonicalPoissonSource.pairCoefficient K S D n₁ n₂ b₁ b₂
      (Ideal.Quotient.mk _ a.val) =
      if IsCoprime (IdealMobiusMask.primeProduct
          (pairSupport K S D n₁ n₂ b₁ b₂).support)
        (sIntegerModulusContraction K Sset a.val) then 1 else 0 := by
  rw [pair_source_factorization K S D Γ n₁ n₂ b₁ b₂ hn₁ hn₂ a,
    primitiveCoefficient_eq_one_of_empty K S D _ _ hempty, mul_one,
    principalMask_mk, principal_source_mask_eq_coprime,
    principalIdeal_eq_period_of_empty _ _ hempty]

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalLocus

end
