import CubicSieve.GaussCharacters
import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier

/-! Literal principal-quotient Fourier coefficients of the actual cubic row.
Divisor dilation may be a nonunit. The exact Gauss phase is retained.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPoissonFinite

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.Arithmetic.ProductResidueFourier
open CubicSieve.GaussSquarefree CubicSieve.GaussCharacters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
variable (I : ExteriorIdeal K S)

local notation "QP" => S.integer K ⧸ Ideal.span ({D.generator I} : Set (S.integer K))
local instance principalFinite : Finite QP :=
  finite_sIntegerPrincipalResidue K S (D.generator I) (D.generator_ne_zero I)
local instance principalFintype : Fintype QP := Fintype.ofFinite _
local instance thetaFinite : Finite (ThetaQuotient K S I) :=
  finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
local instance thetaFintype : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _

theorem principal_addCharacter_transport :
    transportCharacter (principalEquiv K S D I) (thetaPrincipalAddCharacter K S D I) =
      sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I) (D.generator_ne_zero I) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sIntegerActualModulusAddCharacter K S D.different_outside
    (D.generator I) (D.generator_ne_zero I)
      ((Ideal.quotEquivOfEq (D.generator_span I).symm)
        ((Ideal.quotEquivOfEq (D.generator_span I)) (Ideal.Quotient.mk _ a))) = _
  rw [Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk]

theorem principal_fourier (hI : Squarefree I.val.val) (h : QP) :
    PeriodicFourier.fourier
        (sIntegerActualModulusAddCharacter K S D.different_outside
          (D.generator I) (D.generator_ne_zero I))
        (principalCubicCharacter K S D I hI) h =
      star (principalCubicCharacter K S D I hI h) *
        PeriodicFourier.fourier
          (sIntegerActualModulusAddCharacter K S D.different_outside
            (D.generator I) (D.generator_ne_zero I))
          (principalCubicCharacter K S D I hI) 1 := by
  have ht (q : QP) := transport_fourier (principalEquiv K S D I)
    (thetaPrincipalAddCharacter K S D I)
    (fun x => quotientFunction K S D I x ^ (2 : ℕ)) q
  rw [principal_addCharacter_transport] at ht
  have heq : (fun q : QP => quotientFunction K S D I
      (principalEquiv K S D I q) ^ (2 : ℕ)) =
        principalCubicCharacter K S D I hI := by
    funext q
    exact (quotientCubicCharacter_apply K S D I hI _).symm
  rw [heq] at ht
  rw [ht h, quotientFunction_power_fourier K S D I hI 2 (Or.inl rfl), ht 1,
    map_one]
  rw [congrFun heq h]

theorem principal_gauss_eq (hI : Squarefree I.val.val) :
    gaussSum (principalCubicCharacter K S D I hI)
      (sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I) (D.generator_ne_zero I)) =
      (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) * thetaGamma K S D I 2 := by
  have hpos : 0 < (I.val.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (I.val : (Ideal (𝓞 K))⁰)
  have hsqrt : (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  have ht := transport_fourier (principalEquiv K S D I)
    (thetaPrincipalAddCharacter K S D I)
    (fun x => quotientFunction K S D I x ^ (2 : ℕ)) 1
  rw [principal_addCharacter_transport, map_one] at ht
  have heq : (fun q : QP => quotientFunction K S D I
      (principalEquiv K S D I q) ^ (2 : ℕ)) =
        principalCubicCharacter K S D I hI := by
    funext q
    exact (quotientCubicCharacter_apply K S D I hI _).symm
  rw [heq] at ht
  change (∑ x : QP, principalCubicCharacter K S D I hI x *
    sIntegerActualModulusAddCharacter K S D.different_outside
      (D.generator I) (D.generator_ne_zero I) x) = _
  have hsum : (∑ x : QP, principalCubicCharacter K S D I hI x *
      sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I) (D.generator_ne_zero I) x) =
      ∑ x : ThetaQuotient K S I, quotientFunction K S D I x ^ (2 : ℕ) *
        thetaPrincipalAddCharacter K S D I x := by
    simpa only [PeriodicFourier.fourier, one_mul] using ht
  rw [hsum]
  change _ = (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) *
    ((Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ * _)
  rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  rfl

theorem divisorFourier_eq (hI : Squarefree I.val.val) (d : S.integer K) (h : QP) :
    sIntegerPeriodicDivisorFourier K S D.different_outside (D.generator I)
      (D.generator_ne_zero I) (principalCubicCharacter K S D I hI) d h =
      principalCubicCharacter K S D I hI (Ideal.Quotient.mk _ d) *
        star (principalCubicCharacter K S D I hI h) *
        (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) * thetaGamma K S D I 2 := by
  rw [sIntegerPeriodicDivisorFourier_apply]
  simp only [map_mul, mul_assoc]
  rw [← Finset.mul_sum]
  change principalCubicCharacter K S D I hI (Ideal.Quotient.mk _ d) *
    PeriodicFourier.fourier _ _ h = _
  rw [principal_fourier K S D I hI h]
  have heq : PeriodicFourier.fourier
      (sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I) (D.generator_ne_zero I))
      (principalCubicCharacter K S D I hI) 1 =
      gaussSum (principalCubicCharacter K S D I hI)
        (sIntegerActualModulusAddCharacter K S D.different_outside
          (D.generator I) (D.generator_ne_zero I)) := by
    simp only [PeriodicFourier.fourier, gaussSum, one_mul]
  rw [heq, principal_gauss_eq K S D I hI]

end CubicSieve.GaussPoissonFinite
