import CubicSieve.GaussPairFourier

/-! The genuine mixed row on the literal principal quotient of generator(I)*generator(J).
Every divisor pullback and every finite Fourier frequency remains present. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPairLiteral

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.ProductResidueFourier
open CubicSieve.GaussPair
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

abbrev LiteralQuotient (I J : ExteriorIdeal K S) :=
  S.integer K ⧸ Ideal.span ({D.generator I * D.generator J} : Set (S.integer K))

instance literalFinite (I J : ExteriorIdeal K S) : Finite (LiteralQuotient K S D I J) :=
  finite_sIntegerPrincipalResidue K S (D.generator I * D.generator J)
    (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))

instance literalFintype (I J : ExteriorIdeal K S) : Fintype (LiteralQuotient K S D I J) :=
  Fintype.ofFinite _

def literalRow (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (x : LiteralQuotient K S D I J) : ℂ :=
  pairRow K S D I J hI hJ ((literalEquiv K S D I J).symm x)

@[simp] theorem literalRow_mk (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (a : S.integer K) :
    literalRow K S D I J hI hJ (Ideal.Quotient.mk _ a) =
      star (idealSymbol K S D I a ^ 2) * idealSymbol K S D J a ^ 2 := by
  have he : (literalEquiv K S D I J).symm (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := by
    apply (literalEquiv K S D I J).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Ideal.quotEquivOfEq_mk _ a).symm
  rw [literalRow, he, pairRow_mk]

theorem literalRow_mul (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (x y : LiteralQuotient K S D I J) :
    literalRow K S D I J hI hJ (x * y) =
      literalRow K S D I J hI hJ x * literalRow K S D I J hI hJ y := by
  simp only [literalRow, pairRow, map_mul]
  ring

theorem literal_phase_transport (I J : ExteriorIdeal K S) :
    transportCharacter (literalEquiv K S D I J).symm (pairPhase K S D I J) =
      sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I * D.generator J)
        (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)) := by
  ext x
  change sIntegerActualModulusAddCharacter K S D.different_outside
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
        ((literalEquiv K S D I J) ((literalEquiv K S D I J).symm x)) = _
  rw [RingEquiv.apply_symm_apply]

theorem literal_fourier (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (hcop : IsCoprime I.val.val J.val.val)
    (h : LiteralQuotient K S D I J) :
    PeriodicFourier.fourier
      (sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I * D.generator J)
        (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)))
      (literalRow K S D I J hI hJ) h =
      star (literalRow K S D I J hI hJ h) *
        (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
          pairNormalizedGauss K S D I J hI hJ := by
  have ht := transport_fourier (literalEquiv K S D I J).symm
    (pairPhase K S D I J) (pairRow K S D I J hI hJ) h
  rw [literal_phase_transport] at ht
  exact ht.trans (GaussPairFourier.pairFourier K S D I J hI hJ hcop _)

theorem literal_divisorFourier (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (hcop : IsCoprime I.val.val J.val.val)
    (d : S.integer K) (h : LiteralQuotient K S D I J) :
    sIntegerPeriodicDivisorFourier K S D.different_outside
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
      (literalRow K S D I J hI hJ) d h =
      literalRow K S D I J hI hJ (Ideal.Quotient.mk _ d) *
        star (literalRow K S D I J hI hJ h) *
        (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ) *
        (star (thetaGamma K S D I 2) * thetaGamma K S D J 2) := by
  rw [sIntegerPeriodicDivisorFourier_apply]
  simp only [literalRow_mul, mul_assoc]
  rw [← Finset.mul_sum]
  change literalRow K S D I J hI hJ (Ideal.Quotient.mk _ d) *
    PeriodicFourier.fourier _ _ h = _
  rw [literal_fourier K S D I J hI hJ hcop h,
    pairNormalizedGauss_eq K S D hD I J hI hJ hcop]
  ring

end CubicSieve.GaussPairLiteral
