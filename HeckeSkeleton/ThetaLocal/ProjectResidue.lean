import HeckeGeneral.Analysis.MarkedThetaReflection
import HeckeSkeleton.ThetaLocal.ExteriorUnitSums

/-!
# The actual exterior residue data used by marked theta reflection

The residue size, exact sixth order, additive phase (including its sign),
and normalized second Gauss sum are identified with the existing project
definitions.  No compatibility statement is assumed as a new input.
-/

noncomputable section

set_option autoImplicit false

namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance (p : ExteriorPrime K S) : Field (𝓞 K ⧸ p.val.asIdeal) :=
  Ideal.Quotient.field _

local instance (p : ExteriorPrime K S) : Fintype (𝓞 K ⧸ p.val.asIdeal) :=
  Fintype.ofFinite _

/-- The finite-field parameter is the actual prime's absolute norm. -/
theorem residue_card_eq_absNorm (p : ExteriorPrime K S) :
    Fintype.card (𝓞 K ⧸ p.val.asIdeal) = p.val.asIdeal.absNorm :=
  card_primeIdealResidueField K p.val

/-- The project character has exact order six, with its specified root pairing. -/
theorem thetaPrimeCharacter_orderOf (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- Package the existing literal phase as an additive character. -/
def projectPrimePhase (p : ExteriorPrime K S) :
    AddChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  transportCharacter
    (sIntegerResidueEquiv K S p.val.asIdeal
      (sIntegerSexticResidue_coprime K S p.val p.property))
    (thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p))

@[simp] theorem projectPrimePhase_apply (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    projectPrimePhase K S D p x = primePhase K S D p x := rfl

/-- Primitivity is inherited from the literal principal phase, with no rescaling. -/
theorem projectPrimePhase_isPrimitive (p : ExteriorPrime K S) :
    (projectPrimePhase K S D p).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))

/-- On an integral lift the phase is exactly the project's `e(a/generator p)`. -/
theorem projectPrimePhase_mk (p : ExteriorPrime K S) (a : 𝓞 K) :
    projectPrimePhase K S D p (Ideal.Quotient.mk p.val.asIdeal a) =
      sLocalPrincipalPhase K S
        ((algebraMap (𝓞 K) (S.integer K) a : K) /
          (D.generator (exteriorPrimeIdeal K S p) : K)) := by
  unfold projectPrimePhase
  rw [transportCharacter_apply, sIntegerResidueEquiv_mk,
    thetaPrincipalAddCharacter_mk]

private theorem primeDivisor_eq (p : ExteriorPrime K S)
    (q : idealPrimeDivisors K p.val.asIdeal) : q.val = p.val := by
  apply HeightOneSpectrum.ext
  exact (p.val.isMaximal.eq_of_le q.val.isPrime.ne_top
    (Ideal.dvd_iff_le.mp q.property)).symm

/-- The ideal-character function on the prime quotient is the actual prime character. -/
theorem thetaPrimeQuotientFunction_eq (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
      (exteriorPrimeIdeal K S p).val.val
      (nonZeroDivisors.coe_ne_zero (exteriorPrimeIdeal K S p).val)
      (exteriorPrimeIdeal K S p).property
      (fun q hq => D.away_six q ((exteriorPrimeIdeal K S p).property q hq))
      (sIntegerResidueEquiv K S p.val.asIdeal
        (sIntegerSexticResidue_coprime K S p.val p.property) x) =
      thetaPrimeCharacter K S D p x := by
  let p₀ : idealPrimeDivisors K p.val.asIdeal := ⟨p.val, dvd_rfl⟩
  letI : Unique (idealPrimeDivisors K p.val.asIdeal) :=
    { default := p₀
      uniq := fun q => Subtype.ext (primeDivisor_eq K S p q) }
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sIntegerResidueEquiv_mk, sIntegerSexticIdealQuotientFunction_mk]
  unfold sIntegerSexticIdealEvaluation
  rw [Fintype.prod_unique]
  change sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6
      D.embedding (D.away_six p.val p.property)
      (algebraMap (𝓞 K) (S.integer K) a) ^
        idealPrimeMultiplicity K p.val p.val.asIdeal = _
  have hm : idealPrimeMultiplicity K p.val p.val.asIdeal = 1 :=
    Associates.count_self p.val.associates_irreducible
  rw [hm, pow_one, sIntegerSexticEvaluation_algebraMap]
  rfl

/-- The project's Gauss coefficient uses precisely the transported phase and character. -/
theorem thetaGamma_two_eq_gammaTwo (p : ExteriorPrime K S) :
    thetaGamma K S D (exteriorPrimeIdeal K S p) 2 =
      HeckeSkeleton.ThetaLocal.ResidueField.gammaTwo
        (thetaPrimeCharacter K S D p) (projectPrimePhase K S D p) := by
  letI : Finite (ThetaQuotient K S (exteriorPrimeIdeal K S p)) :=
    finite_sIntegerSexticIdealQuotient K S (exteriorPrimeIdeal K S p).val.val
      (nonZeroDivisors.coe_ne_zero (exteriorPrimeIdeal K S p).val)
      (exteriorPrimeIdeal K S p).property
  letI : Fintype (ThetaQuotient K S (exteriorPrimeIdeal K S p)) := Fintype.ofFinite _
  unfold thetaGamma HeckeSkeleton.ThetaLocal.ResidueField.gammaTwo gaussSum
  rw [residue_card_eq_absNorm K S p]
  congr 1
  let e := sIntegerResidueEquiv K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val p.property)
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro x
  rw [thetaPrimeQuotientFunction_eq K S D p x]
  rw [MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
  rfl

end HeckeGeneral.ThetaSkeleton.Global
