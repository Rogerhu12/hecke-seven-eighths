import HeckeSkeleton.HighBinSupport.ActualGeneratorPowers
import HeckeGeneral.Analysis.PrimeCalibrationIdealAssembly

/-!
# The original ideal symbol on principal prime-power quotients

PROJECT ADAPTER. This file uses the original `idealSymbol`, the original
finite quotient function, and the original finite-field sextic character.
The prime-power pullback is proved by actual ideal factorization; no local
Fourier or Euler calibration is a hypothesis. Native checking is pending against the restored project dependency closure.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

noncomputable section
namespace HeckeSkeleton.HighBinActualSymbols
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinActualGenerators
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A total prime-value function; the branch in S is never used by an
exterior ideal's actual prime factorization. -/
def primeValue (D : ThetaArithmeticData K S) (a : S.integer K)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if hp : p ∉ S then
    sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding (D.away_six p hp) a
  else 0

/-- The literal finite-prime product equals the existing multiplicative
ideal coefficient, also when a is zero or nonunit at denominator primes. -/
theorem idealSymbol_eq_idealCoefficient (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a = idealCoefficient (primeValue K S D a) I.val.val := by
  letI : Fintype (idealPrimeDivisors K I.val.val) :=
    (idealPrimeDivisors_finite K I.val.val (nonZeroDivisors.coe_ne_zero I.val)).fintype
  rw [idealCoefficient_eq_prod_idealPrimeDivisors K (primeValue K S D a) I.val]
  unfold idealSymbol sIntegerSexticIdealEvaluation
  apply Finset.prod_congr rfl
  intro p _
  rw [primeValue, dif_pos (I.property p.val p.property)]

/-- Denominator multiplicativity is proved for the actual symbol, with all
nonunit zeros retained, independently of sextic reciprocity. -/
theorem idealSymbol_exteriorMul (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D (exteriorMul K S I J) a =
      idealSymbol K S D I a * idealSymbol K S D J a := by
  rw [idealSymbol_eq_idealCoefficient, idealSymbol_eq_idealCoefficient,
    idealSymbol_eq_idealCoefficient]
  exact idealCoefficient_mul (primeValue K S D a) I.val.val J.val.val

/-- The exact positive prime-power symbol, before passing to a quotient. -/
theorem idealSymbol_primePower (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (a : S.integer K) :
    idealSymbol K S D (exteriorPower K S (exteriorPrimeIdeal K S p) n) a =
      sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
        (D.away_six p.val p.property) a ^ n := by
  rw [idealSymbol_eq_idealCoefficient]
  change idealCoefficient (primeValue K S D a) (p.val.asIdeal ^ n) = _
  rw [idealCoefficient_prime_pow, primeValue, dif_pos p.property]

/-- Positive n is essential: at n=0 the unit ideal has constant symbol 1,
while the zeroth MulChar power is the unit indicator. -/
theorem idealSymbol_primePower_mulChar (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) (a : S.integer K) :
    idealSymbol K S D (exteriorPower K S (exteriorPrimeIdeal K S p) n) a =
      (thetaPrimeCharacter K S D p ^ n) (sIntegerSexticResidueMap K S p.val p.property a) := by
  rw [idealSymbol_primePower, MulChar.pow_apply' _ (by omega : n ≠ 0)]
  rfl

/-- The literal quotient projection to the original residue field. -/
def primePowerResidue (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) :
    ThetaQuotient K S (exteriorPower K S (exteriorPrimeIdeal K S p) n) →+*
      (𝓞 K ⧸ p.val.asIdeal) :=
  (sIntegerResidueEquiv K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val p.property)).symm.toRingHom.comp
      (Ideal.quotientMap (p.val.asIdeal.map (algebraMap (𝓞 K) (S.integer K)))
        (RingHom.id (S.integer K)) (by
          change (p.val.asIdeal ^ n).map (algebraMap (𝓞 K) (S.integer K)) ≤
            (p.val.asIdeal.map (algebraMap (𝓞 K) (S.integer K))).comap
              (RingHom.id (S.integer K))
          rw [Ideal.comap_id]
          exact Ideal.map_mono (Ideal.dvd_iff_le.mp
            (dvd_pow_self p.val.asIdeal (by omega : n ≠ 0)))))

@[simp] theorem primePowerResidue_mk (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n)
    (a : S.integer K) :
    primePowerResidue K S p n hn (Ideal.Quotient.mk _ a) =
      sIntegerSexticResidueMap K S p.val p.property a := by
  unfold primePowerResidue
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingHom.id_apply] <;> rfl

def symbolOnQuotient (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    ThetaQuotient K S I → ℂ :=
  sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

/-- The actual quotient function is exactly the inflated sextic power. -/
theorem symbolOnQuotient_primePower (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n)
    (x : ThetaQuotient K S (exteriorPower K S (exteriorPrimeIdeal K S p) n)) :
    symbolOnQuotient K S D (exteriorPower K S (exteriorPrimeIdeal K S p) n) x =
      (thetaPrimeCharacter K S D p ^ n) (primePowerResidue K S p n hn x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [symbolOnQuotient, sIntegerSexticIdealQuotientFunction_mk, primePowerResidue_mk]
  exact idealSymbol_primePower_mulChar K S D p n hn a

#print axioms idealSymbol_exteriorMul
#print axioms idealSymbol_primePower_mulChar
#print axioms symbolOnQuotient_primePower
end HeckeSkeleton.HighBinActualSymbols
