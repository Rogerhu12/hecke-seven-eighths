import HeckeSkeleton.HighBinSupport.ActualEulerData
import HeckeSkeleton.HighBinSupport.ActualInitialAbsolute
import HeckeSkeleton.HighBinSupport.PrincipalPowerGauss
import Mathlib.Algebra.Field.Equiv

/-!
# The valuation Gauss formula on actual S-integer prime powers

The prime element is the existing generator of the actual exterior prime
ideal. Its primality, maximal residue quotient, all quotient cardinalities,
exact character order, primitive principal phase, and compatibility between
levels are proved from the repository data. None is an extra calibration
assumption. The resulting formula is the literal Fourier sum on
`S.integer K / (generator(p)^n)`.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualPrimeGauss

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeSkeleton.HighBinActualGenerators HeckeSkeleton.HighBinActualAbsolute
open HeckeSkeleton.HighBinActualEuler
open HighBin.PrincipalPowerSupport HighBin.FiniteLocalTable
open scoped Classical BigOperators nonZeroDivisors

section CharacterTransport

variable {R T : Type*} [CommRing R] [CommRing T]

def pullbackMulChar (e : R ≃+* T) (χ : MulChar T ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp
  map_nonunit' x hx := χ.map_nonunit
    (fun h => hx ((MulEquiv.isUnit_map e).mp h))

/-- Transport preserves every character power, including the zeroth
power's unit mask on a quotient ring. -/
theorem pullbackMulChar_pow (e : R ≃+* T) (χ : MulChar T ℂ) (n : ℕ) :
    pullbackMulChar e (χ ^ n) = pullbackMulChar e χ ^ n := by
  apply MulChar.ext
  intro u
  calc
    _ = (χ ^ n) (Units.map e.toMonoidHom u) := rfl
    _ = χ (Units.map e.toMonoidHom u) ^ n := MulChar.pow_apply_coe _ _ _
    _ = pullbackMulChar e χ u ^ n := rfl
    _ = _ := (MulChar.pow_apply_coe _ _ _).symm

theorem pullbackMulChar_order (e : R ≃+* T) (χ : MulChar T ℂ) :
    orderOf (pullbackMulChar e χ) = orderOf χ := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  constructor
  · intro h
    apply MulChar.ext
    intro u
    have hu := congrArg (fun f : MulChar R ℂ =>
      f (Units.map e.symm.toMonoidHom u)) h
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hu
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    simpa [pullbackMulChar] using hu
  · intro h
    apply MulChar.ext
    intro u
    have hu := congrArg (fun f : MulChar T ℂ =>
      f (Units.map e.toMonoidHom u)) h
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hu
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    simpa [pullbackMulChar] using hu

end CharacterTransport

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance primeResidueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance primeResidueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

def primeGenerator (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    S.integer K := D.generator (exteriorPrimeIdeal K S p)

theorem primeGenerator_ne_zero (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    primeGenerator K S D p ≠ 0 := D.generator_ne_zero _

theorem primeGenerator_powerIdeal (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    powerIdeal (primeGenerator K S D p) n =
      (p.val.asIdeal ^ n).map (algebraMap (𝓞 K) (S.integer K)) :=
  generator_power_span K S D (exteriorPrimeIdeal K S p) n

def primeGeneratorQuotientEquiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    PowerQuotient (primeGenerator K S D p) n ≃+*
      ThetaQuotient K S (exteriorPower K S (exteriorPrimeIdeal K S p) n) :=
  Ideal.quotEquivOfEq (primeGenerator_powerIdeal K S D p n)

local instance principalPowerFinite (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    Finite (PowerQuotient (primeGenerator K S D p) n) := by
  let I := exteriorPower K S (exteriorPrimeIdeal K S p) n
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
  exact Finite.of_equiv (ThetaQuotient K S I)
    (primeGeneratorQuotientEquiv K S D p n).symm.toEquiv

local instance principalPowerFintype (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    Fintype (PowerQuotient (primeGenerator K S D p) n) := Fintype.ofFinite _

/-- Actual ideal norm computes every principal prime-power quotient. -/
theorem principalPower_card (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    Fintype.card (PowerQuotient (primeGenerator K S D p) n) = p.val.asIdeal.absNorm ^ n := by
  let I := exteriorPower K S (exteriorPrimeIdeal K S p) n
  have h := Nat.card_congr (primeGeneratorQuotientEquiv K S D p n).toEquiv
  change Nat.card (PowerQuotient (primeGenerator K S D p) n) =
    Nat.card (S.integer K ⧸ (p.val.asIdeal ^ n).map
      (algebraMap (𝓞 K) (S.integer K))) at h
  rw [natCard_sIntegerResidue K S (p.val.asIdeal ^ n)
    (sexticIdeal_coprime_S K S (p.val.asIdeal ^ n) I.property)] at h
  simpa only [Nat.card_eq_fintype_card, map_pow] using h

def principalPrimeResidueEquiv (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    PowerQuotient (primeGenerator K S D p) 1 ≃+* (𝓞 K ⧸ p.val.asIdeal) :=
  (Ideal.quotEquivOfEq (show powerIdeal (primeGenerator K S D p) 1 =
      p.val.asIdeal.map (algebraMap (𝓞 K) (S.integer K)) by
    simpa only [pow_one] using primeGenerator_powerIdeal K S D p 1)).trans
      (thetaPrimeResidueEquiv K S p).symm

@[simp] theorem principalPrimeResidueEquiv_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (x : S.integer K) :
    principalPrimeResidueEquiv K S D p
      (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) 1) x) =
        sIntegerSexticResidueMap K S p.val p.property x := by
  unfold principalPrimeResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem principalPrime_isMaximal (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    (powerIdeal (primeGenerator K S D p) 1).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField (𝓞 K ⧸ p.val.asIdeal))
    (principalPrimeResidueEquiv K S D p).toMulEquiv

local instance principalPrimeMaximal (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    (powerIdeal (primeGenerator K S D p) 1).IsMaximal :=
  principalPrime_isMaximal K S D p

/-- Primality of the chosen prime generator follows from its actual
maximal ideal, without a PID assumption on the ordinary integers. -/
theorem primeGenerator_prime (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    Prime (primeGenerator K S D p) := by
  apply (Ideal.span_singleton_prime (primeGenerator_ne_zero K S D p)).mp
  simpa only [powerIdeal, pow_one] using
    (principalPrime_isMaximal K S D p).isPrime

def principalPrimeCharacter (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    MulChar (PowerQuotient (primeGenerator K S D p) 1) ℂ :=
  pullbackMulChar (principalPrimeResidueEquiv K S D p) (thetaPrimeCharacter K S D p)

@[simp] theorem principalPrimeCharacter_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (x : S.integer K) :
    principalPrimeCharacter K S D p
        (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) 1) x) =
      thetaPrimeCharacter K S D p (sIntegerSexticResidueMap K S p.val p.property x) := by
  simp only [principalPrimeCharacter, pullbackMulChar, principalPrimeResidueEquiv_mk]

theorem principalPrimeCharacter_order (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    orderOf (principalPrimeCharacter K S D p) = 6 := by
  rw [principalPrimeCharacter, pullbackMulChar_order, thetaPrimeCharacter_order]

def principalPowerAddCharacter (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    AddChar (PowerQuotient (primeGenerator K S D p) n) ℂ :=
  sIntegerActualModulusAddCharacter K S D.different_outside (primeGenerator K S D p ^ n)
    (pow_ne_zero n (primeGenerator_ne_zero K S D p))

theorem principalPowerAddCharacter_isPrimitive (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    (principalPowerAddCharacter K S D p n).IsPrimitive :=
  sIntegerActualModulusAddCharacter_isPrimitive K S D.different_outside _ _

theorem principalPowerAddCharacter_compatible (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) (x : S.integer K) :
    principalPowerAddCharacter K S D p n
        (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n)
          (primeGenerator K S D p ^ (n - 1) * x)) =
      principalPowerAddCharacter K S D p 1
        (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) 1) x) := by
  simpa only [principalPowerAddCharacter, powerIdeal, pow_one] using
    principalPower_character_compatible K S D (primeGenerator K S D p)
      (primeGenerator_ne_zero K S D p) n hn x

/-- The two actual prime phases agree under the proved residue
equivalence: both evaluate the same literal fraction x/generator(p). -/
theorem principalPrime_addCharacter (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (x : PowerQuotient (primeGenerator K S D p) 1) :
    principalPowerAddCharacter K S D p 1 x =
      primeAddCharacter K S D p (principalPrimeResidueEquiv K S D p x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  unfold principalPowerAddCharacter primeAddCharacter
  rw [transportCharacter_apply]
  unfold principalPrimeResidueEquiv
  rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, Ideal.quotEquivOfEq_mk,
    thetaPrincipalAddCharacter_mk, sIntegerActualModulusAddCharacter_mk]
  simp only [primeGenerator, pow_one]

/-- Prime-level Gauss coefficients in the principal-power computation
are the very same finite-field sums used in the actual Euler tables.
This includes exponent zero, with its correct unit-indicator convention. -/
theorem principalPrime_gaussSum (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (r : ℕ) :
    gaussSum (principalPrimeCharacter K S D p ^ r) (principalPowerAddCharacter K S D p 1) =
      HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) r := by
  let e := principalPrimeResidueEquiv K S D p
  unfold gaussSum HighBin.ActualGaussPhases.gaussFamily
  rw [gaussSum]
  calc
    _ = ∑ x : 𝓞 K ⧸ p.val.asIdeal,
        (principalPrimeCharacter K S D p ^ r) (e.symm x) *
          principalPowerAddCharacter K S D p 1 (e.symm x) :=
      (e.symm.toEquiv.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [principalPrime_addCharacter, principalPrimeCharacter, ← pullbackMulChar_pow]
      change (thetaPrimeCharacter K S D p ^ r) (e (e.symm x)) *
        primeAddCharacter K S D p (e (e.symm x)) = _
      rw [e.apply_symm_apply]

/-- Literal prime-power Fourier evaluation for the actual arithmetic
data. The only valuation input is that v is prime to the actual generator;
the Gauss coefficients and all quotient structures are constructed above. -/
theorem actualPrimePowerFourier_eq_valuationGauss (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n)
    (v : S.integer K) (hv : ¬primeGenerator K S D p ∣ v) (J r : ℕ) :
    HighBin.FiniteResidueFourier.fourier (principalPowerAddCharacter K S D p n)
      (fun x => (principalPrimeCharacter K S D p ^ r)
        (residueMap (primeGenerator K S D p) n hn x))
      (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n)
        (primeGenerator K S D p ^ J * v)) =
      valuationGauss p.val.asIdeal.absNorm
        (fun b => gaussSum (principalPrimeCharacter K S D p ^ b)
          (principalPowerAddCharacter K S D p 1))
        (thetaPrimeCharacter K S D p (sIntegerSexticResidueMap K S p.val p.property v))
        n r J := by
  have hc : Fintype.card (PowerQuotient (primeGenerator K S D p) n) =
      Fintype.card (PowerQuotient (primeGenerator K S D p) 1) ^ n := by
    rw [principalPower_card, principalPower_card, pow_one]
  have h := HighBin.PrincipalPowerGauss.fourier_eq_valuationGauss
    (primeGenerator K S D p) n hn (primeGenerator_prime K S D p) v hv J r
    (principalPrimeCharacter K S D p) (principalPrimeCharacter_order K S D p)
    (principalPowerAddCharacter K S D p n) (principalPowerAddCharacter_isPrimitive K S D p n)
    (principalPowerAddCharacter K S D p 1) hc
    (principalPowerAddCharacter_compatible K S D p n hn)
  simpa only [principalPower_card, pow_one, principalPrimeCharacter_mk] using h

/-- The valuation formula with the exact Gauss family already used by
`arithmeticHighEulerData`, after actual quotient reindexing. -/
theorem actualPrimePowerFourier_eq_tableGauss (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n)
    (v : S.integer K) (hv : ¬primeGenerator K S D p ∣ v) (J r : ℕ) :
    HighBin.FiniteResidueFourier.fourier (principalPowerAddCharacter K S D p n)
      (fun x => (principalPrimeCharacter K S D p ^ r)
        (residueMap (primeGenerator K S D p) n hn x))
      (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n)
        (primeGenerator K S D p ^ J * v)) =
      valuationGauss p.val.asIdeal.absNorm
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
          (primeAddCharacter K S D p))
        (thetaPrimeCharacter K S D p (sIntegerSexticResidueMap K S p.val p.property v))
        n r J := by
  rw [actualPrimePowerFourier_eq_valuationGauss K S D p n hn v hv J r]
  congr 1
  funext b
  exact principalPrime_gaussSum K S D p b

#print axioms principalPrime_gaussSum
#print axioms actualPrimePowerFourier_eq_tableGauss

end HeckeSkeleton.HighBinActualPrimeGauss
