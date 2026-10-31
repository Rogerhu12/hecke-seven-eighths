import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Characters.SIntegerSexticPowerMask
import RowCharacterCanonicalUniqueness
import ArithmeticFrequencyRowRamification
/-!
The actual unramified row phase, from the existing coefficient calibration.

At a prime not dividing the row ideal, the literal residue of the frequency
element is nonzero. Its specified-root sextic character is exactly the
prime Hecke coefficient of every correctly calibrated RowCharacterInput.
This is a specialization of actual arithmetic data, not a freely supplied
phase-character identity. The real repository's canonical-uniqueness and
ramification theorems also identify the exact zeros at row primes.

This project-dependent file is excluded from the Mathlib-only aggregate.
-/

noncomputable section

namespace HighBinVerified.RowPrimeCharacter

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance (p : ExteriorPrime K S) : Field (𝓞 K ⧸ p.val.asIdeal) :=
  Ideal.Quotient.field _

/-- Public prime specialization of the literal complete-ideal symbol.
All denominator and specified-root normalizations are retained. -/
theorem idealSymbol_prime_eq_residueCharacter (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (a : S.integer K) :
    idealSymbol K S D (exteriorPrimeIdeal K S p) a =
      thetaPrimeCharacter K S D p (sIntegerSexticResidueMap K S p.val p.property a) := by
  let p0 : idealPrimeDivisors K p.val.asIdeal := ⟨p.val, dvd_refl _⟩
  letI : Fintype (idealPrimeDivisors K p.val.asIdeal) :=
    (idealPrimeDivisors_finite K p.val.asIdeal p.val.ne_bot).fintype
  have hsingle : ∀ q : idealPrimeDivisors K p.val.asIdeal, q = p0 := by
    intro q
    apply Subtype.ext
    have he : p.val.asIdeal = q.val.asIdeal :=
      p.val.isMaximal.eq_of_le q.val.isPrime.ne_top (Ideal.dvd_iff_le.mp q.property)
    exact HeightOneSpectrum.ext he.symm
  have hmult : idealPrimeMultiplicity K p.val p.val.asIdeal = 1 := by
    unfold idealPrimeMultiplicity
    exact Associates.count_self p.val.associates_irreducible
  change (∏ q : idealPrimeDivisors K p.val.asIdeal,
    sIntegerSexticEvaluation K S q.val
      ((exteriorPrimeIdeal K S p).property q.val q.property)
      D.root6 D.primitive6 D.embedding
      (D.away_six q.val ((exteriorPrimeIdeal K S p).property q.val q.property)) a ^
        idealPrimeMultiplicity K q.val p.val.asIdeal) = _
  rw [Finset.prod_eq_single_of_mem p0 (Finset.mem_univ p0)
    (fun q _ hne => False.elim (hne (hsingle q)))]
  change sIntegerSexticEvaluation K S p.val p.property D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property) a ^ idealPrimeMultiplicity K p.val p.val.asIdeal = _
  rw [hmult, pow_one]
  rfl

theorem prime_coprime_of_not_dvd (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    IsCoprime p.val.asIdeal u.ideal.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he : p.val.asIdeal = p.val.asIdeal ⊔ u.ideal.val.val :=
    p.val.isMaximal.eq_of_le hne le_sup_left
  exact hp (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq he.symm))

/-- The phase in the valuation-zero finite table is the actual row's
Euler coefficient. The existing mask has been discharged by hp. -/
theorem row_primeCoefficient_eq_residueCharacter
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    primeCoefficient K (R.character u) p.val =
      thetaPrimeCharacter K S P.arithmetic p
        (sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u)) := by
  have hc := R.coefficient_calibration u (exteriorPrimeIdeal K S p)
  have hcop : IsCoprime (exteriorPrimeIdeal K S p).val.val u.ideal.val.val :=
    prime_coprime_of_not_dvd K S u p hp
  rw [ite_eq_left hcop] at hc
  simpa only [heckeIdealCoefficient, nonzeroIdealCoefficient, exteriorPrimeIdeal,
    idealCoefficient_prime] using
      hc.trans (idealSymbol_prime_eq_residueCharacter K S P.arithmetic p _)

/-- The frequency element generates the actual row ideal after contraction;
this is proved directly from the generator field and the unit sector. -/
theorem row_element_contraction (P : ProbeData K S) (u : FrequencyRow K S) :
    sIntegerModulusContraction K S (frequencyRowElement K S P u) = u.ideal.val.val := by
  unfold frequencyRowElement sIntegerModulusContraction
  rw [Ideal.span_singleton_mul_left_unit
    (S.unitEquivUnitsInteger K (Quotient.out u.sector)).isUnit,
    P.arithmetic.generator_span]
  exact under_map_coprime_sIntegerIdeal K S u.ideal.val.val
    (sexticIdeal_coprime_S K S u.ideal.val.val u.ideal.property)

theorem row_residue_ne_zero (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u) ≠ 0 := by
  intro hz
  have hd := (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
    K S p.val p.property (frequencyRowElement K S P u)).mp hz
  rw [row_element_contraction] at hd
  exact hp hd

/-- The exact zero mask is the original row ideal, independently of any
claim about how its primitive inducing character behaves at bad primes. -/
theorem row_residue_eq_zero_iff_dvd (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) :
    sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u) = 0 ↔
      p.val.asIdeal ∣ u.ideal.val.val := by
  rw [sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction, row_element_contraction]

/-- The finite phase polynomial can therefore be replaced by the actual
prime Hecke polynomial with exactly the original row-prime mask. -/
theorem row_residueCharacter_eq_masked_primeCoefficient
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    thetaPrimeCharacter K S P.arithmetic p
        (sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u)) =
      if p.val.asIdeal ∣ u.ideal.val.val then 0 else primeCoefficient K (R.character u) p.val := by
  by_cases hp : p.val.asIdeal ∣ u.ideal.val.val
  · rw [ite_eq_left hp, (row_residue_eq_zero_iff_dvd K S P u p).mpr hp]
    exact map_zero _
  · rw [ite_eq_right hp]
    exact (row_primeCoefficient_eq_residueCharacter K S P R u p hp).symm

/-- The literal residue unit expected by the finite-field Gauss table. -/
def rowResidueUnit (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    (𝓞 K ⧸ p.val.asIdeal)ˣ :=
  Units.mk0 (sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u))
    (row_residue_ne_zero K S P u p hp)

theorem row_primeCoefficient_eq_residueUnit_character
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    primeCoefficient K (R.character u) p.val =
      thetaPrimeCharacter K S P.arithmetic p (rowResidueUnit K S P u p hp) :=
  row_primeCoefficient_eq_residueCharacter K S P R u p hp

/-- Every calibrated actual provider is unramified outside the original
row ideal. This conclusion does not need a ramification hypothesis. -/
theorem row_unramified_of_not_dvd
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : ¬ p.val.asIdeal ∣ u.ideal.val.val) :
    UnramifiedAt K (R.character u) p.val := by
  have hphase : thetaPrimeCharacter K S P.arithmetic p
      (rowResidueUnit K S P u p hp) ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr (rowResidueUnit K S P u p hp).isUnit
  rw [← row_primeCoefficient_eq_residueUnit_character K S P R u p hp] at hphase
  by_contra hram
  exact hphase (primeCoefficient_of_ramified K (R.character u) p.val hram)

/-- The actual canonical-character theorem determines the bad-prime
behavior of every original calibrated row provider. -/
theorem row_not_unramified_of_dvd
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p.val.asIdeal ∣ u.ideal.val.val) :
    ¬ UnramifiedAt K (R.character u) p.val := by
  rw [rowCharacterInput_character_eq_arithmetic K S P R u]
  apply arithmeticRowCharacter_not_unramified_of_pos_exponent K S P u p.val p.property
  apply Nat.pos_of_ne_zero
  apply Finsupp.mem_support_iff.mp
  exact (HeckeGeneral.Analysis.SquarefreeAmplification.mem_idealPrimeSupport_iff
    K u.ideal.val p.val).mpr hp

theorem row_primeCoefficient_eq_zero_of_dvd
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p.val.asIdeal ∣ u.ideal.val.val) :
    primeCoefficient K (R.character u) p.val = 0 :=
  primeCoefficient_of_ramified K (R.character u) p.val
    (row_not_unramified_of_dvd K S P R u p hp)

/-- Complete prime calibration, including both branches of the original
zero mask. The only character input is the original RowCharacterInput. -/
theorem row_primeCoefficient_eq_residueCharacter_all
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    primeCoefficient K (R.character u) p.val =
      thetaPrimeCharacter K S P.arithmetic p
        (sIntegerSexticResidueMap K S p.val p.property (frequencyRowElement K S P u)) := by
  rw [row_residueCharacter_eq_masked_primeCoefficient K S P R u p]
  by_cases hp : p.val.asIdeal ∣ u.ideal.val.val
  · rw [ite_eq_left hp]
    exact row_primeCoefficient_eq_zero_of_dvd K S P R u p hp
  · rw [ite_eq_right hp]

end HighBinVerified.RowPrimeCharacter

#print axioms HighBinVerified.RowPrimeCharacter.idealSymbol_prime_eq_residueCharacter
#print axioms HighBinVerified.RowPrimeCharacter.row_primeCoefficient_eq_residueUnit_character
#print axioms HighBinVerified.RowPrimeCharacter.row_residue_ne_zero
#print axioms HighBinVerified.RowPrimeCharacter.row_residueCharacter_eq_masked_primeCoefficient
#print axioms HighBinVerified.RowPrimeCharacter.row_unramified_of_not_dvd
#print axioms HighBinVerified.RowPrimeCharacter.row_not_unramified_of_dvd
#print axioms HighBinVerified.RowPrimeCharacter.row_primeCoefficient_eq_residueCharacter_all
