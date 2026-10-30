import ArithmeticRowCharacterInput
import HeckeGeneral.Analysis.ThetaPrimeGaussNorm
import HeckeSkeleton.HighBinSupport.ActualPrimePowerSymbols
import HeckeSkeleton.HighBinSupport.ContractiveGaussPhases
import HeckeSkeleton.HighBinSupport.FiniteEulerTables

/-!
# Actual finite Euler data for physical frequency rows

The row character is the repository's arithmetic Artin/Kummer character.
The exceptional polynomial is built from the actual prime residue field,
the actual principal additive character, the theta-period coefficient,
and the prime-free part of the actual row ideal. There are exactly five
ramified rows; the sixth-power-free condition supplies their indices.

This constructs `RowEulerData` and proves its exceptional estimate. The
initial Fourier-to-Euler identity is a further theorem, not a field added
to this construction or an assumption used for its estimates.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualEuler

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinActualGenerators
open HeckeSkeleton.HighBinActualSymbols
open HeckeSkeleton.HighBinContinuation
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance primeResidueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance primeResidueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

theorem mem_exteriorSupport_iff (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    p ∈ exteriorSupport K S I ↔ p.val.asIdeal ∣ I.val.val := by
  constructor
  · intro hp
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hp
    have hval : q.val = p.val := congrArg Subtype.val hq
    exact hval ▸ (mem_idealPrimeSupport_iff K I.val q.val).mp q.property
  · intro hp
    let q : {q : HeightOneSpectrum (𝓞 K) // q ∈ idealPrimeSupport K I.val} :=
      ⟨p.val, (mem_idealPrimeSupport_iff K I.val p.val).mpr hp⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ q, Subtype.ext rfl⟩

/-- Removing p erases all its copies, so the remaining generator is a
unit in the residue field even when p divides the original row ideal. -/
theorem removePrime_not_dvd (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    ¬p.val.asIdeal ∣ (removePrime K S I p).val.val := by
  intro hp
  have hne : primeExponents (removePrime K S I p).val p.val ≠ 0 :=
    Finsupp.mem_support_iff.mp
      ((mem_idealPrimeSupport_iff K (removePrime K S I p).val p.val).mpr hp)
  simpa only [removePrime, primeExponents_idealOfPrimeExponents,
    Finsupp.erase_same, ne_eq, not_true_eq_false] using hne

theorem removePrime_eq_self_of_not_mem (I : ExteriorIdeal K S) (p : ExteriorPrime K S)
    (hp : p ∉ exteriorSupport K S I) : removePrime K S I p = I := by
  have h0 : primeExponents I.val p.val = 0 := by
    by_contra h
    exact hp ((mem_exteriorSupport_iff K S I p).mpr
      ((mem_idealPrimeSupport_iff K I.val p.val).mp (Finsupp.mem_support_iff.mpr h)))
  have he : (primeExponents I.val).erase p.val = primeExponents I.val := by
    ext q
    by_cases hq : q = p.val
    · subst q
      simp only [Finsupp.erase_same, h0]
    · exact Finsupp.erase_ne hq
  apply Subtype.ext
  change idealOfPrimeExponents ((primeExponents I.val).erase p.val) = I.val
  rw [he, idealOfPrimeExponents_primeExponents]

theorem residue_generator_removePrime_ne_zero (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    sIntegerSexticResidueMap K S p.val p.property (D.generator (removePrime K S I p)) ≠ 0 := by
  rw [ne_eq, sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction,
    contraction_thetaGenerator K S D]
  exact removePrime_not_dvd K S I p

/-- Prime-power removal reconstructs the original ideal exactly. -/
theorem exteriorPrimePower_mul_removePrime (I : ExteriorIdeal K S)
    (p : ExteriorPrime K S) :
    exteriorMul K S
      (exteriorPower K S (exteriorPrimeIdeal K S p) (primeExponents I.val p.val))
      (removePrime K S I p) = I := by
  apply Subtype.ext
  apply Subtype.ext
  change p.val.asIdeal ^ (primeExponents I.val p.val) *
    (idealOfPrimeExponents ((primeExponents I.val).erase p.val)).val = I.val.val
  calc
    _ = (idealOfPrimeExponents (Finsupp.single p.val (primeExponents I.val p.val)) *
        idealOfPrimeExponents ((primeExponents I.val).erase p.val)).val := by
      simp only [Submonoid.coe_mul, idealOfPrimeExponents_single]
    _ = (idealOfPrimeExponents (Finsupp.single p.val (primeExponents I.val p.val) +
        (primeExponents I.val).erase p.val)).val := by
      rw [idealOfPrimeExponents_add]
    _ = I.val.val := by
      rw [Finsupp.single_add_erase, idealOfPrimeExponents_primeExponents]

/-- For the actual allowed generator section, the prime-free row element
is its literal local unit part up to a sixth power of an S-unit. The
exponent is the actual ideal valuation, including exponent zero. -/
theorem frequencyRowElement_eq_prime_power_unitPart (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    ∃ v : S.unit K, frequencyRowElement K S P u =
      (S.unitEquivUnitsInteger K v).val ^ 6 *
        P.arithmetic.generator (exteriorPrimeIdeal K S p) ^ (primeExponents u.ideal.val p.val) *
        ((S.unitEquivUnitsInteger K (Quotient.out u.sector)).val *
          P.arithmetic.generator (removePrime K S u.ideal p)) := by
  obtain ⟨v, hv⟩ := hP.multiplicative
    (exteriorPower K S (exteriorPrimeIdeal K S p) (primeExponents u.ideal.val p.val))
    (removePrime K S u.ideal p)
  rw [exteriorPrimePower_mul_removePrime] at hv
  obtain ⟨w, hw⟩ := generator_power_eq_sixth_unit K S P.arithmetic hP
    (exteriorPrimeIdeal K S p) (primeExponents u.ideal.val p.val)
  refine ⟨v * w, ?_⟩
  rw [frequencyRowElement, hv, hw]
  simp only [map_mul, Units.val_mul, mul_pow]
  ring

/-- The unit residue of the actual row after removing its p-primary ideal
factor. It retains the row's sixth-unit sector. -/
def rowPrimeUnit (P : ProbeData K S) (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    (𝓞 K ⧸ p.val.asIdeal)ˣ :=
  sUnitSexticResidueUnit K S p.val p.property (Quotient.out u.sector) *
    Units.mk0 (sIntegerSexticResidueMap K S p.val p.property
      (P.arithmetic.generator (removePrime K S u.ideal p)))
      (residue_generator_removePrime_ne_zero K S P.arithmetic u.ideal p)

@[simp] theorem rowPrimeUnit_val (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) :
    (rowPrimeUnit K S P u p : 𝓞 K ⧸ p.val.asIdeal) =
      sIntegerSexticResidueMap K S p.val p.property
        ((S.unitEquivUnitsInteger K (Quotient.out u.sector)).val *
          P.arithmetic.generator (removePrime K S u.ideal p)) := by
  simp only [rowPrimeUnit, Units.val_mul, sUnitSexticResidueUnit_val,
    Units.val_mk0, map_mul]

/-- At a prime outside the actual row ideal, the local unit phase is
the actual arithmetic row-character coefficient, by whole-ideal
calibration at that prime. No independent phase identification is assumed. -/
theorem rowPrimeUnit_character_of_not_mem_row (P : ProbeData K S)
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∉ exteriorSupport K S u.ideal) :
    thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p) =
      primeCoefficient K (arithmeticRowCharacter K S P u) p.val := by
  have hnot : ¬p.val.asIdeal ∣ u.ideal.val.val :=
    fun h => hp ((mem_exteriorSupport_iff K S u.ideal p).mpr h)
  have hcop : IsCoprime p.val.asIdeal u.ideal.val.val := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := p.val.isMaximal.eq_of_le h le_sup_left
    exact hnot (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq heq.symm))
  have hcal := arithmeticRowCharacter_coefficient_calibration K S P u (exteriorPrimeIdeal K S p)
  rw [if_pos hcop] at hcal
  change idealCoefficient (primeCoefficient K (arithmeticRowCharacter K S P u))
      p.val.asIdeal = idealSymbol K S P.arithmetic (exteriorPrimeIdeal K S p)
        (frequencyRowElement K S P u) at hcal
  rw [idealCoefficient_prime, idealSymbol_eq_idealCoefficient] at hcal
  change primeCoefficient K (arithmeticRowCharacter K S P u) p.val =
    idealCoefficient (primeValue K S P.arithmetic (frequencyRowElement K S P u))
      p.val.asIdeal at hcal
  rw [idealCoefficient_prime, primeValue, dif_pos p.property] at hcal
  rw [rowPrimeUnit_val, removePrime_eq_self_of_not_mem K S u.ideal p hp]
  exact hcal.symm

/-- The literal prime-level additive character, transferred across the
proved residue equivalence; this is not an arbitrary trace character. -/
def primeAddCharacter (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    AddChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  transportCharacter (thetaPrimeResidueEquiv K S p)
    (thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p))

theorem primeAddCharacter_isPrimitive (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) : (primeAddCharacter K S D p).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))

theorem thetaPrimeCharacter_order (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

/-- The whole-ideal quotient symbol specializes to the prescribed prime
residue character. This identifies the actual finite sum before applying
any Gauss norm or orthogonality theorem. -/
theorem primeQuotientSymbol_equiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (x : 𝓞 K ⧸ p.val.asIdeal) :
    symbolOnQuotient K S D (exteriorPrimeIdeal K S p) (thetaPrimeResidueEquiv K S p x) =
      thetaPrimeCharacter K S D p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [thetaPrimeResidueEquiv, sIntegerResidueEquiv_mk,
    symbolOnQuotient, sIntegerSexticIdealQuotientFunction_mk]
  change idealSymbol K S D (exteriorPrimeIdeal K S p)
    (algebraMap (𝓞 K) (S.integer K) a) = _
  rw [idealSymbol_eq_idealCoefficient]
  change idealCoefficient (primeValue K S D (algebraMap (𝓞 K) (S.integer K) a))
    p.val.asIdeal = _
  rw [idealCoefficient_prime, primeValue, dif_pos p.property,
    sIntegerSexticEvaluation_algebraMap]
  rfl

/-- Every positive prime-level Gauss coefficient used in the finite table
is the repository's actual `thetaGamma`, with precisely its square-root
normalization. The exponent-zero unit mask is deliberately excluded. -/
theorem normalizedFamily_eq_thetaGamma (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (j : ℕ) (hj : j ≠ 0) :
    HighBin.ActualGaussPhases.normalizedFamily (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) j =
        thetaGamma K S D (exteriorPrimeIdeal K S p) j := by
  let Q := ThetaQuotient K S (exteriorPrimeIdeal K S p)
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S p.val.asIdeal
    p.val.ne_bot (exteriorPrimeIdeal K S p).property
  letI : Fintype Q := Fintype.ofFinite _
  let e : (𝓞 K ⧸ p.val.asIdeal) ≃+* Q := thetaPrimeResidueEquiv K S p
  have hsum :
      (∑ x : Q, symbolOnQuotient K S D (exteriorPrimeIdeal K S p) x ^ j *
        thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) x) =
      gaussSum (thetaPrimeCharacter K S D p ^ j) (primeAddCharacter K S D p) := by
    calc
      _ = ∑ x : 𝓞 K ⧸ p.val.asIdeal,
          symbolOnQuotient K S D (exteriorPrimeIdeal K S p) (e x) ^ j *
            thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) (e x) :=
        (e.toEquiv.sum_comp _).symm
      _ = _ := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro x _
        rw [primeQuotientSymbol_equiv, MulChar.pow_apply' _ hj]
        rfl
  unfold HighBin.ActualGaussPhases.normalizedFamily
    HighBin.FiniteResidueFourier.normalizedGauss
  change gaussSum (thetaPrimeCharacter K S D p ^ j) (primeAddCharacter K S D p) /
      (Real.sqrt (Fintype.card (𝓞 K ⧸ p.val.asIdeal)) : ℂ) =
    (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      ∑ x : Q, symbolOnQuotient K S D (exteriorPrimeIdeal K S p) x ^ j *
        thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p) x
  rw [hsum, card_primeIdealResidueField]
  ring

/-- All six finite-table coefficients are computed from actual Gauss sums.
The contractive theta factor includes the ramified-target zero case. -/
def rowPhaseData (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) : PhaseData :=
  HighBin.ActualGaussPhases.contractivePhaseData
    (thetaPrimeCharacter K S P.arithmetic p)
    (thetaPrimeCharacter_order K S P.arithmetic p)
    (primeAddCharacter K S P.arithmetic p)
    (primeAddCharacter_isPrimitive K S P.arithmetic p)
    (primeCoefficient K (thetaPeriod K S P ψ) p.val)
    (norm_primeCoefficient_le_one K _ p.val) (rowPrimeUnit K S P u p)

def rowRamifiedIndex (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ exteriorSupport K S u.ideal) : Fin 5 := by
  have hne : primeExponents u.ideal.val p.val ≠ 0 :=
    Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff K u.ideal.val p.val).mpr
      ((mem_exteriorSupport_iff K S u.ideal p).mp hp))
  exact ⟨primeExponents u.ideal.val p.val - 1, by
    have hlt := u.sixthPowerFree p.val
    omega⟩

@[simp] theorem rowRamifiedIndex_val (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ exteriorSupport K S u.ideal) :
    (rowRamifiedIndex K S u p hp).val = primeExponents u.ideal.val p.val - 1 := rfl

/-- The literal finite Laurent table at each exceptional prime. The marked
branch subtracts the completed-unit term at the numerator level. -/
def exceptionalFactor (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (p : {p : ExteriorPrime K S // p ∈ rowExceptionalPrimes K S Q u}) :
    FiniteEulerRational :=
  if hp : p.val ∈ exteriorSupport K S u.ideal then
    HighBinFiniteTables.ramified (rowPhaseData K S P ψ u p.val)
      (p.val.val.asIdeal.absNorm : ℝ) (rowRamifiedIndex K S u p.val hp)
      (decide (p.val ∈ Q))
  else
    HighBinFiniteTables.regular (p.val.val.asIdeal.absNorm : ℝ)
      (primeCoefficient K (arithmeticRowCharacter K S P u) p.val.val)
      (primeCoefficient K ψ p.val.val *
        conj (primeCoefficient K (arithmeticRowCharacter K S P u) p.val.val))
      (primeCoefficient K (thetaPeriod K S P ψ) p.val.val ^ 6)
      (decide (p.val ∈ Q))

/-- A construction of the repository's actual two-field Euler data. No
analytic calibration or bound occurs in the input arguments. -/
def arithmeticHighEulerData (P : ProbeData K S) (ψ : HeckeCharacter K) :
    RowEulerData K S P where
  rows := arithmeticRowCharacterInput K S P
  exceptionalFactor := exceptionalFactor K S P ψ

@[simp] theorem arithmeticHighEulerData_character (P : ProbeData K S)
    (ψ : HeckeCharacter K) (u : FrequencyRow K S) :
    (arithmeticHighEulerData K S P ψ).rows.character u = arithmeticRowCharacter K S P u := rfl

/-- Every exceptional prime outside the mark set is one of the five
ramified rows. This is a set-theoretic consequence, not a ramification
assumption about a free family of characters. -/
theorem exceptional_unmarked_mem_row (Q : Finset (ExteriorPrime K S))
    (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ rowExceptionalPrimes K S Q u) (hpQ : p ∉ Q) :
    p ∈ exteriorSupport K S u.ideal := by
  exact (Finset.mem_union.mp hp).resolve_right hpQ

theorem exceptional_unmarked_value (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ rowExceptionalPrimes K S Q u) (hpQ : p ∉ Q)
    (s w z : ℂ)
    (hR : 1 - coordR (rowPhaseData K S P ψ u p) (p.val.asIdeal.absNorm : ℝ) s z ≠ 0) :
    finiteEulerRationalValue
        ((arithmeticHighEulerData K S P ψ).exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) s w z =
      ramifiedTableValue (rowPhaseData K S P ψ u p) (p.val.asIdeal.absNorm : ℝ) s w z
        (rowRamifiedIndex K S u p (exceptional_unmarked_mem_row K S Q u p hp hpQ)) := by
  have hmem := exceptional_unmarked_mem_row K S Q u p hp hpQ
  have hq : (0 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))
  simp only [arithmeticHighEulerData, exceptionalFactor, dif_pos hmem,
    decide_eq_false hpQ]
  simpa only [Bool.false_eq_true, if_false, sub_zero] using
    HighBinFiniteTables.ramified_value (rowPhaseData K S P ψ u p)
      (p.val.asIdeal.absNorm : ℝ) hq s w z (rowRamifiedIndex K S u p hmem) false hR

/-- The constructed ramified factor is exactly the finite table with the
actual prime-level Gauss sums. This equality includes ramified targets
whose theta-period coefficient is zero. The exponent-zero unit mask in
the raw table is retained. -/
theorem exceptional_unmarked_eq_actualGaussTable
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ rowExceptionalPrimes K S Q u) (hpQ : p ∉ Q)
    (s w z : ℂ)
    (hV : 1 - coordV (p.val.asIdeal.absNorm : ℝ) z ≠ 0)
    (hR : 1 - coordR (rowPhaseData K S P ψ u p) (p.val.asIdeal.absNorm : ℝ) s z ≠ 0) :
    finiteEulerRationalValue
        ((arithmeticHighEulerData K S P ψ).exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) s w z =
      HighBin.FiniteLocalTable.finiteTableCorrection (p.val.asIdeal.absNorm : ℂ)
        (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
        (coordV (p.val.asIdeal.absNorm : ℝ) z)
        (rowRamifiedIndex K S u p (exceptional_unmarked_mem_row K S Q u p hp hpQ)) := by
  rw [exceptional_unmarked_value K S P ψ Q u p hp hpQ s w z hR]
  have hV' : 1 - coordV (Fintype.card (𝓞 K ⧸ p.val.asIdeal)) z ≠ 0 := by
    simpa only [card_primeIdealResidueField] using hV
  have hR' : 1 - coordR (rowPhaseData K S P ψ u p)
      (Fintype.card (𝓞 K ⧸ p.val.asIdeal)) s z ≠ 0 := by
    simpa only [card_primeIdealResidueField] using hR
  have h := HighBin.ActualGaussPhases.finiteTable_eq_contractiveGaussTable
    (thetaPrimeCharacter K S P.arithmetic p) (thetaPrimeCharacter_order K S P.arithmetic p)
    (primeAddCharacter K S P.arithmetic p) (primeAddCharacter_isPrimitive K S P.arithmetic p)
    (primeCoefficient K (thetaPeriod K S P ψ) p.val)
    (norm_primeCoefficient_le_one K _ p.val) (rowPrimeUnit K S P u p) s w z
    (rowRamifiedIndex K S u p (exceptional_unmarked_mem_row K S Q u p hp hpQ)) hV' hR'
  simpa only [card_primeIdealResidueField, rowPhaseData] using h.symm

/-- Uniform exceptional-prime estimate for the constructed actual finite
tables. Its constant is 9 and its cutoff is 2, independent of a, u, Q,
all imaginary parts, and all finite Gauss zeros. -/
theorem exceptional_unmarked_dynamic_bound (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (p : ExteriorPrime K S)
    (hp : p ∈ rowExceptionalPrimes K S Q u) (hpQ : p ∉ Q)
    {a e : ℝ} (ha : 1 / 2 ≤ a) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = a + 16 * e)
    (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50) :
    ‖finiteEulerRationalValue
        ((arithmeticHighEulerData K S P ψ).exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) s w z - 1‖ ≤
      9 * (p.val.asIdeal.absNorm : ℝ) ^ (-10 * e) := by
  have hmem := exceptional_unmarked_mem_row K S Q u p hp hpQ
  have hq : (2 : ℝ) ≤ p.val.asIdeal.absNorm := by
    have hqN : 2 ≤ p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
    exact_mod_cast hqN
  simp only [arithmeticHighEulerData, exceptionalFactor, dif_pos hmem,
    decide_eq_false hpQ]
  exact HighBinFiniteTables.ramified_dynamic_bound (rowPhaseData K S P ψ u p)
    (p.val.asIdeal.absNorm : ℝ) a e hq ha he s w z hs hw hz (rowRamifiedIndex K S u p hmem)

end HeckeSkeleton.HighBinActualEuler
