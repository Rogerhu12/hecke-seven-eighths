import HeckeGeneral.Arithmetic.SIntegerSixthPowerDenominator
import ArithmeticSexticKummerPrimeCoefficient
import HeckeGeneral.Analysis.PrimeCalibrationIdealAssembly
import HeckeGeneral.Analysis.FrequencyRowOrbit

/-!
UNCOMPILED cache candidate, 2026-10-11. No Lean/Lake process was started.

An actual RowCharacterInput assembled from the existing ProbeData arithmetic:
choose one integral sixth-power S-unit representative for each actual row,
construct its arithmetic Artin/Kummer character, prove finite order, and
calibrate every exterior ideal with the ORIGINAL row coprimality mask.

No character, local coefficient formula, whole-ideal calibration, conductor,
faithfulness, exact order six, theta realization, or analytic bound is assumed.
The imported independent cache proofs and their upstream closure remain
subject to native checking. This candidate is not a checked construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ArithmeticKummerDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open GlobalClassFieldTheory.Reciprocity

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A fixed sixth-power S-unit representative calibrates the actual original
S-integer prime evaluation at all good primes. The representative precedes p. -/
theorem arithmeticSexticKummerCharacter_primeCoefficient_sInteger
    (D : ThetaArithmeticData K S)
    (a : S.integer K) (ha : a ≠ 0) (b : 𝓞 K) (hb : b ≠ 0) (u : S.unit K)
    (hrep : algebraMap (𝓞 K) (S.integer K) b =
      (S.unitEquivUnitsInteger K u).val ^ 6 * a)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S)
    (hpa : ¬ p.asIdeal ∣ sIntegerModulusContraction K S a) :
    primeCoefficient K
        (arithmeticSexticKummerCharacter K D.embedding
          ⟨D.root6, (mem_primitiveRoots (by norm_num)).mpr D.primitive6⟩
          (nonzeroIntegralFieldUnit K b hb)) p =
      sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
        (D.away_six p hp) a := by
  have hbp : b ∉ p.asIdeal := p.valuation_eq_one_iff_notMem.mp
    (integer_sixthPower_sUnit_representative_valuation_eq_one
      K S a ha b u hrep p hp hpa)
  rw [arithmeticSexticKummerCharacter_primeCoefficient
    K D.root6 D.primitive6 D.embedding b hb p (D.away_six p hp) hbp]
  calc
    sexticResidueEvaluation K D.root6 D.primitive6 D.embedding p (D.away_six p hp) b =
        sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
          (D.away_six p hp) (algebraMap (𝓞 K) (S.integer K) b) :=
      (sIntegerSexticEvaluation_algebraMap
        K S p hp D.root6 D.primitive6 D.embedding (D.away_six p hp) b).symm
    _ = sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
        (D.away_six p hp) a := by
      rw [hrep]
      exact sIntegerSexticEvaluation_mul_sixth_power_unit
        K S p hp D.root6 D.primitive6 D.embedding (D.away_six p hp) u a

end HeckeGeneral.Characters.ArithmeticKummerDraft

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Characters.ArithmeticKummerDraft
open HeckeGeneral.Analysis HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.ThetaSkeleton.Global
open GlobalClassFieldTheory.Reciprocity
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Choose b once for this row, with its nonzero proof and a sixth-power
S-unit relation to the original row element. No ideal argument enters here. -/
def arithmeticRowIntegralRepresentative (P : ProbeData K S) (v : FrequencyRow K S) :
    {b : 𝓞 K // b ≠ 0 ∧ ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
        (S.unitEquivUnitsInteger K u).val ^ 6 * frequencyRowElement K S P v} := by
  have hexists : ∃ b : 𝓞 K, b ≠ 0 ∧ ∃ u : S.unit K,
      algebraMap (𝓞 K) (S.integer K) b =
        (S.unitEquivUnitsInteger K u).val ^ 6 * frequencyRowElement K S P v := by
    obtain ⟨b, hb, u, hrep⟩ := exists_integer_sixthPower_sUnit_representative
      K S (frequencyRowElement K S P v) (frequencyRowElement_ne_zero K S P v)
    exact ⟨b, hb, u, hrep⟩
  exact ⟨Classical.choose hexists, Classical.choose_spec hexists⟩

/-- The continuous arithmetic Artin/Kummer character of the chosen integral
representative, using exactly P's root and embedding. -/
def arithmeticRowCharacter (P : ProbeData K S) (v : FrequencyRow K S) : HeckeCharacter K :=
  let b := arithmeticRowIntegralRepresentative K S P v
  arithmeticSexticKummerCharacter K P.arithmetic.embedding
    ⟨P.arithmetic.root6, (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
    (nonzeroIntegralFieldUnit K b.val b.property.1)

theorem arithmeticRowCharacter_finiteOrder (P : ProbeData K S) (v : FrequencyRow K S) :
    FiniteOrder (arithmeticRowCharacter K S P v) := by
  dsimp only [arithmeticRowCharacter]
  exact arithmeticSexticKummerCharacter_finiteOrder K _ _ _

/-- Literal calibration of every exterior ideal, including I=1 and the
noncoprime zero branch. No ramification claim at bad row primes is needed. -/
theorem arithmeticRowCharacter_coefficient_calibration
    (P : ProbeData K S) (v : FrequencyRow K S) (I : ExteriorIdeal K S) :
    (if IsCoprime I.val.val v.ideal.val.val
      then heckeIdealCoefficient K (arithmeticRowCharacter K S P v) I.val else 0) =
      idealSymbol K S P.arithmetic I (frequencyRowElement K S P v) := by
  let b := arithmeticRowIntegralRepresentative K S P v
  obtain ⟨u, hrep⟩ := b.property.2
  have hcal := masked_heckeIdealCoefficient_eq_idealSymbol_of_primeCalibration
    K S P.arithmetic (frequencyRowElement K S P v) (arithmeticRowCharacter K S P v)
    (fun p hp hpa => by
      change primeCoefficient K
          (arithmeticSexticKummerCharacter K P.arithmetic.embedding
            ⟨P.arithmetic.root6,
              (mem_primitiveRoots (by norm_num)).mpr P.arithmetic.primitive6⟩
            (nonzeroIntegralFieldUnit K b.val b.property.1)) p = _
      exact arithmeticSexticKummerCharacter_primeCoefficient_sInteger
        K S P.arithmetic (frequencyRowElement K S P v)
        (frequencyRowElement_ne_zero K S P v) b.val b.property.1 u hrep p hp hpa) I
  simpa only [frequencyRowElement_contraction] using hcal

/-- R's actual three fields, with no extra assumptions beyond the existing
number-field, finite S and ProbeData arguments. Native checking is pending. -/
def arithmeticRowCharacterInput (P : ProbeData K S) : RowCharacterInput K S P where
  character := arithmeticRowCharacter K S P
  finite_order := arithmeticRowCharacter_finiteOrder K S P
  coefficient_calibration := arithmeticRowCharacter_coefficient_calibration K S P

end HeckeGeneral.ThetaSkeleton.Physical
