module

public import ThetaGlobal.ReflectedCoefficientSummability
public import ThetaGlobal.ReflectedArithmetic

/-!
# Exact instantiation of the standalone scalar model by project arithmetic

This adapter is intentionally separate from the Mathlib-only verified model.
It imports the provided project and consequently needs its vendored dependencies.
Every local hypothesis of ScalarData is discharged here from actual project
characters and the proved prime Gauss norm. No global identity is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedCoefficientProject

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S) (θ : HeckeCharacter K)

def actualScalarData :
    ReflectedCoefficientModel.ScalarData
      (ExteriorPrime K S) (ExteriorIdeal K S) (S.integer K) (SixthUnitClasses K S) where
  normI := exteriorNorm K S
  normI_ge_one := ReflectedArithmetic.exteriorNorm_ge_one K S
  primeNorm := fun p => (p.val.asIdeal.absNorm : ℝ)
  primeNorm_ge_one := ReflectedArithmetic.primeNorm_ge_one K S
  generator := D.generator
  frequencyUnit := fun u => (S.unitEquivUnitsInteger K (Quotient.out u)).val
  removePrime := removePrime K S
  exponent := fun a p => primeExponents a.val p.val
  support := exteriorSupport K S
  primeSetIdeal := primeSetIdeal K S
  primeCharacter := primeEvaluation K S D
  primeCharacter_zeroOrUnit := ReflectedArithmetic.primeEvaluation_zeroOrUnit K S D
  idealCharacter := idealSymbol K S D
  idealCharacter_zeroOrUnit := ReflectedArithmetic.idealSymbol_zeroOrUnit K S D
  period := periodValue K S D d θ
  period_zeroOrUnit := ReflectedArithmetic.periodValue_zeroOrUnit K S D d θ
  gamma := fun p => thetaGamma K S D (exteriorPrimeIdeal K S p) 2
  gamma_norm := thetaGamma_exteriorPrime_two_norm K S D
  residueUnits := fun p => (𝓞 K ⧸ p.val.asIdeal)ˣ
  residueFintype := fun _ => Fintype.ofFinite _
  residueCharacter := fun p x => thetaPrimeCharacter K S D p x
  residueCharacter_zeroOrUnit := fun p x =>
    ReflectedArithmetic.thetaPrimeCharacter_zeroOrUnit K S D p x
  digit := fun p j x => digitMask K S D p j x
  inversePhase := fun p x =>
    primePhase K S D p ((x⁻¹ : (𝓞 K ⧸ p.val.asIdeal)ˣ) : 𝓞 K ⧸ p.val.asIdeal)

def actualFrame : ReflectedCoefficientModel.Frame (ExteriorPrime K S) (ExteriorIdeal K S) where
  moving := d.moving
  frozenPrimes := frozenPrimes K S d
  marks := d.marks
  rowDigit := rowDigit K S d

def actualIndex (i : ReflectionIndex K S d) :
    ReflectedCoefficientModel.Index (ExteriorPrime K S)
      (ExteriorIdeal K S) (SixthUnitClasses K S) where
  activeMarks := i.activeMarks
  activeFrozen := i.activeFrozen
  numeratorFrozen := i.numeratorFrozen
  n := i.n
  c := i.c
  unitSector := i.unitSector

theorem localWeyl_actual (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    ReflectedCoefficientModel.localWeyl (actualScalarData K S D d θ) p j e =
      localWeylScalar K S D p j e := by
  simp only [ReflectedCoefficientModel.localWeyl, actualScalarData,
    ReflectedLocalBounds.finiteWeylCoefficient,
    ReflectedLocalBounds.sphericalCoefficient, localWeylScalar, sphericalDigit,
    Complex.ofReal_natCast]

theorem reflectedCoefficient_actual (i : ReflectionIndex K S d) :
    ReflectedCoefficientModel.reflectedCoefficient (actualScalarData K S D d θ)
      (actualFrame K S d) (actualIndex K S d i) =
      ReflectedArithmetic.reflectedCoefficient K S D d i θ := by
  simp only [ReflectedCoefficientModel.reflectedCoefficient,
    ReflectedCoefficientModel.frozenOmega, ReflectedCoefficientModel.reflectedRowFactor,
    ReflectedCoefficientModel.reflectedMarkFactor,
    ReflectedCoefficientModel.reflectedColumnFactor,
    ReflectedCoefficientModel.activeFrozenIdeal, ReflectedCoefficientModel.activeMarkedIdeal,
    ReflectedCoefficientModel.localExponent, localWeyl_actual, actualFrame, actualIndex,
    ReflectedArithmetic.reflectedCoefficient, frozenOmega, reflectedRowFactor,
    reflectedMarkFactor, reflectedColumnFactor, localWeylExponent,
    activeFrozenIdeal, activeMarkedIdeal, frequencyUnit, actualScalarData,
    Complex.ofReal_natCast]

/-- An independent confirmation that every actual index appears in the
standalone ambient space with all six independent data coordinates retained. -/
def actualAmbientIndex (i : ReflectionIndex K S d) :
    ReflectedCoefficientSummability.AdmissibleIndex
      (U := SixthUnitClasses K S) (actualFrame K S d) :=
  ⟨actualIndex K S d i, i.marks_subset, i.frozen_subset⟩

theorem actualAmbientIndex_injective :
    Function.Injective (actualAmbientIndex K S d) := by
  intro i j h
  have he := congrArg Subtype.val h
  have hm : i.activeMarks = j.activeMarks := congrArg
    ReflectedCoefficientModel.Index.activeMarks he
  have hf : i.activeFrozen = j.activeFrozen := congrArg
    ReflectedCoefficientModel.Index.activeFrozen he
  have ha : i.numeratorFrozen = j.numeratorFrozen := congrArg
    ReflectedCoefficientModel.Index.numeratorFrozen he
  have hn : i.n = j.n := congrArg ReflectedCoefficientModel.Index.n he
  have hc : i.c = j.c := congrArg ReflectedCoefficientModel.Index.c he
  have hu : i.unitSector = j.unitSector := congrArg ReflectedCoefficientModel.Index.unitSector he
  cases i
  cases j
  cases hm
  cases hf
  cases ha
  cases hn
  cases hc
  cases hu
  rfl

end ThetaGlobal.ReflectedCoefficientProject

