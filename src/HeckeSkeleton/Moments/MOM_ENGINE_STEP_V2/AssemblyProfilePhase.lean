module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormula
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The Fourier phase of a public original profile formula

The original profile at frequency zero contains its dilation, scalar,
real power and conjugation. Its remaining dependence on the Fourier
parameter is one logarithmic phase. This identity holds on the whole
real line, including the formula's zero extension at nonpositive
arguments, and uses no calibration or task implementation.
-/

open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase

open Blueprint EngineStep
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

theorem linear_zero (a : ℝ × ℝ) : ProfileFormula.linear a 0 = 0 := by
  change a.1 * 0 + a.2 * 0 = 0
  simp

theorem value_zero (f : ProfileFormula) (x : ℝ) :
    f.value 0 x = if 0 < x then
      f.scalar *
        (if f.conjugate then star (f.original (f.dilation * x))
         else f.original (f.dilation * x)) * (x ^ f.power : ℝ) else 0 := by
  simp only [ProfileFormula.value, linear_zero, zero_mul, zero_add,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

theorem logPhase_inner (phase translation : ℝ × ℝ)
    (ξ : EngineParameter) (x : ℝ) :
    inner ℝ ξ (WithLp.toLp 2 translation + Real.log x • WithLp.toLp 2 phase) =
      ProfileFormula.linear phase ξ * Real.log x +
        ProfileFormula.linear translation ξ := by
  rw [inner_add_right, real_inner_smul_right]
  simp only [WithLp.prod_inner_apply, Real.inner_apply,
    ProfileFormula.linear]
  ring

/-- The fixed amplitude is the value of the same original formula at
zero frequency. No positivity assumption on the real argument is needed. -/
theorem value_eq_zero_mul_phase (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) :
    f.value ξ x = f.value 0 x *
      jointPhase ξ
        (WithLp.toLp 2 f.translation + Real.log x • WithLp.toLp 2 f.phase) := by
  rw [jointPhase, Real.fourierChar_apply, logPhase_inner, value_zero]
  by_cases hx : 0 < x
  · simp only [ProfileFormula.value, hx, ite_true]
  · simp only [ProfileFormula.value, hx, ite_false, zero_mul]

/-- All non-phase factors remain in the original zero-frequency
profile. The atom therefore has unit scale and exponent zero. -/
noncomputable def atom (f : ProfileFormula) : CanonicalLogProfiles.Atom EngineParameter where
  scale := 1
  scale_pos := zero_lt_one
  exponent := 0
  offset := WithLp.toLp 2 f.translation
  direction := WithLp.toLp 2 f.phase

theorem atom_multiplier (f : ProfileFormula) (ξ : EngineParameter) (x : ℝ) :
    (atom f).multiplier ξ x =
      jointPhase ξ
        (WithLp.toLp 2 f.translation + Real.log x • WithLp.toLp 2 f.phase) := by
  simp only [atom, CanonicalLogProfiles.Atom.multiplier,
    CanonicalLogProfiles.Atom.location, one_mul, Real.rpow_zero, Complex.ofReal_one]

theorem value_eq_zero_mul_multiplier (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) :
    f.value ξ x = f.value 0 x * (atom f).multiplier ξ x := by
  rw [atom_multiplier]
  exact value_eq_zero_mul_phase f ξ x

/-- A formula with zero phase and translation is fixed at every
Fourier parameter, as required for the original inverse profile. -/
theorem value_eq_zero_of_zero_phase (f : ProfileFormula)
    (hphase : f.phase = 0) (htranslation : f.translation = 0)
    (ξ : EngineParameter) (x : ℝ) : f.value ξ x = f.value 0 x := by
  simp [ProfileFormula.value, ProfileFormula.linear, hphase, htranslation]

theorem value_eq_zero_of_nonpos (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) (hx : x ≤ 0) : f.value ξ x = 0 := by
  simp only [ProfileFormula.value, not_lt.mpr hx, ite_false]

theorem argument_pos_of_value_ne_zero (f : ProfileFormula)
    (ξ : EngineParameter) (x : ℝ) (hvalue : f.value ξ x ≠ 0) : 0 < x := by
  by_contra hx
  exact hvalue (by simp only [ProfileFormula.value, hx, ite_false])

variable {K : Type} [Field K] [NumberField K]

/-- A whole-profile formula identity supplies the positivity required
by the base ideal-test atom constructor. -/
theorem positivePlainProfile_of_formula (f : ProfileFormula) (ξ : EngineParameter)
    (W : IdealTest K)
    (hprofile : ∀ u t x, W.profile u t x = f.value ξ x) :
    CanonicalLogProfiles.PositivePlainProfile W := by
  intro u t x hx
  rw [hprofile u t x] at hx
  exact argument_pos_of_value_ne_zero f ξ x hx

/-- The analogous positivity statement for one original prime slot. -/
theorem positivePrimeProfile_of_formula (f : ProfileFormula) (ξ : EngineParameter)
    (W : PrimeWindow K)
    (hprofile : ∀ t x, W.profile t x = f.value ξ x) :
    CanonicalLogProfiles.PositivePrimeProfile W := by
  intro t x hx
  rw [hprofile t x] at hx
  exact argument_pos_of_value_ne_zero f ξ x hx

end HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.value_eq_zero_mul_phase
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.atom
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.atom_multiplier
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.value_eq_zero_mul_multiplier
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.value_eq_zero_of_zero_phase
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.argument_pos_of_value_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.positivePlainProfile_of_formula
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.ProfilePhase.positivePrimeProfile_of_formula
