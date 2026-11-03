import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Actual separated profile parameters

Q 15149 puts `(q/P)^(z_phys-1)` into the prime profile; Q 15163--15168
permits rowwise witness parameters after fixing physical parameters and slot
indices. These are actual support-preserving constructors and literal finite
sum identities, not moment estimates or canonical-admissibility instances.

Inverse and the two plain tests may have independent rowwise times and
complex powers. Prime parameters are fixed per slot and cannot depend on the
moving row. The whole family of permitted prime profiles must be selected
before the target, as required by M 283--304; freezing a parameter does not
prove uniform seminorm bounds or justify posttarget changes of geometry.

The logarithmic exponential is a nonzero total extension at nonpositive
arguments, to preserve the existing all-real support specification. At actual
positive norm ratios it is exactly the complex power. Original coefficients,
integer orientation, common masks, and ramified zero extensions are untouched.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped BigOperators Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- Total, everywhere nonzero extension of the complex-power profile twist. -/
def profilePower (a : ℂ) (y : ℝ) : ℂ :=
  Complex.exp ((Real.log y : ℂ) * a)

theorem profilePower_ne_zero (a : ℂ) (y : ℝ) : profilePower a y ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem profilePower_zero (y : ℝ) : profilePower 0 y = 1 := by
  simp [profilePower]

theorem profilePower_eq_cpow (a : ℂ) {y : ℝ} (hy : 0 < y) :
    profilePower a y = (y : ℂ) ^ a := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne')]
  rw [← Complex.ofReal_log hy.le]
  rfl

/-- The time and complex power may be chosen independently at every row. -/
def IdealTest.freezeTwist (W : IdealTest K)
    (time : NonzeroIdeal K → ℝ) (power : NonzeroIdeal K → ℂ) : IdealTest K where
  profile u _ y := W.profile u (time u) y * profilePower (power u) y
  support u _ D := W.support u (time u) D
  support_spec u _ D I := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero h (profilePower_ne_zero _ _)
    · exact left_ne_zero_of_mul

/-- A prime slot has a single time and power, independent of the row. -/
def PrimeWindow.freezeTwist (W : PrimeWindow K) (time : ℝ) (power : ℂ) :
    PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile _ y := W.profile time y * profilePower power y
  support _ P := W.support time P
  support_spec _ P p := by
    rw [W.support_spec]
    constructor
    · intro h
      exact mul_ne_zero h (profilePower_ne_zero _ _)
    · exact left_ne_zero_of_mul

/-- Slot lengths and the number of slots are unchanged. -/
def SlotGeometry.freezeTwists (g : SlotGeometry K)
    (time : Fin g.slotCount → ℝ) (power : Fin g.slotCount → ℂ) : SlotGeometry K where
  slotCount := g.slotCount
  slots i := (g.slots i).freezeTwist (time i) (power i)

@[simp] theorem SlotGeometry.totalLength_freezeTwists (g : SlotGeometry K)
    (time : Fin g.slotCount → ℝ) (power : Fin g.slotCount → ℂ) :
    (g.freezeTwists time power).totalLength = g.totalLength := rfl

@[simp] theorem SlotGeometry.fitsMesh_freezeTwists (g : SlotGeometry K)
    (time : Fin g.slotCount → ℝ) (power : Fin g.slotCount → ℂ) (mesh : ℝ) :
    (g.freezeTwists time power).fitsMesh mesh ↔ g.fitsMesh mesh := Iff.rfl

variable {ω ψ : HeckeCharacter K}

/-- Freeze separate inverse/plain witness parameters and row-independent slot
parameters into the actual data. This supplies no admissibility certificate. -/
def MomentData.separatedProfiles (d : MomentData K ω ψ)
    (inverseTime plainTime₁ plainTime₂ : NonzeroIdeal K → ℝ)
    (inversePower plainPower₁ plainPower₂ : NonzeroIdeal K → ℂ)
    (slotTime : Fin d.geometry.slotCount → ℝ)
    (slotPower : Fin d.geometry.slotCount → ℂ) : MomentData K ω ψ :=
  { d with
    inverseTest := d.inverseTest.freezeTwist inverseTime inversePower
    plainTest₁ := d.plainTest₁.freezeTwist plainTime₁ plainPower₁
    plainTest₂ := d.plainTest₂.freezeTwist plainTime₂ plainPower₂
    geometry := d.geometry.freezeTwists slotTime slotPower }

variable (d : MomentData K ω ψ)
    (inverseTime plainTime₁ plainTime₂ : NonzeroIdeal K → ℝ)
    (inversePower plainPower₁ plainPower₂ : NonzeroIdeal K → ℂ)
    (slotTime : Fin d.geometry.slotCount → ℝ)
    (slotPower : Fin d.geometry.slotCount → ℂ)

local notation "d'" => d.separatedProfiles inverseTime plainTime₁ plainTime₂
  inversePower plainPower₁ plainPower₂ slotTime slotPower

@[simp] theorem maskValue_separatedProfiles (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) : maskValue d' u I = maskValue d u I := rfl

@[simp] theorem pairedRows_separatedProfiles (a : RealParameters) (Z : ℝ) :
    pairedRows d' a Z = pairedRows d a Z := rfl

/-- The independently frozen inverse sum at common interface time zero. -/
theorem inversePolynomial_separatedProfiles (u : NonzeroIdeal K) (D : ℝ) :
    inversePolynomial d' u D 0 =
      (Real.sqrt D : ℂ)⁻¹ *
        ∑ I ∈ d.inverseTest.support u (inverseTime u) D,
          (UniqueFactorizationMonoid.moebius I.val : ℂ) *
            heckeIdealCoefficient K d.inverseBackground I *
            heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction *
            (d.inverseTest.profile u (inverseTime u) (idealNorm K I / D) *
              profilePower (inversePower u) (idealNorm K I / D)) *
            maskValue d u I.val := rfl

/-- This applies separately to either plain test; its time and power need not
agree with the inverse test or with the other plain test. -/
theorem plainPolynomial_separatedProfiles (W : IdealTest K)
    (time : NonzeroIdeal K → ℝ) (power : NonzeroIdeal K → ℂ)
    (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial d' (W.freezeTwist time power) u N 0 =
      (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ W.support u (time u) N,
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          (W.profile u (time u) (idealNorm K I / N) *
            profilePower (power u) (idealNorm K I / N)) *
          maskValue d u I.val := rfl

/-- The prime character remains the literal positive-oriented row character
times the original slot coefficient; its profile parameters are row-independent. -/
theorem primePolynomial_separatedProfiles (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z : ℝ) :
    primePolynomial d' i u Z 0 =
      let P := Z ^ (d.geometry.slots i).length
      (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support (slotTime i) P,
        primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
          ((d.geometry.slots i).profile (slotTime i) ((Ideal.absNorm p.asIdeal : ℝ) / P) *
            profilePower (slotPower i) ((Ideal.absNorm p.asIdeal : ℝ) / P)) *
          maskValue d u p.asIdeal := rfl

/-- With no extra power, freezing recovers each original sum at its own time. -/
theorem inversePolynomial_freeze_time (u : NonzeroIdeal K) (D : ℝ) :
    inversePolynomial
      (d.separatedProfiles inverseTime plainTime₁ plainTime₂
        (fun _ => 0) plainPower₁ plainPower₂ slotTime slotPower) u D 0 =
      inversePolynomial d u D (inverseTime u) := by
  simp only [inversePolynomial, MomentData.separatedProfiles, IdealTest.freezeTwist,
    profilePower_zero, mul_one, maskValue]

theorem plainPolynomial_freeze_time (W : IdealTest K)
    (time : NonzeroIdeal K → ℝ) (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial d' (W.freezeTwist time (fun _ => 0)) u N 0 =
      plainPolynomial d W u N (time u) := by
  simp only [plainPolynomial, MomentData.separatedProfiles, IdealTest.freezeTwist,
    profilePower_zero, mul_one, maskValue]
  rfl

theorem primePolynomial_freeze_time (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z : ℝ) :
    primePolynomial
      (d.separatedProfiles inverseTime plainTime₁ plainTime₂
        inversePower plainPower₁ plainPower₂ slotTime (fun _ => 0)) i u Z 0 =
      primePolynomial d i u Z (slotTime i) := by
  simp only [primePolynomial, MomentData.separatedProfiles, SlotGeometry.freezeTwists,
    PrimeWindow.freezeTwist, profilePower_zero, mul_one, maskValue]
  rfl

end HeckeGeneral.Analysis.ConditionalMoments
