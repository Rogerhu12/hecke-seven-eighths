import HeckeGeneral.Characters.Packet
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Classification of continuous unitary characters of the real additive group

We first prove the continuous exponential functional equation without any
differentiability assumption. Integration over one nonzero interval supplies
differentiability, and an integrating factor identifies the exponential.
Unitarity then forces a purely imaginary exponent. This is the radial
character classification needed at each infinite place.
-/

noncomputable section

namespace HeckeGeneral.Characters

open MeasureTheory intervalIntegral

/-- An antiderivative of a continuous complex-valued function on the line. -/
def realPrimitive (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in 0..x, f t

theorem hasDerivAt_realPrimitive {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (realPrimitive f) (f x) x :=
  integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem exists_realPrimitive_ne_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hzero : f 0 = 1) : ∃ x : ℝ, realPrimitive f x ≠ 0 := by
  by_contra h
  push Not at h
  have heq : realPrimitive f = fun _ => 0 := funext h
  have hd := hasDerivAt_realPrimitive hf 0
  rw [heq, hzero] at hd
  have hbad := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  exact one_ne_zero hbad

/-- Translation of the integral uses the actual multiplicative functional equation. -/
theorem realPrimitive_add_sub {f : ℝ → ℂ} (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) (x a : ℝ) :
    realPrimitive f (x + a) - realPrimitive f x = f x * realPrimitive f a := by
  unfold realPrimitive
  rw [integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have hshift := integral_comp_add_left (f := f) (a := 0) (b := a) x
  simp only [add_zero] at hshift
  rw [← hshift]
  simp_rw [hadd]
  exact integral_const_mul (f x) f

/-- A continuous solution of the exponential equation is automatically differentiable. -/
theorem hasDerivAt_exponential_equation {f : ℝ → ℂ} (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) {a : ℝ}
    (ha : realPrimitive f a ≠ 0) (x : ℝ) :
    HasDerivAt f (((f a - 1) / realPrimitive f a) * f x) x := by
  have hformula : f = fun y =>
      (realPrimitive f (y + a) - realPrimitive f y) / realPrimitive f a := by
    funext y
    rw [realPrimitive_add_sub hf hadd]
    exact (mul_div_cancel_right₀ (f y) ha).symm
  have hshift : HasDerivAt (fun y => realPrimitive f (y + a)) (f (x + a)) x := by
    simpa only [Function.comp_def, one_smul] using! (hasDerivAt_realPrimitive hf (x + a)).scomp x
      ((hasDerivAt_id x).add_const a)
  have hd := (hshift.sub (hasDerivAt_realPrimitive hf x)).div_const (realPrimitive f a)
  change HasDerivAt (fun y =>
    (realPrimitive f (y + a) - realPrimitive f y) / realPrimitive f a)
    ((f (x + a) - f x) / realPrimitive f a) x at hd
  rw [← hformula] at hd
  convert hd using 1
  rw [hadd]
  ring

/-- The integrating-factor argument for a scalar complex differential equation on the real line. -/
theorem eq_exp_of_hasDerivAt_mul {f : ℝ → ℂ} {c : ℂ}
    (hf : ∀ x : ℝ, HasDerivAt f (c * f x) x) (hzero : f 0 = 1) :
    ∀ x : ℝ, f x = Complex.exp (c * x) := by
  let g : ℝ → ℂ := fun x => f x * Complex.exp (-c * x)
  have hg : ∀ x : ℝ, HasDerivAt g 0 x := by
    intro x
    have he : HasDerivAt (fun y : ℝ => Complex.exp (-c * y))
        (Complex.exp (-c * x) * (-c)) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt).const_mul (-c)).cexp (x := x)
    change HasDerivAt (fun y => f y * Complex.exp (-c * y)) 0 x
    convert! (hf x).mul he using 1
    ring
  have hconst : ∀ x : ℝ, g x = g 0 :=
    fun x => is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
      (fun y => (hg y).deriv) x 0
  intro x
  have hx : f x * Complex.exp (-(c * x)) = 1 := by
    simpa [g, hzero, neg_mul] using hconst x
  rw [Complex.exp_neg] at hx
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hx

/-- Continuous complex multiplicative functions on the additive real line are exponentials. -/
theorem exists_complex_exponent {f : ℝ → ℂ} (hf : Continuous f)
    (hzero : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) := by
  obtain ⟨a, ha⟩ := exists_realPrimitive_ne_zero hf hzero
  exact ⟨(f a - 1) / realPrimitive f a,
    eq_exp_of_hasDerivAt_mul (hasDerivAt_exponential_equation hf hadd ha) hzero⟩

/-- Unitarity forces the exponent to be imaginary, with one real frequency. -/
theorem exists_real_frequency {f : ℝ → ℂ} (hf : Continuous f)
    (hzero : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y)
    (hunit : ∀ x, ‖f x‖ = 1) :
    ∃ t : ℝ, ∀ x : ℝ, f x = Complex.exp ((t * x : ℝ) * Complex.I) := by
  obtain ⟨c, hc⟩ := exists_complex_exponent hf hzero hadd
  have hre : c.re = 0 := by
    have hn := hunit 1
    rw [hc, Complex.ofReal_one, mul_one, Complex.norm_exp, Real.exp_eq_one_iff] at hn
    exact hn
  refine ⟨c.im, fun x => ?_⟩
  rw [hc]
  congr 1
  apply Complex.ext <;> simp [hre]

/-- The actual continuous character, viewed on the underlying additive real line. -/
def realCharacterValue (χ : UnitaryCharacter (Multiplicative ℝ)) (x : ℝ) : ℂ :=
  χ (Multiplicative.ofAdd x)

theorem continuous_realCharacterValue (χ : UnitaryCharacter (Multiplicative ℝ)) :
    Continuous (realCharacterValue χ) :=
  continuous_subtype_val.comp χ.continuous

@[simp] theorem realCharacterValue_zero (χ : UnitaryCharacter (Multiplicative ℝ)) :
    realCharacterValue χ 0 = 1 := by simp [realCharacterValue]

theorem realCharacterValue_add (χ : UnitaryCharacter (Multiplicative ℝ)) (x y : ℝ) :
    realCharacterValue χ (x + y) = realCharacterValue χ x * realCharacterValue χ y := by
  exact congrArg (fun z : Circle => (z : ℂ))
    (map_mul χ (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

@[simp] theorem norm_realCharacterValue (χ : UnitaryCharacter (Multiplicative ℝ)) (x : ℝ) :
    ‖realCharacterValue χ x‖ = 1 := Circle.norm_coe _

/-- Classification applies to every continuous unitary character, without a frequency assumption. -/
theorem exists_frequency_realCharacter (χ : UnitaryCharacter (Multiplicative ℝ)) :
    ∃ t : ℝ, ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Circle.exp (t * x) := by
  obtain ⟨t, ht⟩ := exists_real_frequency (continuous_realCharacterValue χ)
    (realCharacterValue_zero χ) (realCharacterValue_add χ) (norm_realCharacterValue χ)
  refine ⟨t, fun x => Subtype.ext ?_⟩
  exact ht x

end HeckeGeneral.Characters
