import HeckeGeneral.Characters.InfinityType
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!+# Actual angular cancellation at a complex place

We integrate rotations through a full angle `2π`. Integer modes are orthogonal,
and an actual complex local Hecke character of nonzero weight kills every
rotation-invariant factor. This gives the local constant-term cancellation
mechanism, without postulating a theta constant-term formula.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Characters NumberField
open scoped ComplexConjugate

def angularMode (m : ℤ) (θ : ℝ) : ℂ := (Circle.exp θ : ℂ) ^ m

theorem angularMode_exp (m : ℤ) (θ : ℝ) :
    angularMode m θ = Complex.exp (((m : ℂ) * Complex.I) * θ) := by
  have h := congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_intCast_mul θ m)
  change Complex.exp (((m : ℝ) * θ : ℝ) * Complex.I) = angularMode m θ at h
  rw [← h]
  congr 1
  push_cast
  ring

theorem angularMode_zero_angle (m : ℤ) : angularMode m 0 = 1 := by simp [angularMode]

theorem angularMode_full_angle (m : ℤ) : angularMode m (2 * Real.pi) = 1 := by
  change ((Circle.exp (2 * Real.pi) : Circle) : ℂ) ^ m = 1
  rw [Circle.exp_two_pi, Circle.coe_one, one_zpow]

theorem continuous_angularMode (m : ℤ) : Continuous (angularMode m) := by
  have he : angularMode m = fun θ : ℝ => Complex.exp (((m : ℂ) * Complex.I) * θ) :=
    funext (angularMode_exp m)
  rw [he]
  fun_prop

theorem integral_angularMode_of_ne_zero {m : ℤ} (hm : m ≠ 0) :
    (∫ θ : ℝ in 0..2 * Real.pi, angularMode m θ) = 0 := by
  simp_rw [angularMode_exp]
  rw [integral_exp_mul_complex
    (mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero)]
  rw [← angularMode_exp, ← angularMode_exp, angularMode_full_angle, angularMode_zero_angle,
    sub_self, zero_div]

def angularAverage (f : ℝ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, f θ

theorem angularAverage_mode (m : ℤ) : angularAverage (angularMode m) = if m = 0 then 1 else 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [angularAverage, angularMode, intervalIntegral.integral_const]
    field_simp
  · rw [angularAverage, integral_angularMode_of_ne_zero hm, mul_zero, ite_eq_right hm]

theorem angularMode_conj_mul (m n : ℤ) (θ : ℝ) :
    angularMode m θ * conj (angularMode n θ) = angularMode (m - n) θ := by
  change ((Circle.exp θ ^ m : Circle) : ℂ) *
    conj ((Circle.exp θ ^ n : Circle) : ℂ) = ((Circle.exp θ ^ (m - n) : Circle) : ℂ)
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  exact congrArg (fun z : Circle => (z : ℂ)) (zpow_sub (Circle.exp θ) m n).symm

/-- Orthogonality with normalized angular measure. -/
theorem angularAverage_orthogonal (m n : ℤ) :
    angularAverage (fun θ => angularMode m θ * conj (angularMode n θ)) =
      if m = n then 1 else 0 := by
  simp_rw [angularMode_conj_mul]
  simp only [angularAverage_mode, sub_eq_zero]

def complexRotation (θ : ℝ) : ℂˣ := complexCircleEmbedding (Circle.exp θ)

theorem complexCharacter_rotation (χ : UnitaryCharacter ℂˣ) (θ : ℝ) :
    (χ (complexRotation θ) : ℂ) = angularMode (complexWeight χ) θ := by
  rw [complexRotation, complexCharacter_circle]
  rfl

/-- Rotation leaves the ordinary radius, hence every radial factor, unchanged. -/
theorem norm_complexRotation_mul (θ : ℝ) (u : ℂˣ) :
    ‖(complexRotation θ * u).val‖ = ‖u.val‖ := by
  change ‖(complexCircleEmbedding (Circle.exp θ)).val * u.val‖ = _
  rw [norm_mul, norm_complexCircleEmbedding, one_mul]

def characterAngularAverage (χ : UnitaryCharacter ℂˣ) (f : ℂˣ → ℂ) (u : ℂˣ) : ℂ :=
  angularAverage (fun θ => (χ (complexRotation θ * u) : ℂ) * f (complexRotation θ * u))

/-- The full angular integral of a rotation-invariant factor is selected by the actual weight. -/
theorem characterAngularAverage_invariant (χ : UnitaryCharacter ℂˣ) (f : ℂˣ → ℂ)
    (u : ℂˣ) (hf : ∀ θ, f (complexRotation θ * u) = f u) :
    characterAngularAverage χ f u =
      (if complexWeight χ = 0 then 1 else 0) * ((χ u : ℂ) * f u) := by
  unfold characterAngularAverage angularAverage
  have he : (fun θ => (χ (complexRotation θ * u) : ℂ) * f (complexRotation θ * u)) =
      fun θ => angularMode (complexWeight χ) θ * ((χ u : ℂ) * f u) := by
    funext θ
    rw [hf, map_mul, Circle.coe_mul, complexCharacter_rotation]
    ring
  rw [he, intervalIntegral.integral_mul_const, ← mul_assoc]
  exact congrArg (fun z => z * ((χ u : ℂ) * f u)) (angularAverage_mode (complexWeight χ))

theorem characterAngularAverage_eq_zero (χ : UnitaryCharacter ℂˣ) (f : ℂˣ → ℂ)
    (u : ℂˣ) (hm : complexWeight χ ≠ 0) (hf : ∀ θ, f (complexRotation θ * u) = f u) :
    characterAngularAverage χ f u = 0 := by
  rw [characterAngularAverage_invariant χ f u hf, ite_eq_right hm, zero_mul]

theorem characterAngularAverage_radial_eq_zero (χ : UnitaryCharacter ℂˣ) (F : ℝ → ℂ)
    (u : ℂˣ) (hm : complexWeight χ ≠ 0) :
    characterAngularAverage χ (fun z => F ‖z.val‖) u = 0 :=
  characterAngularAverage_eq_zero χ _ u hm (fun θ => congrArg F (norm_complexRotation_mul θ u))

/-- Nonzero angular weight of the actual Hecke restriction cancels any radial local factor. -/
theorem hecke_angular_radial_cancellation (K : Type*) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : v.IsComplex) (χ : HeckeCharacter K) (F : ℝ → ℂ)
    (u : ℂˣ) (hm : heckeComplexWeight K v hv χ ≠ 0) :
    characterAngularAverage (complexHeckeComponent K v hv χ) (fun z => F ‖z.val‖) u = 0 :=
  characterAngularAverage_radial_eq_zero _ F u hm

end HeckeGeneral.Analysis
