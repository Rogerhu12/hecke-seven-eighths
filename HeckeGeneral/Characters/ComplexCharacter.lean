import HeckeGeneral.Characters.CircleCharacter
import HeckeGeneral.Characters.RealCharacterFrequency
import Mathlib.Topology.Algebra.GroupWithZero

/-!+# Continuous unitary characters of the nonzero complex numbers

The polar decomposition is implemented on the actual topological unit group.
Every continuous character has a canonical integer angular weight and real
radial frequency. No choice of argument, smoothness, or infinity type is
included in the hypotheses.
-/

noncomputable section

namespace HeckeGeneral.Characters

/-- The compact angular subgroup of the complex unit group. -/
def complexCircleEmbedding : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr continuous_subtype_val

@[simp] theorem complexCircleEmbedding_val (z : Circle) :
    (complexCircleEmbedding z).val = (z : ℂ) := rfl

/-- The positive radial subgroup, parametrized by the logarithm of radius. -/
def complexRadialExponential : Multiplicative ℝ →ₜ* ℂˣ where
  toFun x := Units.mk0 (Real.exp x.toAdd : ℂ) (by exact_mod_cast Real.exp_ne_zero x.toAdd)
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change (Real.exp (x.toAdd + y.toAdd) : ℂ) = _
    rw [Real.exp_add, Complex.ofReal_mul]
    rfl
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
    (Complex.continuous_ofReal.comp Real.continuous_exp)

@[simp] theorem complexRadialExponential_val (x : ℝ) :
    (complexRadialExponential (Multiplicative.ofAdd x)).val = (Real.exp x : ℂ) := rfl

theorem complex_unit_norm_pos (u : ℂˣ) : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero

/-- The phase `z/|z|` is continuous on all of `ℂˣ`, unlike an argument function. -/
def complexPhase : ℂˣ →ₜ* Circle where
  toFun u := ⟨u.val / (‖u.val‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (complex_unit_norm_pos u).ne'⟩
  map_one' := by apply Circle.ext; simp
  map_mul' u v := by
    apply Circle.ext
    change (u.val * v.val) / (‖u.val * v.val‖ : ℂ) =
      (u.val / (‖u.val‖ : ℂ)) * (v.val / (‖v.val‖ : ℂ))
    rw [norm_mul, Complex.ofReal_mul]
    exact mul_div_mul_comm ..
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact Units.continuous_val.div
      (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun u => by
        change (‖u.val‖ : ℂ) ≠ 0
        exact_mod_cast (complex_unit_norm_pos u).ne')

@[simp] theorem complexPhase_val (u : ℂˣ) :
    (complexPhase u : ℂ) = u.val / (‖u.val‖ : ℂ) := rfl

@[simp] theorem complexPhase_circle (z : Circle) :
    complexPhase (complexCircleEmbedding z) = z := by
  apply Circle.ext
  simp

@[simp] theorem complexPhase_radial (x : ℝ) :
    complexPhase (complexRadialExponential (Multiplicative.ofAdd x)) = 1 := by
  apply Circle.ext
  simp [complexPhase_val]

@[simp] theorem norm_complexCircleEmbedding (z : Circle) :
    ‖(complexCircleEmbedding z).val‖ = 1 := Circle.norm_coe z

@[simp] theorem norm_complexRadialExponential (x : ℝ) :
    ‖(complexRadialExponential (Multiplicative.ofAdd x)).val‖ = Real.exp x := by
  rw [complexRadialExponential_val, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos x).le]

/-- Actual multiplicative polar decomposition, inside the unit group. -/
theorem complex_polar_decomposition (u : ℂˣ) :
    complexCircleEmbedding (complexPhase u) *
      complexRadialExponential (Multiplicative.ofAdd (Real.log ‖u.val‖)) = u := by
  apply Units.ext
  change (u.val / (‖u.val‖ : ℂ)) * (Real.exp (Real.log ‖u.val‖) : ℂ) = u.val
  rw [Real.exp_log (complex_unit_norm_pos u)]
  exact div_mul_cancel₀ _ (by exact_mod_cast (complex_unit_norm_pos u).ne')

/-- The canonical integer angular weight of a complex local character. -/
def complexWeight (χ : UnitaryCharacter ℂˣ) : ℤ :=
  circleWeight (χ.comp complexCircleEmbedding)

/-- The canonical real frequency, with respect to the ordinary complex norm. -/
def complexFrequency (χ : UnitaryCharacter ℂˣ) : ℝ :=
  realFrequency (χ.comp complexRadialExponential)

theorem complexCharacter_circle (χ : UnitaryCharacter ℂˣ) (z : Circle) :
    χ (complexCircleEmbedding z) = z ^ complexWeight χ :=
  circleWeight_spec (χ.comp complexCircleEmbedding) z

theorem complexCharacter_radial (χ : UnitaryCharacter ℂˣ) (x : ℝ) :
    χ (complexRadialExponential (Multiplicative.ofAdd x)) =
      Circle.exp (complexFrequency χ * x) :=
  realFrequency_spec (χ.comp complexRadialExponential) x

/-- Classification of every continuous unitary complex local character. -/
theorem complexCharacter_formula (χ : UnitaryCharacter ℂˣ) (u : ℂˣ) :
    χ u = complexPhase u ^ complexWeight χ *
      Circle.exp (complexFrequency χ * Real.log ‖u.val‖) := by
  conv_lhs => rw [← complex_polar_decomposition u]
  rw [map_mul, complexCharacter_circle, complexCharacter_radial]

theorem complexCharacter_parameters_injective {χ ψ : UnitaryCharacter ℂˣ}
    (hw : complexWeight χ = complexWeight ψ) (ht : complexFrequency χ = complexFrequency ψ) :
    χ = ψ := by
  ext u
  rw [complexCharacter_formula χ u, complexCharacter_formula ψ u, hw, ht]

theorem complexWeight_mul (χ ψ : UnitaryCharacter ℂˣ) :
    complexWeight (χ * ψ) = complexWeight χ + complexWeight ψ := by
  exact circleWeight_mul (χ.comp complexCircleEmbedding) (ψ.comp complexCircleEmbedding)

theorem complexFrequency_mul (χ ψ : UnitaryCharacter ℂˣ) :
    complexFrequency (χ * ψ) = complexFrequency χ + complexFrequency ψ := by
  exact realFrequency_mul (χ.comp complexRadialExponential) (ψ.comp complexRadialExponential)

@[simp] theorem complexWeight_one : complexWeight (1 : UnitaryCharacter ℂˣ) = 0 := circleWeight_one

@[simp] theorem complexFrequency_one : complexFrequency (1 : UnitaryCharacter ℂˣ) = 0 :=
  realFrequency_one

theorem complexWeight_inv (χ : UnitaryCharacter ℂˣ) :
    complexWeight χ⁻¹ = -complexWeight χ :=
  circleWeight_inv (χ.comp complexCircleEmbedding)

theorem complexFrequency_inv (χ : UnitaryCharacter ℂˣ) :
    complexFrequency χ⁻¹ = -complexFrequency χ :=
  realFrequency_inv (χ.comp complexRadialExponential)

theorem complexWeight_pow (χ : UnitaryCharacter ℂˣ) (n : ℕ) :
    complexWeight (χ ^ n) = n * complexWeight χ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, complexWeight_mul, ih]; push_cast; ring

theorem complexFrequency_pow (χ : UnitaryCharacter ℂˣ) (n : ℕ) :
    complexFrequency (χ ^ n) = n * complexFrequency χ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, complexFrequency_mul, ih]; push_cast; ring

/-- Finite-order continuous characters are trivial at complex infinite places. -/
theorem finiteOrder_complexCharacter_iff (χ : UnitaryCharacter ℂˣ) : FiniteOrder χ ↔ χ = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ := finiteOrder_iff χ |>.mp h
    have hw : complexWeight χ = 0 := by
      have he := congrArg complexWeight hpow
      rw [complexWeight_pow, complexWeight_one] at he
      exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast hn.ne')
    have ht : complexFrequency χ = 0 := by
      have he := congrArg complexFrequency hpow
      rw [complexFrequency_pow, complexFrequency_one] at he
      exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast hn.ne')
    apply complexCharacter_parameters_injective <;> simpa
  · rintro rfl
    exact (finiteOrder_iff _).mpr ⟨1, Nat.zero_lt_one, by simp⟩

end HeckeGeneral.Characters
