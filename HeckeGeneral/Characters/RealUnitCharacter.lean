import HeckeGeneral.Characters.RealCharacterFrequency
import Mathlib.Topology.Algebra.GroupWithZero

/-!+# Continuous unitary characters of the nonzero real numbers

The positive component is classified by a real frequency. The value at `-1`
records the remaining sign character and has order at most two. This keeps
real-place parity separate from the radial parameters and proves exactly what
finite-order twisting can change at a real infinite place.
-/

noncomputable section

namespace HeckeGeneral.Characters

def realRadialExponential : Multiplicative ℝ →ₜ* ℝˣ where
  toFun x := Units.mk0 (Real.exp x.toAdd) (Real.exp_ne_zero _)
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change Real.exp (x.toAdd + y.toAdd) = _
    exact Real.exp_add ..
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp

@[simp] theorem realRadialExponential_val (x : ℝ) :
    (realRadialExponential (Multiplicative.ofAdd x)).val = Real.exp x := rfl

def realUnitFrequency (χ : UnitaryCharacter ℝˣ) : ℝ :=
  realFrequency (χ.comp realRadialExponential)

def realUnitSign (χ : UnitaryCharacter ℝˣ) : Circle := χ (-1)

theorem realUnitSign_sq (χ : UnitaryCharacter ℝˣ) : realUnitSign χ ^ 2 = 1 := by
  rw [realUnitSign, ← map_pow]
  norm_num

/-- The two possible sign values, proved inside the actual complex unit circle. -/
theorem realUnitSign_eq_one_or_neg_one (χ : UnitaryCharacter ℝˣ) :
    realUnitSign χ = 1 ∨ realUnitSign χ = -1 := by
  have h : (realUnitSign χ : ℂ) ^ 2 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using
      congrArg (fun z : Circle => (z : ℂ)) (realUnitSign_sq χ)
  rcases sq_eq_one_iff.mp h with h | h
  · exact Or.inl (Circle.ext h)
  · exact Or.inr (Circle.ext h)

theorem realCharacter_radial (χ : UnitaryCharacter ℝˣ) (x : ℝ) :
    χ (realRadialExponential (Multiplicative.ofAdd x)) =
      Circle.exp (realUnitFrequency χ * x) :=
  realFrequency_spec (χ.comp realRadialExponential) x

theorem real_positive_decomposition (u : ℝˣ) (hu : 0 < u.val) :
    realRadialExponential (Multiplicative.ofAdd (Real.log |u.val|)) = u := by
  apply Units.ext
  change Real.exp (Real.log |u.val|) = u.val
  rw [abs_of_pos hu, Real.exp_log hu]

theorem real_negative_decomposition (u : ℝˣ) (hu : u.val < 0) :
    (-1 : ℝˣ) * realRadialExponential (Multiplicative.ofAdd (Real.log |u.val|)) = u := by
  apply Units.ext
  change -1 * Real.exp (Real.log |u.val|) = u.val
  rw [Real.exp_log (abs_pos.mpr u.ne_zero), abs_of_neg hu]
  ring

/-- Classification without a preselected parity or radial frequency. -/
theorem realCharacter_formula (χ : UnitaryCharacter ℝˣ) (u : ℝˣ) :
    χ u = (if 0 < u.val then 1 else realUnitSign χ) *
      Circle.exp (realUnitFrequency χ * Real.log |u.val|) := by
  by_cases hu : 0 < u.val
  · rw [ite_eq_left hu, one_mul, ← realCharacter_radial]
    rw [real_positive_decomposition u hu]
  · have hneg : u.val < 0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
    rw [ite_eq_right hu, ← realCharacter_radial, realUnitSign, ← map_mul]
    rw [real_negative_decomposition u hneg]

theorem realCharacter_parameters_injective {χ ψ : UnitaryCharacter ℝˣ}
    (hs : realUnitSign χ = realUnitSign ψ) (ht : realUnitFrequency χ = realUnitFrequency ψ) :
    χ = ψ := by
  ext u
  rw [realCharacter_formula χ u, realCharacter_formula ψ u, hs, ht]

theorem realUnitFrequency_mul (χ ψ : UnitaryCharacter ℝˣ) :
    realUnitFrequency (χ * ψ) = realUnitFrequency χ + realUnitFrequency ψ :=
  realFrequency_mul (χ.comp realRadialExponential) (ψ.comp realRadialExponential)

theorem realUnitSign_mul (χ ψ : UnitaryCharacter ℝˣ) :
    realUnitSign (χ * ψ) = realUnitSign χ * realUnitSign ψ := rfl

@[simp] theorem realUnitFrequency_one : realUnitFrequency (1 : UnitaryCharacter ℝˣ) = 0 :=
  realFrequency_one

@[simp] theorem realUnitSign_one : realUnitSign (1 : UnitaryCharacter ℝˣ) = 1 := rfl

theorem realUnitFrequency_inv (χ : UnitaryCharacter ℝˣ) :
    realUnitFrequency χ⁻¹ = -realUnitFrequency χ :=
  realFrequency_inv (χ.comp realRadialExponential)

theorem realUnitSign_inv (χ : UnitaryCharacter ℝˣ) : realUnitSign χ⁻¹ = (realUnitSign χ)⁻¹ := rfl

theorem realUnitFrequency_pow (χ : UnitaryCharacter ℝˣ) (n : ℕ) :
    realUnitFrequency (χ ^ n) = n * realUnitFrequency χ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, realUnitFrequency_mul, ih]; push_cast; ring

theorem realUnitSign_pow (χ : UnitaryCharacter ℝˣ) (n : ℕ) :
    realUnitSign (χ ^ n) = realUnitSign χ ^ n := by simp [realUnitSign]

/-- The radial frequency is the only obstruction to finite order at a real place. -/
theorem finiteOrder_realUnitCharacter_iff (χ : UnitaryCharacter ℝˣ) :
    FiniteOrder χ ↔ realUnitFrequency χ = 0 := by
  constructor
  · intro h
    obtain ⟨n, hn, he⟩ := finiteOrder_iff χ |>.mp h
    have ht := congrArg realUnitFrequency he
    rw [realUnitFrequency_pow, realUnitFrequency_one] at ht
    exact (mul_eq_zero.mp ht).resolve_left (by exact_mod_cast hn.ne')
  · intro ht
    apply (finiteOrder_iff _).mpr
    refine ⟨2, by norm_num, ?_⟩
    apply realCharacter_parameters_injective
    · rw [realUnitSign_pow, realUnitSign_sq, realUnitSign_one]
    · rw [realUnitFrequency_pow, ht, mul_zero, realUnitFrequency_one]

theorem realCharacter_sq_eq_one_of_finiteOrder {χ : UnitaryCharacter ℝˣ} (hχ : FiniteOrder χ) :
    χ ^ 2 = 1 := by
  apply realCharacter_parameters_injective
  · rw [realUnitSign_pow, realUnitSign_sq, realUnitSign_one]
  · rw [realUnitFrequency_pow, (finiteOrder_realUnitCharacter_iff χ).mp hχ,
      mul_zero, realUnitFrequency_one]

theorem finiteOrder_realUnitCharacter_trivial_on_positive {χ : UnitaryCharacter ℝˣ}
    (hχ : FiniteOrder χ) (u : ℝˣ) (hu : 0 < u.val) : χ u = 1 := by
  rw [realCharacter_formula, (finiteOrder_realUnitCharacter_iff χ).mp hχ,
    ite_eq_left hu, zero_mul, Circle.exp_zero, mul_one]

end HeckeGeneral.Characters
