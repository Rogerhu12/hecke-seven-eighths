import HeckeGeneral.Characters.RealAdditiveCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Integer weights of continuous circle characters

Pulling back along the actual exponential map reduces the classification to
the real additive line. Its period forces the frequency to be an integer,
and surjectivity of the exponential recovers the original circle character.
-/

noncomputable section

namespace HeckeGeneral.Characters

/-- The universal real exponential, bundled as a continuous multiplicative homomorphism. -/
def realCircleExponential : Multiplicative ℝ →ₜ* Circle where
  toFun x := Circle.exp x.toAdd
  map_one' := Circle.exp_zero
  map_mul' x y := Circle.exp_add x.toAdd y.toAdd
  continuous_toFun := Circle.exp.continuous

@[simp] theorem realCircleExponential_ofAdd (x : ℝ) :
    realCircleExponential (Multiplicative.ofAdd x) = Circle.exp x := rfl

theorem realCircleExponential_surjective : Function.Surjective realCircleExponential :=
  fun z => by
    obtain ⟨x, hx⟩ := Circle.exp_surjective z
    exact ⟨Multiplicative.ofAdd x, hx⟩

/-- Every continuous circle character is an integral power, with no smoothness hypothesis. -/
theorem exists_integer_weight (χ : UnitaryCharacter Circle) :
    ∃ m : ℤ, ∀ z : Circle, χ z = z ^ m := by
  obtain ⟨t, ht⟩ := exists_frequency_realCharacter (χ.comp realCircleExponential)
  have hperiod : Circle.exp (t * (2 * Real.pi)) = 1 := by
    rw [← ht]
    change χ (Circle.exp (2 * Real.pi)) = 1
    simp
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hperiod
  have htint : t = (m : ℝ) := mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hm
  refine ⟨m, fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Circle.exp_surjective z
  have hx := ht x
  change χ (Circle.exp x) = Circle.exp (t * x) at hx
  rw [hx, htint, Circle.exp_intCast_mul]

/-- The integer weight is unique; this is not merely a chosen presentation. -/
theorem integer_weight_unique {m n : ℤ}
    (h : ∀ z : Circle, z ^ m = z ^ n) : m = n := by
  by_contra hmn
  have hdiff : ((m - n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn
  let x : ℝ := Real.pi / ((m - n : ℤ) : ℝ)
  have hexp : Circle.exp (((m - n : ℤ) : ℝ) * x) = 1 := by
    rw [Circle.exp_intCast_mul, zpow_sub]
    exact div_eq_one.mpr (h (Circle.exp x))
  have hmul : ((m - n : ℤ) : ℝ) * x = Real.pi := by
    dsimp [x]
    field_simp
  rw [hmul] at hexp
  exact Circle.exp_pi_ne_one hexp

/-- The unique angular weight of an actual continuous circle character. -/
def circleWeight (χ : UnitaryCharacter Circle) : ℤ := Classical.choose (exists_integer_weight χ)

theorem circleWeight_spec (χ : UnitaryCharacter Circle) (z : Circle) :
    χ z = z ^ circleWeight χ := Classical.choose_spec (exists_integer_weight χ) z

theorem circleWeight_eq_iff (χ : UnitaryCharacter Circle) (m : ℤ) :
    circleWeight χ = m ↔ ∀ z : Circle, χ z = z ^ m := by
  constructor
  · intro hm z
    rw [circleWeight_spec, hm]
  · intro hm
    exact integer_weight_unique fun z => (circleWeight_spec χ z).symm.trans (hm z)

theorem circleWeight_mul (χ ψ : UnitaryCharacter Circle) :
    circleWeight (χ * ψ) = circleWeight χ + circleWeight ψ := by
  apply (circleWeight_eq_iff _ _).mpr
  intro z
  change χ z * ψ z = _
  rw [circleWeight_spec, circleWeight_spec, zpow_add]

@[simp] theorem circleWeight_one : circleWeight (1 : UnitaryCharacter Circle) = 0 := by
  apply (circleWeight_eq_iff _ _).mpr
  simp

theorem circleWeight_inv (χ : UnitaryCharacter Circle) : circleWeight χ⁻¹ = -circleWeight χ := by
  apply (circleWeight_eq_iff _ _).mpr
  intro z
  change (χ z)⁻¹ = _
  rw [circleWeight_spec, zpow_neg]

theorem finiteOrder_circleCharacter_iff (χ : UnitaryCharacter Circle) : FiniteOrder χ ↔ χ = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ := finiteOrder_iff_pointwise χ |>.mp h
    have he : circleWeight χ * (n : ℤ) = 0 := by
      apply integer_weight_unique
      intro z
      simpa only [zpow_zero, zpow_mul, zpow_natCast, ← circleWeight_spec] using hpow z
    have hm : circleWeight χ = 0 := (mul_eq_zero.mp he).resolve_right (by exact_mod_cast hn.ne')
    ext z
    simp [circleWeight_spec, hm]
  · rintro rfl
    exact (finiteOrder_iff _).mpr ⟨1, Nat.zero_lt_one, by simp⟩

end HeckeGeneral.Characters
