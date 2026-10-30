import HeckeGeneral.Characters.RealAdditiveCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!+# Canonical frequencies and their arithmetic

The classification of continuous characters of the additive real line has a
unique real parameter. This file records its behavior under character products,
integer powers, rescaling, and finite-order twists. These properties are used
to keep track of the radial parameters of an actual Hecke-character packet.
-/

noncomputable section

namespace HeckeGeneral.Characters

theorem real_frequency_unique {t u : ℝ}
    (h : ∀ x : ℝ, Circle.exp (t * x) = Circle.exp (u * x)) : t = u := by
  by_contra htu
  have hd : t - u ≠ 0 := sub_ne_zero.mpr htu
  have hexp : Circle.exp ((t - u) * (Real.pi / (t - u))) = 1 := by
    rw [sub_mul, Circle.exp_sub]
    exact div_eq_one.mpr (h _)
  rw [mul_div_cancel₀ _ hd] at hexp
  exact Circle.exp_pi_ne_one hexp

/-- The canonical real frequency, obtained from continuity rather than assumed. -/
def realFrequency (χ : UnitaryCharacter (Multiplicative ℝ)) : ℝ :=
  Classical.choose (exists_frequency_realCharacter χ)

theorem realFrequency_spec (χ : UnitaryCharacter (Multiplicative ℝ)) (x : ℝ) :
    χ (Multiplicative.ofAdd x) = Circle.exp (realFrequency χ * x) :=
  Classical.choose_spec (exists_frequency_realCharacter χ) x

theorem realFrequency_eq_iff (χ : UnitaryCharacter (Multiplicative ℝ)) (t : ℝ) :
    realFrequency χ = t ↔ ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Circle.exp (t * x) := by
  constructor
  · intro ht x
    rw [realFrequency_spec, ht]
  · intro ht
    exact real_frequency_unique fun x => (realFrequency_spec χ x).symm.trans (ht x)

theorem realFrequency_injective : Function.Injective realFrequency := by
  intro χ ψ h
  ext x
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [realFrequency_spec, realFrequency_spec, h]

/-- The actual character of frequency `t`. -/
def frequencyCharacter (t : ℝ) : UnitaryCharacter (Multiplicative ℝ) where
  toFun x := Circle.exp (t * x.toAdd)
  map_one' := by simp
  map_mul' x y := by
    change Circle.exp (t * (x.toAdd + y.toAdd)) = _
    rw [mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_id)

@[simp] theorem frequencyCharacter_apply (t x : ℝ) :
    frequencyCharacter t (Multiplicative.ofAdd x) = Circle.exp (t * x) := rfl

@[simp] theorem realFrequency_frequencyCharacter (t : ℝ) :
    realFrequency (frequencyCharacter t) = t :=
  (realFrequency_eq_iff _ _).mpr fun _ => rfl

theorem frequencyCharacter_realFrequency (χ : UnitaryCharacter (Multiplicative ℝ)) :
    frequencyCharacter (realFrequency χ) = χ := by
  apply realFrequency_injective
  rw [realFrequency_frequencyCharacter]

theorem realFrequency_mul (χ ψ : UnitaryCharacter (Multiplicative ℝ)) :
    realFrequency (χ * ψ) = realFrequency χ + realFrequency ψ := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  change χ (Multiplicative.ofAdd x) * ψ (Multiplicative.ofAdd x) = _
  rw [realFrequency_spec, realFrequency_spec, add_mul, Circle.exp_add]

@[simp] theorem realFrequency_one : realFrequency (1 : UnitaryCharacter (Multiplicative ℝ)) = 0 := by
  apply (realFrequency_eq_iff _ _).mpr
  simp

theorem realFrequency_inv (χ : UnitaryCharacter (Multiplicative ℝ)) :
    realFrequency χ⁻¹ = -realFrequency χ := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  change (χ (Multiplicative.ofAdd x))⁻¹ = _
  rw [realFrequency_spec, neg_mul, Circle.exp_neg]

theorem realFrequency_pow (χ : UnitaryCharacter (Multiplicative ℝ)) (n : ℕ) :
    realFrequency (χ ^ n) = n * realFrequency χ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, realFrequency_mul, ih]; push_cast; ring

theorem realFrequency_zpow (χ : UnitaryCharacter (Multiplicative ℝ)) (n : ℤ) :
    realFrequency (χ ^ n) = n * realFrequency χ := by
  cases n with
  | ofNat n => simpa using realFrequency_pow χ n
  | negSucc n =>
    rw [zpow_negSucc, realFrequency_inv, realFrequency_pow]
    push_cast
    ring

/-- A finite-order continuous character is trivial on the connected real line. -/
theorem finiteOrder_realCharacter_iff (χ : UnitaryCharacter (Multiplicative ℝ)) :
    FiniteOrder χ ↔ χ = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn, hpow⟩ := finiteOrder_iff χ |>.mp h
    have ht : realFrequency χ = 0 := by
      have he := congrArg realFrequency hpow
      rw [realFrequency_pow, realFrequency_one] at he
      exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast hn.ne')
    apply realFrequency_injective
    simpa using ht
  · rintro rfl
    exact (finiteOrder_iff _).mpr ⟨1, Nat.zero_lt_one, by simp⟩

/-- Rescaling the line multiplies the character frequency by the same real factor. -/
def realLineRescale (a : ℝ) : Multiplicative ℝ →ₜ* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (a * x.toAdd)
  map_one' := by change a * 0 = 0; simp
  map_mul' x y := by change a * (x.toAdd + y.toAdd) = _; exact mul_add ..
  continuous_toFun := by
    change Continuous (fun x : ℝ => a * x)
    exact continuous_const.mul continuous_id

theorem realFrequency_comp_rescale (χ : UnitaryCharacter (Multiplicative ℝ)) (a : ℝ) :
    realFrequency (χ.comp (realLineRescale a)) = a * realFrequency χ := by
  apply (realFrequency_eq_iff _ _).mpr
  intro x
  change χ (Multiplicative.ofAdd (a * x)) = _
  rw [realFrequency_spec]
  congr 1
  ring

end HeckeGeneral.Characters
