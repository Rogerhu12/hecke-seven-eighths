import Expansion.SmoothDyadicPartition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-! Support geometry of the actual inverse/terminal cutoffs.  These are
exact consequences of the explicit profiles, prior to every norm estimate. -/
set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open scoped Classical BigOperators

def pairCutoff (Dstar H x y : ℝ) : ℂ :=
  (cutoff (x / Dstar) : ℂ) * (1 - (cutoff (2 * (x * y) / Dstar) : ℂ)) *
    (cutoff (x * y / H) : ℂ)

theorem pairCutoff_support {Dstar H x y : ℝ}
    (hD : 0 < Dstar) (hH : 0 < H)
    (h : pairCutoff Dstar H x y ≠ 0) :
    x < 2 * Dstar ∧ Dstar / 2 < x * y ∧ x * y < 2 * H := by
  have hprod := mul_ne_zero_iff.mp h
  have hleft := mul_ne_zero_iff.mp hprod.1
  have hx : x / Dstar < 2 := by
    apply lt_of_not_ge
    intro hx
    exact hleft.1 (by rw [cutoff_zero hx]; simp)
  have hxy : 1 < 2 * (x * y) / Dstar := by
    apply lt_of_not_ge
    intro hxy
    exact hleft.2 (by rw [cutoff_one hxy]; simp)
  have hHxy : x * y / H < 2 := by
    apply lt_of_not_ge
    intro hxy
    exact hprod.2 (by rw [cutoff_zero hxy]; simp)
  have hx' := (div_lt_iff₀ hD).mp hx
  have hxy' := (lt_div_iff₀ hD).mp hxy
  have hHxy' := (div_lt_iff₀ hH).mp hHxy
  exact ⟨hx', by linarith, hHxy'⟩

theorem annular_scaled_support {x D : ℝ} (hD : 0 < D)
    (hw : annularProfile (x / D) ≠ 0) :
    D / 2 < x ∧ x < 2 * D := by
  have hn : annular (x / D) ≠ 0 := by
    intro h
    exact hw (by simp [annularProfile, h])
  have hb := annular_nonzero_bounds hn
  have hl := (lt_div_iff₀ hD).mp hb.1
  exact ⟨by linarith, (div_lt_iff₀ hD).mp hb.2⟩

/-- Every nonzero dyadic summand has the claimed inverse length, total
length, and terminal support.  There is no spike assumption here. -/
theorem nonzero_pair_scale_bounds {Dstar H D E x y : ℝ}
    (hDs : 0 < Dstar) (hH : 0 < H) (hD : 0 < D) (hE : 0 < E)
    (hcut : pairCutoff Dstar H x y ≠ 0)
    (hW : annularProfile (x / D) ≠ 0)
    (hV : annularProfile (y / E) ≠ 0) :
    D < 4 * Dstar ∧ Dstar / 8 < D * E ∧ D * E < 8 * H := by
  have hc := pairCutoff_support hDs hH hcut
  have hx := annular_scaled_support hD hW
  have hy := annular_scaled_support hE hV
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hupper : x * y < (2 * D) * (2 * E) :=
    (mul_lt_mul_of_pos_right hx.2 hy0).trans
      (mul_lt_mul_of_pos_left hy.2 (by positivity))
  have hlower : (D / 2) * (E / 2) < x * y :=
    (mul_lt_mul_of_pos_right hx.1 (by positivity : 0 < E / 2)).trans
      (mul_lt_mul_of_pos_left hy.1 hx0)
  exact ⟨by linarith, by nlinarith, by nlinarith⟩

variable {ι κ : Type*}

/-- This statement consumes the literal cutoff factors of each coefficient,
so a large block automatically belongs to the finite admissible schedule. -/
theorem pairBlock_scale_bounds (pairs : Finset (ι × κ))
    (core : ι × κ → ℂ) (N : ι → ℝ) (M : κ → ℝ)
    {Dstar H : ℝ} (hDs : 0 < Dstar) (hH : 0 < H) (j k : ℕ)
    (hblock : pairBlock pairs
      (fun p => core p * pairCutoff Dstar H (N p.1) (M p.2)) N M j k ≠ 0) :
    (2 : ℝ) ^ j < 4 * Dstar ∧
      Dstar / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
      (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * H := by
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  have h1 := mul_ne_zero_iff.mp hne
  have h2 := mul_ne_zero_iff.mp h1.1
  have h3 := mul_ne_zero_iff.mp h2.1
  exact nonzero_pair_scale_bounds hDs hH (by positivity) (by positivity)
    h3.2 h2.2 h1.2

/-- Converting support geometry to row-base exponents has only the explicit
logarithmic endpoint losses; these are uniform over every retained pair. -/
theorem witness_length_bounds {U r m t : ℝ} (hU : 1 < U)
    (hD : U ^ r < 4 * U ^ t)
    (hprod : U ^ t / 8 < U ^ r * U ^ m) :
    r < t + Real.log 4 / Real.log U ∧
      t - Real.log 8 / Real.log U < r + m := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlog : 0 < Real.log U := Real.log_pos hU
  have hDlog := Real.log_lt_log (Real.rpow_pos_of_pos hU0 r) hD
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hU0 t).ne', Real.log_rpow hU0, Real.log_rpow hU0] at hDlog
  have hplog := Real.log_lt_log
    (div_pos (Real.rpow_pos_of_pos hU0 t) (by norm_num : (0 : ℝ) < 8)) hprod
  rw [Real.log_div (Real.rpow_pos_of_pos hU0 t).ne' (by norm_num : (8 : ℝ) ≠ 0),
    Real.log_mul (Real.rpow_pos_of_pos hU0 r).ne' (Real.rpow_pos_of_pos hU0 m).ne',
    Real.log_rpow hU0, Real.log_rpow hU0, Real.log_rpow hU0] at hplog
  constructor
  · have hh : r - t < Real.log 4 / Real.log U := by
      apply (lt_div_iff₀ hlog).mpr
      nlinarith
    linarith
  · have hh : t - (r + m) < Real.log 8 / Real.log U := by
      apply (lt_div_iff₀ hlog).mpr
      nlinarith
    linarith

def dyadicCap (R : ℝ) : ℕ := ⌈Real.log R / Real.log 2⌉₊

theorem le_two_pow_dyadicCap {R : ℝ} (hR : 0 < R) :
    R ≤ (2 : ℝ) ^ dyadicCap R := by
  apply (Real.le_pow_iff_log_le hR (by norm_num : (0 : ℝ) < 2)).mpr
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    (Nat.le_ceil (Real.log R / Real.log 2))

/-- The finite cap for H = U^21 is logarithmic in U, with a fixed additive
constant.  This is the count used before any Fourier frequency is selected. -/
theorem dyadicCap_terminal_le {U : ℝ} (hU : 1 ≤ U) :
    (dyadicCap (3 * U ^ (21 : ℝ)) : ℝ) ≤
      (21 / Real.log 2) * Real.log U + (Real.log 3 / Real.log 2 + 1) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 1 ≤ 3 * U ^ (21 : ℝ) := by
    have hpow := Real.one_le_rpow hU (by norm_num : (0 : ℝ) ≤ 21)
    linarith
  have hquot : 0 ≤ Real.log (3 * U ^ (21 : ℝ)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hR) (Real.log_pos (by norm_num)).le
  have hn := Nat.ceil_lt_add_one hquot
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hU0 21).ne', Real.log_rpow hU0] at hn
  dsimp [dyadicCap]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hU0 21).ne', Real.log_rpow hU0]
  calc
    _ ≤ (Real.log 3 + 21 * Real.log U) / Real.log 2 + 1 := hn.le
    _ = _ := by ring

end Expansion.Dyadic
