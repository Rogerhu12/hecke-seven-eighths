import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Tactic.Linarith

/-! The explicit arc `re z > 1/2` contains no nontrivial subgroup of the circle. -/

noncomputable section

namespace HeckeGeneral.Characters

open scoped BigOperators
open Filter Topology

theorem circle_eq_one_of_powers_re (z : Circle)
    (h : ∀ n : ℕ, (1 / 2 : ℝ) ≤ (↑(z ^ n) : ℂ).re) : z = 1 := by
  by_contra hz
  have hc : (z : ℂ) - 1 ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    exact sub_eq_zero.mp he
  have hd : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.mpr hc
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ‖(z : ℂ) - 1‖)
  let s : ℂ := ∑ k ∈ Finset.range n, (z : ℂ) ^ k
  have hre : (n : ℝ) / 2 ≤ s.re := by
    have hs := Finset.sum_le_sum (s := Finset.range n)
      (f := fun _ : ℕ => (1 / 2 : ℝ)) (g := fun k => ((z : ℂ) ^ k).re)
      (fun k _ => by simpa using h k)
    simpa [s, Complex.re_sum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hs
  have hbound : ‖s‖ * ‖(z : ℂ) - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      ‖(z : ℂ) ^ n - 1‖ ≤ ‖(z : ℂ) ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, Circle.norm_coe]
  have hreal : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hn' : 4 < (n : ℝ) * ‖(z : ℂ) - 1‖ := (div_lt_iff₀ hd).mp hn
  nlinarith

def circleSmallArc : Set Circle := {z | (1 / 2 : ℝ) < (z : ℂ).re}

theorem isOpen_circleSmallArc : IsOpen circleSmallArc :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

theorem one_mem_circleSmallArc : (1 : Circle) ∈ circleSmallArc := by
  change (1 / 2 : ℝ) < (1 : ℂ).re
  norm_num

theorem eq_one_of_range_in_circleSmallArc {G : Type*} [Monoid G]
    (f : G →* Circle) (h : ∀ x, f x ∈ circleSmallArc) (x : G) : f x = 1 := by
  apply circle_eq_one_of_powers_re
  intro n
  have hn := h (x ^ n)
  change (1 / 2 : ℝ) < (f (x ^ n) : ℂ).re at hn
  rw [map_pow] at hn
  exact le_of_lt hn

end HeckeGeneral.Characters
