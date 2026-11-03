import HeckeGeneral.Analysis.RowEulerRational
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Rational Euler-factor cancellation, including the removable W=1 locus. -/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighEulerAlgebra

/-- The actual rational correction from the verified main library. -/
abbrev rowEulerCancelledValue :=
  HeckeGeneral.ThetaSkeleton.Physical.rowEulerRationalValue

theorem rowEulerRational_eq_cancelled (q qInv V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    (((1 - V)⁻¹ + W / (1 - W) +
        E / (1 - E) * ((1 - qInv) / (1 - V) + W) -
        D / (1 - E) * (1 + (q - 1) * W * V / (1 - V))) *
      (1 - V) * (1 - W) / (1 - D)) =
      rowEulerCancelledValue q qInv V W D E :=
  HeckeGeneral.ThetaSkeleton.Physical.rowEulerLiteral_eq_rational
    q qInv V W D E hV hW hE hD

theorem rowEulerCancelledValue_W_one (q qInv V D E : ℂ)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    rowEulerCancelledValue q qInv V 1 D E = (1 - V) / (1 - D) :=
  HeckeGeneral.ThetaSkeleton.Physical.rowEulerRationalValue_W_one q qInv V D E hE hD

/-- The full-range high contour can meet Re w=0 exactly at this bin value.
No bin-avoidance conclusion follows from a lower and upper range alone. -/
theorem high_w_line_zero_iff (a e : ℝ) :
    1 - a - 6 * e = 0 ↔ a = 1 - 6 * e := by
  constructor <;> intro h <;> linarith

theorem high_w_zero_bin_in_full_range (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 49 / 600) :
    ∃ a : ℝ, 51 / 100 ≤ a ∧ a ≤ 1 ∧ 1 - a - 6 * e = 0 := by
  refine ⟨1 - 6 * e, ?_, ?_, ?_⟩ <;> linarith

/-- A cancellation identity with no smallness assumption on W. In particular
it remains useful at a=1, where w=-6e and an unramified W has norm > 1.
The hypothesis W≠1 is essential for the currently defined local factor. -/
theorem rowEulerRational_sub_one (q qInv V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    (((1 - V)⁻¹ + W / (1 - W) +
        E / (1 - E) * ((1 - qInv) / (1 - V) + W) -
        D / (1 - E) * (1 + (q - 1) * W * V / (1 - V))) *
      (1 - V) * (1 - W) / (1 - D)) - 1 =
      (-W * V + E * (1 - qInv + qInv * W - W ^ 2 + W ^ 2 * V) +
        D * (V + W - q * W * V + (q - 1) * W ^ 2 * V - E)) /
        ((1 - E) * (1 - D)) := by
  field_simp [hV, hW, hE, hD] <;> ring


end HeckeSkeleton.HighEulerAlgebra
