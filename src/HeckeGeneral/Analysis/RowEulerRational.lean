import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rational Euler correction with the geometric denominators cancelled. -/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

/-- The rational continuation after cancelling the geometric denominators.
The independent qInv variable keeps the algebra valid even for q=0; for an
actual prime one substitutes qInv=q⁻¹. The local row correction uses this expression also when W=1. -/
def rowEulerRationalValue (q qInv V W D E : ℂ) : ℂ :=
  ((1 - E) * (1 - W * V) +
      E * (1 - W) * ((1 - qInv) + W * (1 - V)) -
      D * (1 - W) * ((1 - V) + (q - 1) * W * V)) /
    ((1 - E) * (1 - D))

theorem rowEulerLiteral_eq_rational (q qInv V W D E : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    (((1 - V)⁻¹ + W / (1 - W) +
        E / (1 - E) * ((1 - qInv) / (1 - V) + W) -
        D / (1 - E) * (1 + (q - 1) * W * V / (1 - V))) *
      (1 - V) * (1 - W) / (1 - D)) =
      rowEulerRationalValue q qInv V W D E := by
  unfold rowEulerRationalValue
  field_simp [hV, hW, hE, hD] <;> ring

/-- At W=1 the continued value retains the factor 1-V. -/
theorem rowEulerRationalValue_W_one (q qInv V D E : ℂ)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    rowEulerRationalValue q qInv V 1 D E = (1 - V) / (1 - D) := by
  unfold rowEulerRationalValue
  field_simp [hE, hD] <;> ring


/-- The error numerator is valid across V=1 and W=1; only genuine
rational denominators must be nonzero. -/
theorem rowEulerRationalValue_sub_one (q qInv V W D E : ℂ)
    (hE : 1 - E ≠ 0) (hD : 1 - D ≠ 0) :
    rowEulerRationalValue q qInv V W D E - 1 =
      (-W * V + E * (1 - qInv + qInv * W - W ^ 2 + W ^ 2 * V) +
        D * (V + W - q * W * V + (q - 1) * W ^ 2 * V - E)) /
        ((1 - E) * (1 - D)) := by
  unfold rowEulerRationalValue
  field_simp [hE, hD] <;> ring

end HeckeGeneral.ThetaSkeleton.Physical
