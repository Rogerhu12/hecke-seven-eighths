import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Absorb the fixed detector-height degree into the chosen decay order.

The detector is shortened to H+3/2 and the external tail parameter is
chosen to be H itself. Increasing its order from N to N+k removes the
entire polynomial height cost. Only a lower bound H >= delta*T is then
needed to return to the original external height T.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinBoundary

/-- The exact detector-height factor produced by U=H+3/2 is absorbed
by requesting k additional powers of tail decay. -/
theorem height_tail_absorb (H : ℝ) (N k : ℕ) (hH : 1 ≤ H) :
    (2 + (H + 3 / 2)) ^ k * H ^ (-((N + k : ℕ) : ℝ)) ≤
      (5 : ℝ) ^ k * H ^ (-(N : ℝ)) := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hpoly : (2 + (H + 3 / 2)) ^ k ≤ (5 : ℝ) ^ k * H ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) k
  have hcancel : H ^ k * H ^ (-((N + k : ℕ) : ℝ)) = H ^ (-(N : ℝ)) := by
    rw [← Real.rpow_natCast H k, ← Real.rpow_add hH0]
    congr 1
    simp only [Nat.cast_add]
    ring
  calc
    _ ≤ ((5 : ℝ) ^ k * H ^ k) * H ^ (-((N + k : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hH0.le _)
    _ = (5 : ℝ) ^ k * (H ^ k * H ^ (-((N + k : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hcancel]

/-- Conversion to the original external parameter requires only the
positive lower bound H >= delta*T. There is no upper bound on H. -/
theorem height_tail_absorption_external
    (H delta T : ℝ) (N k : ℕ) (hH : 1 ≤ H)
    (hdelta : 0 < delta) (hT : 0 < T) (hdeltaT : delta * T ≤ H) :
    (H + 7 / 2) ^ k * H ^ (-((N + k : ℕ) : ℝ)) ≤
      ((5 : ℝ) ^ k * delta ^ (-(N : ℝ))) * T ^ (-(N : ℝ)) := by
  have hb := height_tail_absorb H N k hH
  rw [show (2 + (H + 3 / 2) : ℝ) = H + 7 / 2 by ring] at hb
  have htail : H ^ (-(N : ℝ)) ≤
      delta ^ (-(N : ℝ)) * T ^ (-(N : ℝ)) := by
    calc
      _ ≤ (delta * T) ^ (-(N : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hdelta hT) hdeltaT
          (neg_nonpos.mpr (Nat.cast_nonneg N))
      _ = _ := Real.mul_rpow hdelta.le hT.le
  exact hb.trans ((mul_le_mul_of_nonneg_left htail (pow_nonneg (by norm_num) k)).trans_eq
    (by ring))

end HighBinBoundary

#print axioms HighBinBoundary.height_tail_absorb
#print axioms HighBinBoundary.height_tail_absorption_external
