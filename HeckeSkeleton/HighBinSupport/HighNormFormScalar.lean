import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-!
Scalar norm-form accounting for HIGHBIN.

These theorems are independent of all admitted project declarations.  The
first equality reconstructs the exact exponent from the actual geometric
scales X=Z^(17/48), Y=Z^(23/48), z=17/50.  A separate theorem handles a
row in the complete dyadic shell, including when its resulting norm power
is negative.  No row-count estimate occurs in this module.
-/

noncomputable section
namespace HighBinVerified.NormForm

/-- The row-count-free exponent directly obtained from the three Mellin
scales, the reflected row L-function, and the normalized prime slots. -/
def rowExponent (d a q : ℝ) : ℝ :=
  (25 / 48) * a - 63 / 100 + d * (a - 21 / 25) + q / 6

/-- The formula called `moderateExponent` in the supplied project.  It is
repeated here to keep this module independent of admitted declarations. -/
def moderateExponent (d δ q R : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + q / 6 - (13 / 16) * (1 - R) +
    (d - 13 / 16) * (R + δ / 2 - 17 / 50)

/-- Exact agreement with (6.24), before insertion of any row count. -/
theorem rowExponent_eq_moderate (d a q : ℝ) :
    rowExponent d a q = 3 / 16 + moderateExponent d (2 * a - 1) q 0 := by
  unfold rowExponent moderateExponent
  ring

/-- Inserting a count of order U^R contributes exactly dR, not R. -/
theorem countedExponent_eq (d a q R : ℝ) :
    rowExponent d a q + d * R =
      3 / 16 + moderateExponent d (2 * a - 1) q R := by
  unfold rowExponent moderateExponent
  ring

/-- The exact real exponent of X^(1/2-z) Z^(s+z-1) Y^(w-1). -/
theorem geometric_exponent_identity (a e : ℝ) :
    (17 / 48) * (1 / 2 - 17 / 50) +
      (a + 16 * e + 17 / 50 - 1) +
      (23 / 48) * (-a - 6 * e) =
        (25 / 48) * a - 181 / 300 + (105 / 8) * e := by
  ring

/-- The row-conductor and prime-amplitude factors produce exactly the
claimed norm form.  `eta` is a row-norm loss and `rho` a base-Z loss. -/
theorem full_exponent_identity (d a q e eta rho : ℝ) :
    (17 / 48) * (1 / 2 - 17 / 50) +
      (a + 16 * e + 17 / 50 - 1) +
      (23 / 48) * (-a - 6 * e) +
      d * (a - 1 / 2 + 6 * e + eta - 17 / 50) +
      (-2 / 75 + q / 6 + rho) =
        rowExponent d a q + (105 / 8 + 6 * d) * e + d * eta + rho := by
  unfold rowExponent
  ring

/-- Multiplicative version of the exact exponent identity. -/
theorem full_scale_identity (Z d a q e eta rho : ℝ) (hZ : 0 < Z) :
    (Z ^ (17 / 48 : ℝ)) ^ (1 / 2 - 17 / 50 : ℝ) *
      Z ^ (a + 16 * e + 17 / 50 - 1) *
      (Z ^ (23 / 48 : ℝ)) ^ (-a - 6 * e) *
      (Z ^ d) ^ (a - 1 / 2 + 6 * e + eta - 17 / 50) *
      Z ^ (-2 / 75 + q / 6 + rho) =
        Z ^ (rowExponent d a q + (105 / 8 + 6 * d) * e + d * eta + rho) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ]
  congr 1
  exact full_exponent_identity d a q e eta rho

/-- A dyadic shell estimate valid for both signs of the exponent.  Using
only the upper endpoint is incorrect when p is negative. -/
theorem dyadic_shell_rpow (U N p M : ℝ) (hU : 0 < U)
    (hUN : U ≤ N) (hNU : N ≤ 2 * U) (hM : 0 ≤ M) (hpM : p ≤ M) :
    N ^ p ≤ (2 : ℝ) ^ M * U ^ p := by
  have hN : 0 ≤ N := hU.le.trans hUN
  by_cases hp : 0 ≤ p
  · calc
      N ^ p ≤ (2 * U) ^ p := Real.rpow_le_rpow hN hNU hp
      _ = (2 : ℝ) ^ p * U ^ p := Real.mul_rpow (by norm_num) hU.le
      _ ≤ (2 : ℝ) ^ M * U ^ p := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpM)
        (Real.rpow_nonneg hU.le _)
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    calc
      N ^ p ≤ U ^ p := Real.rpow_le_rpow_of_nonpos hU hUN hp'
      _ ≤ (2 : ℝ) ^ M * U ^ p := by
        have htwo : 1 ≤ (2 : ℝ) ^ M := Real.one_le_rpow (by norm_num) hM
        simpa using mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hU.le p)

/-- The whole scalar expression on an actual dyadic row shell. -/
theorem dyadic_full_scale_bound (Z N d a q e eta rho M : ℝ)
    (hZ : 0 < Z) (hNlo : Z ^ d ≤ N) (hNhi : N ≤ 2 * Z ^ d)
    (hM : 0 ≤ M) (hpM : a - 1 / 2 + 6 * e + eta - 17 / 50 ≤ M) :
    (Z ^ (17 / 48 : ℝ)) ^ (1 / 2 - 17 / 50 : ℝ) *
      Z ^ (a + 16 * e + 17 / 50 - 1) *
      (Z ^ (23 / 48 : ℝ)) ^ (-a - 6 * e) *
      N ^ (a - 1 / 2 + 6 * e + eta - 17 / 50) *
      Z ^ (-2 / 75 + q / 6 + rho) ≤
        (2 : ℝ) ^ M *
          Z ^ (rowExponent d a q + (105 / 8 + 6 * d) * e + d * eta + rho) := by
  have hU : 0 < Z ^ d := Real.rpow_pos_of_pos hZ _
  have hrow := dyadic_shell_rpow (Z ^ d) N
    (a - 1 / 2 + 6 * e + eta - 17 / 50) M hU hNlo hNhi hM hpM
  calc
    _ ≤ (Z ^ (17 / 48 : ℝ)) ^ (1 / 2 - 17 / 50 : ℝ) *
          Z ^ (a + 16 * e + 17 / 50 - 1) *
          (Z ^ (23 / 48 : ℝ)) ^ (-a - 6 * e) *
          ((2 : ℝ) ^ M * (Z ^ d) ^ (a - 1 / 2 + 6 * e + eta - 17 / 50)) *
          Z ^ (-2 / 75 + q / 6 + rho) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = (2 : ℝ) ^ M *
          ((Z ^ (17 / 48 : ℝ)) ^ (1 / 2 - 17 / 50 : ℝ) *
            Z ^ (a + 16 * e + 17 / 50 - 1) *
            (Z ^ (23 / 48 : ℝ)) ^ (-a - 6 * e) *
            (Z ^ d) ^ (a - 1 / 2 + 6 * e + eta - 17 / 50) *
            Z ^ (-2 / 75 + q / 6 + rho)) := by ring
    _ = _ := by rw [full_scale_identity Z d a q e eta rho hZ]

/-- Explicit sufficient loss budget for the complete moderate shell range.
The small positive losses eta and rho can be chosen after the slot system.
This is valid through a=1 and uses no restriction B≤11/12. -/
theorem loss_budget (d e eta rho lam : ℝ)
    (hd : d ≤ 5 / 6) (he : 0 ≤ e) (heta : 0 ≤ eta)
    (heSmall : e ≤ lam / 100) (hetaSmall : eta ≤ lam / 100)
    (hrhoSmall : rho ≤ lam / 20) :
    (105 / 8 + 6 * d) * e + d * eta + rho ≤ lam / 4 := by
  have hde : d * e ≤ (5 / 6) * e := mul_le_mul_of_nonneg_right hd he
  have hdeta : d * eta ≤ (5 / 6) * eta := mul_le_mul_of_nonneg_right hd heta
  linarith

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.rowExponent_eq_moderate
#print axioms HighBinVerified.NormForm.full_scale_identity
#print axioms HighBinVerified.NormForm.dyadic_shell_rpow
#print axioms HighBinVerified.NormForm.dyadic_full_scale_bound
#print axioms HighBinVerified.NormForm.loss_budget
