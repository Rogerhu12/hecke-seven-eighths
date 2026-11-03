import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionMellin
import HeckePort.Moments.Descent.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Actual logarithmic scales of reopened cube parents

The common smooth partition changes the total column length by its
literal logarithmic dilation. Both canonical margins keep this change.
The squarefree scale is allowed to fall below one; only the nonnegative
branch of `annularLength` will enter the recursive provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionGeometry

open HeckeSkeleton.Moments.MOM_INV_STEP
open CubeCompletionMellin

def cubeLength (Z H : ℝ) : ℝ := Real.logb Z H

def annularScale (i : SchwartzTestPartition.Index) : ℝ :=
  SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)

def annularLength (Z N H : ℝ) (i : SchwartzTestPartition.Index) : ℝ :=
  Real.logb Z (annularScale i * (Z ^ N / H ^ 3))

theorem annularScale_pos (i : SchwartzTestPartition.Index) : 0 < annularScale i :=
  SchwartzTestPartition.scale_pos _

theorem cubeLength_scale {Z H : ℝ} (hZ : 1 < Z) (hH : 0 < H) :
    Z ^ cubeLength Z H = H :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hH

theorem annularLength_scale {Z N H : ℝ} (hZ : 1 < Z) (hH : 0 < H)
    (i : SchwartzTestPartition.Index) :
    Z ^ annularLength Z N H i = annularScale i * (Z ^ N / H ^ 3) :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (mul_pos (annularScale_pos i)
      (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (pow_pos hH _)))

theorem annular_total_length {Z N H V : ℝ} (hZ : 1 < Z) (hH : 0 < H)
    (i : SchwartzTestPartition.Index) :
    annularLength Z N H i + 3 * cubeLength Z H + V =
      N + V + Real.logb Z (annularScale i) := by
  have hz0 := zero_lt_one.trans hZ
  simp only [annularLength, cubeLength,
    Real.logb_mul (annularScale_pos i).ne'
      (div_pos (Real.rpow_pos_of_pos hz0 _) (pow_pos hH _)).ne',
    Real.logb_div (Real.rpow_pos_of_pos hz0 _).ne' (pow_pos hH _).ne',
    Real.logb_pow, Real.logb_rpow hz0 (ne_of_gt hZ)]
  ring

theorem annularLength_nonneg {Z N H : ℝ} (hZ : 1 < Z)
    (i : SchwartzTestPartition.Index)
    (hscale : 1 ≤ annularScale i * (Z ^ N / H ^ 3)) :
    0 ≤ annularLength Z N H i := Real.logb_nonneg hZ hscale

theorem cubeLength_nonneg {Z H : ℝ} (hZ : 1 < Z) (hH : 1 ≤ H) :
    0 ≤ cubeLength Z H := Real.logb_nonneg hZ hH

/-- The fixed partition scale is at most eight. This bound gives a
uniform provider capacity even before the much finer eta threshold is
used for its descent margins. -/
theorem annularLength_upper {Z N H : ℝ} (hZ : 2 ≤ Z) (hH : 1 ≤ H)
    (i : SchwartzTestPartition.Index) : annularLength Z N H i ≤ N + 3 := by
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have hH0 := zero_lt_one.trans_le hH
  have hX := Real.rpow_pos_of_pos hz0 N
  have h8 : (8 : ℝ) ≤ Z ^ (3 : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hZ 3
    norm_num at hp
    simpa only [Real.rpow_ofNat] using hp
  have hbound : annularScale i * (Z ^ N / H ^ 3) ≤ Z ^ (N + 3) := by
    calc
      _ ≤ 8 * Z ^ N :=
        (mul_le_mul_of_nonneg_right (annular_scale_le_eight i)
          (div_nonneg hX.le (pow_nonneg hH0.le _))).trans
          (mul_le_mul_of_nonneg_left (div_le_self hX.le (one_le_pow₀ hH)) (by norm_num))
      _ ≤ Z ^ (3 : ℝ) * Z ^ N := mul_le_mul_of_nonneg_right h8 hX.le
      _ = _ := by rw [← Real.rpow_add hz0]; congr 1; ring
  have hb := Real.logb_le_logb_of_le hz1
    (mul_pos (annularScale_pos i) (div_pos hX (pow_pos hH0 _))) hbound
  simpa only [annularLength, Real.logb_rpow hz0 (ne_of_gt hz1)] using hb

theorem cubeLength_upper {Z N H : ℝ} (hZ : 2 ≤ Z) (hH : 0 < H)
    (hsupport : H ^ 3 ≤ 2 * Z ^ N) : cubeLength Z H ≤ (N + 1) / 3 := by
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have hlog := Real.logb_le_logb_of_le hz1 (pow_pos hH 3)
    (hsupport.trans (mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz0.le N)))
  rw [Real.logb_pow, Real.logb_mul hz0.ne' (Real.rpow_pos_of_pos hz0 N).ne',
    Real.logb_self_eq_one hz1,
    Real.logb_rpow hz0 (ne_of_gt hz1)] at hlog
  change Real.logb Z H ≤ (N + 1) / 3
  norm_num at hlog
  linarith

/-- The two margins pay the actual annular shift. The stronger second
margin requires four times that shift, hence eta/2 rather than eta/8. -/
theorem annular_margins {Z N H V M Q z c eta : ℝ}
    (hZ : 1 < Z) (hH : 0 < H) (i : SchwartzTestPartition.Index)
    (hshift : |Real.logb Z (annularScale i)| ≤ eta / 8)
    (hparent : HeckePort.Moments.CanonicalMargins (N + V) M Q z c) :
    HeckePort.Moments.CanonicalMargins
      (annularLength Z N H i + 3 * cubeLength Z H + V) M Q z (c - eta / 2) := by
  rw [annular_total_length hZ hH i]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hshift
  constructor <;> linarith [hparent.1, hparent.2]

theorem annular_capacity {Z N H V Fcap eta : ℝ}
    (hZ : 1 < Z) (hH : 0 < H) (i : SchwartzTestPartition.Index)
    (hshift : |Real.logb Z (annularScale i)| ≤ eta / 8) (hF : N + V ≤ Fcap) :
    annularLength Z N H i + 3 * cubeLength Z H + V ≤ Fcap + eta / 8 := by
  rw [annular_total_length hZ hH i]
  linarith [(abs_le.mp hshift).2]

theorem provider_parameters {d eta h : ℝ} (hh : 0 ≤ h)
    (hmesh : h ≤ eta / 128) (hstep : eta ≤ d / 16) :
    0 ≤ eta / 2 ∧ 0 ≤ 2 * d / 3 ∧ h ≤ (eta / 2) / 32 ∧
      eta / 2 ≤ (2 * d / 3) / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem provider_row_drop (R d : ℝ) : R - 3 * (2 * d / 3) / 2 = R - d := by ring

theorem provider_child_capacity {Fcap eta : ℝ} (heta : 0 ≤ eta) :
    (Fcap + eta / 8) + 11 * (eta / 2) ≤ Fcap + 11 * eta := by linarith

theorem provider_child_margin {c eta : ℝ} (heta : 0 ≤ eta) :
    c - 7 * eta ≤ (c - eta / 2) - 7 * (eta / 2) := by linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionGeometry
