import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTests
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedScale
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleBudget

/-!
# A fixed finite annular partition after common-prime extraction

Both ends of each original prime window are used.  Consequently the
new column lies in a fixed multiplicative interval around
`Z^(r+z-2G)`.  The number of annuli depends only on the fixed slot cap,
not on the source scale, selected overlap, row or Fourier parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedAnnuli

open HeckeSkeleton.Moments.MOM_INV_STEP
open scoped Classical BigOperators

def width (slotCap : ℕ) : ℕ := 2 * slotCap + 1
def blocks (slotCap : ℕ) : Finset ℕ := Finset.range (2 * width slotCap + 1)
def scale (slotCap k : ℕ) : ℝ := (2 : ℝ) ^ k / (2 : ℝ) ^ width slotCap
def supportConstant (slotCap : ℕ) : ℝ := 8 * (2 : ℝ) ^ width slotCap
def columnScale (slotCap k : ℕ) (i : SchwartzTestPartition.Index) (Z r z G : ℝ) : ℝ :=
  SourceScaleBudget.annularScale i * scale slotCap k *
    Z ^ ProviderMarkedScale.columnLength r z G

theorem scale_pos (slotCap k : ℕ) : 0 < scale slotCap k := by unfold scale; positivity

theorem supportConstant_ge_one (slotCap : ℕ) : 1 ≤ supportConstant slotCap := by
  have h : 1 ≤ (2 : ℝ) ^ width slotCap := one_le_pow₀ (by norm_num)
  unfold supportConstant
  linarith

theorem scale_upper (slotCap k : ℕ) (hk : k ∈ blocks slotCap) :
    scale slotCap k ≤ (2 : ℝ) ^ width slotCap := by
  have hk' : k ≤ 2 * width slotCap := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ width slotCap)).mpr
  calc
    _ ≤ (2 : ℝ) ^ (2 * width slotCap) := pow_le_pow_right₀ (by norm_num) hk'
    _ = _ := by rw [two_mul, pow_add]

theorem columnScale_pos (slotCap k : ℕ) (i : SchwartzTestPartition.Index)
    (Z r z G : ℝ) (hZ : 0 < Z) : 0 < columnScale slotCap k i Z r z G := by
  unfold columnScale
  exact mul_pos (mul_pos (SourceScaleBudget.annularScale_pos i) (scale_pos slotCap k))
    (Real.rpow_pos_of_pos hZ _)

theorem columnScale_upper (slotCap k : ℕ) (hk : k ∈ blocks slotCap)
    (i : SchwartzTestPartition.Index) (Z r z G : ℝ) (hZ : 0 < Z) :
    columnScale slotCap k i Z r z G ≤
      supportConstant slotCap * Z ^ ProviderMarkedScale.columnLength r z G := by
  unfold columnScale supportConstant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (SourceScaleBudget.annularScale_le_eight i) (scale_upper slotCap k hk)
      (scale_pos slotCap k).le (by norm_num)) (Real.rpow_nonneg hZ.le _)

/-- Fixed annular partition on the entire literal new column window. -/
theorem partition (slotCap : ℕ) (x R : ℝ) (hR : 0 < R)
    (hl : R / (2 : ℝ) ^ width slotCap ≤ x)
    (hu : x ≤ (2 : ℝ) ^ width slotCap * R) :
    (∑ k ∈ blocks slotCap, Expansion.Dyadic.annularProfile (x / (scale slotCap k * R))) = 1 := by
  have hlo : 1 ≤ x / (R / (2 : ℝ) ^ width slotCap) :=
    (one_le_div (div_pos hR (by positivity))).mpr hl
  have hhi : x / (R / (2 : ℝ) ^ width slotCap) ≤ (2 : ℝ) ^ (2 * width slotCap) := by
    apply (div_le_iff₀ (div_pos hR (by positivity))).mpr
    calc
      x ≤ (2 : ℝ) ^ width slotCap * R := hu
      _ = _ := by rw [two_mul, pow_add]; field_simp
  have h := Expansion.Dyadic.sum_annularProfile_eq_one hlo (2 * width slotCap) hhi
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold scale
  field_simp
  <;> ring

theorem finite_partition {ι : Type*} (slotCap : ℕ) (T : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (R : ℝ) (hR : 0 < R)
    (hwindow : ∀ n ∈ T, a n ≠ 0 →
      R / (2 : ℝ) ^ width slotCap ≤ N n ∧ N n ≤ (2 : ℝ) ^ width slotCap * R) :
    (∑ n ∈ T, a n) =
      ∑ k ∈ blocks slotCap, ∑ n ∈ T,
        a n * Expansion.Dyadic.annularProfile (N n / (scale slotCap k * R)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.mul_sum]
  by_cases ha : a n = 0
  · rw [ha, zero_mul]
  · rw [partition slotCap (N n) R hR (hwindow n hn ha).1 (hwindow n hn ha).2, mul_one]

/-- The elementary quotient range used with the actual norm identity.
The lower and upper prime bounds are both retained. -/
theorem quotient_window (A a b x y : ℝ) (hA : 1 ≤ A) (hx : 0 ≤ x)
    (ha : A⁻¹ ≤ a ∧ a ≤ A) (hb : A⁻¹ ≤ b ∧ b ≤ A)
    (hy : 1 / 2 ≤ y ∧ y ≤ 2) (heq : a * x = y * b) :
    (2 * A ^ 2)⁻¹ ≤ x ∧ x ≤ 2 * A ^ 2 := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have haa : 1 ≤ A * a := by
    have h := mul_le_mul_of_nonneg_left ha.1 hAp.le
    simpa only [mul_inv_cancel₀ hAp.ne'] using h
  have hbb : 1 ≤ A * b := by
    have h := mul_le_mul_of_nonneg_left hb.1 hAp.le
    simpa only [mul_inv_cancel₀ hAp.ne'] using h
  have hb0 : 0 ≤ b := (inv_pos.mpr hAp).le.trans hb.1
  have hyb : y * b ≤ 2 * A := (mul_le_mul_of_nonneg_right hy.2 hb0).trans
    (mul_le_mul_of_nonneg_left hb.2 (by norm_num))
  have hlower : 1 ≤ 2 * A ^ 2 * x := by
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy.1 hb0) hAp.le
    have ha' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.2 hx) hAp.le
    have heqA := congrArg (fun v : ℝ => A * v) heq
    nlinarith
  constructor
  · rw [← one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * A ^ 2)).mpr
    nlinarith
  · have hax := mul_le_mul_of_nonneg_right haa hx
    have hu := mul_le_mul_of_nonneg_left hyb hAp.le
    have heqA := congrArg (fun v : ℝ => A * v) heq
    nlinarith

theorem dyadic_width (slotCap : ℕ) :
    2 * ((2 : ℝ) ^ slotCap) ^ 2 = (2 : ℝ) ^ width slotCap := by
  unfold width
  rw [pow_add, pow_one, ← pow_mul, Nat.mul_comm slotCap 2]
  ring

theorem productConstant_le_support (slotCap : ℕ) :
    (2 : ℝ) ^ slotCap ≤ supportConstant slotCap := by
  have hA : 1 ≤ (2 : ℝ) ^ slotCap := one_le_pow₀ (by norm_num)
  rw [supportConstant, ← dyadic_width]
  nlinarith

/-- Enlarging the complete column pool is done before Fourier
inversion.  Its radius depends only on the fixed slot cap and the
new central scale, while retaining the literal common ideal. -/
theorem product_cap (slotCap : ℕ) (Z r z G j P : ℝ) (hZ : 0 < Z)
    (hj : ((2 : ℝ) ^ slotCap)⁻¹ ≤ j / Z ^ G)
    (hP : P / Z ^ (z - G) ≤ (2 : ℝ) ^ slotCap) :
    P ≤ (supportConstant slotCap * Z ^ ProviderMarkedScale.columnLength r z G) * j /
      Z ^ r := by
  let A : ℝ := (2 : ℝ) ^ slotCap
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hjA : 1 ≤ A * (j / Z ^ G) := by
    have h : A * A⁻¹ ≤ A * (j / Z ^ G) := mul_le_mul_of_nonneg_left hj hAp.le
    simpa only [mul_inv_cancel₀ hAp.ne'] using h
  have hj0 : 0 ≤ j / Z ^ G := (inv_pos.mpr hAp).le.trans hj
  have hcoeff : A ≤ supportConstant slotCap * (j / Z ^ G) := by
    have h := mul_le_mul_of_nonneg_left hjA hAp.le
    have hs : A ^ 2 ≤ supportConstant slotCap := by
      rw [supportConstant, ← dyadic_width]
      dsimp only [A]
      nlinarith [sq_nonneg ((2 : ℝ) ^ slotCap)]
    nlinarith [mul_le_mul_of_nonneg_right hs hj0]
  have he : (j / Z ^ G) * Z ^ (z - G) =
      Z ^ ProviderMarkedScale.columnLength r z G * j / Z ^ r := by
    have hbalance : Z ^ r * Z ^ (z - G) =
        Z ^ G * Z ^ ProviderMarkedScale.columnLength r z G := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 1
      unfold ProviderMarkedScale.columnLength
      ring
    apply (eq_div_iff (Real.rpow_pos_of_pos hZ r).ne').mpr
    calc
      _ = (j / Z ^ G) * (Z ^ r * Z ^ (z - G)) := by ring
      _ = (j / Z ^ G) * (Z ^ G * Z ^ ProviderMarkedScale.columnLength r z G) := by
        rw [hbalance]
      _ = _ := by field_simp [(Real.rpow_pos_of_pos hZ G).ne']
                  <;> ring
  calc
    P ≤ A * Z ^ (z - G) := (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp hP
    _ ≤ (supportConstant slotCap * (j / Z ^ G)) * Z ^ (z - G) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc, he]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedAnnuli

end
