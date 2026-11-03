import HeckePort.Moments.Descent.SieveComposition
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite dyadic cube blocks

Every cube is assigned to its actual norm dyadic block. The partition
is exact, and its cardinality costs an arbitrarily small power of the
norm ceiling. A long-cube lower bound applies to every nonempty block,
with the one factor of two from the dyadic annulus kept explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks

open scoped Classical BigOperators

def index (q : ℝ) : ℕ := ⌊Real.logb 2 q⌋₊
def scale (j : ℕ) : ℝ := (2 : ℝ) ^ j
def count (R : ℝ) : ℕ := ⌊Real.logb 2 R⌋₊ + 1

theorem scale_pos (j : ℕ) : 0 < scale j := pow_pos (by norm_num) _
theorem scale_one_le (j : ℕ) : 1 ≤ scale j := one_le_pow₀ (by norm_num)

theorem norm_window (q : ℝ) (hq : 1 ≤ q) :
    scale (index q) ≤ q ∧ q < 2 * scale (index q) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hl : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hq
  have hlo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.floor_le hl)
  have hhi := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (Nat.lt_floor_add_one (Real.logb 2 q))
  rw [Real.rpow_logb (by norm_num) (by norm_num) hq0] at hlo hhi
  constructor
  · simpa only [scale, index, Real.rpow_natCast] using hlo
  · simpa only [scale, index, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, Real.rpow_one, mul_comm] using hhi

theorem index_lt_count (q R : ℝ) (hq : 1 ≤ q) (hR : q ≤ R) : index q < count R := by
  have hm := Nat.floor_mono
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (zero_lt_one.trans_le hq) hR)
  exact Nat.lt_succ_of_le hm

variable {β A κ : Type*} [AddCommMonoid A]

def block (B : Finset β) (q : β → ℝ) (j : ℕ) : Finset β :=
  B.filter (fun b => index (q b) = j)

theorem mem_block (B : Finset β) (q : β → ℝ) (j : ℕ) (b : β) :
    b ∈ block B q j ↔ b ∈ B ∧ index (q b) = j := Finset.mem_filter

theorem block_window (B : Finset β) (q : β → ℝ) (j : ℕ)
    (hq : ∀ b ∈ B, 1 ≤ q b) (b : β) (hb : b ∈ block B q j) :
    scale j ≤ q b ∧ q b ≤ 2 * scale j := by
  obtain ⟨hbB, hbindex⟩ := (mem_block B q j b).mp hb
  have h := norm_window (q b) (hq b hbB)
  rw [hbindex] at h
  exact ⟨h.1, h.2.le⟩

/-- An exact finite identity for arbitrary coefficients, before any
row energy or norm estimate. -/
theorem sum_eq_blocks (B : Finset β) (q : β → ℝ) (R : ℝ)
    (hq : ∀ b ∈ B, 1 ≤ q b) (hR : ∀ b ∈ B, q b ≤ R) (a : β → A) :
    (∑ b ∈ B, a b) = ∑ j ∈ Finset.range (count R), ∑ b ∈ block B q j, a b := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun b hb => Finset.mem_range.mpr (index_lt_count (q b) R (hq b hb) (hR b hb))) a

/-- The exact one-Cauchy cost of combining the actual cube blocks. -/
theorem sum_sq_le_blocks (B : Finset β) (q : β → ℝ) (R : ℝ)
    (hq : ∀ b ∈ B, 1 ≤ q b) (hR : ∀ b ∈ B, q b ≤ R) (a : β → ℂ) :
    ‖∑ b ∈ B, a b‖ ^ 2 ≤ (count R : ℝ) *
      ∑ j ∈ Finset.range (count R), ‖∑ b ∈ block B q j, a b‖ ^ 2 := by
  rw [sum_eq_blocks B q R hq hR]
  have h := HeckePort.Moments.bounded_finset_coefficient_sum_sq
    (Finset.range (count R)) (fun _ => (1 : ℂ))
    (fun j => ∑ b ∈ block B q j, a b) (by simp)
  simpa only [one_mul, Finset.card_range] using h

theorem weighted_energy_le_blocks (rows : Finset κ) (w : κ → ℝ)
    (hw : ∀ k ∈ rows, 0 ≤ w k)
    (B : Finset β) (q : β → ℝ) (R : ℝ)
    (hq : ∀ b ∈ B, 1 ≤ q b) (hR : ∀ b ∈ B, q b ≤ R)
    (a : κ → β → ℂ) :
    (∑ k ∈ rows, w k * ‖∑ b ∈ B, a k b‖ ^ 2) ≤
      (count R : ℝ) * ∑ j ∈ Finset.range (count R),
        ∑ k ∈ rows, w k * ‖∑ b ∈ block B q j, a k b‖ ^ 2 := by
  calc
    _ ≤ ∑ k ∈ rows, w k * ((count R : ℝ) *
        ∑ j ∈ Finset.range (count R), ‖∑ b ∈ block B q j, a k b‖ ^ 2) :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
        (sum_sq_le_blocks B q R hq hR (a k)) (hw k hk))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem count_le_log (R : ℝ) (hR : 1 ≤ R) :
    (count R : ℝ) ≤ Real.logb 2 R + 1 := by
  have hl : 0 ≤ Real.logb 2 R := Real.logb_nonneg (by norm_num) hR
  simp only [count, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le hl]

/-- The dyadic family and its later Cauchy factor can be budgeted by
small powers chosen before the source. -/
theorem exists_count_small_power (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → (count R : ℝ) ≤ C * R ^ eps := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + (eps * Real.log 2)⁻¹, le_add_of_nonneg_right (inv_nonneg.mpr (mul_pos heps hl2).le), ?_⟩
  intro R hR
  have hp : 1 ≤ R ^ eps := Real.one_le_rpow hR heps.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hR) heps
  calc
    _ ≤ Real.log R / Real.log 2 + 1 := count_le_log R hR
    _ ≤ (R ^ eps / eps) / Real.log 2 + R ^ eps :=
      add_le_add (div_le_div_of_nonneg_right hlog hl2.le) hp
    _ = _ := by field_simp [heps.ne', hl2.ne']; ring

/-- A nonempty block in the long pool has a genuinely long annular
lower scale, with the dyadic factor two accounted for. -/
theorem long_block_lower (B : Finset β) (q : β → ℝ) (T : ℝ) (j : ℕ)
    (hq : ∀ b ∈ B, 1 ≤ q b) (hlong : ∀ b ∈ B, T ≤ q b)
    (hne : (block B q j).Nonempty) : T / 2 < scale j := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨hbB, hbindex⟩ := (mem_block B q j b).mp hb
  have hw := (norm_window (q b) (hq b hbB)).2
  rw [hbindex] at hw
  linarith [hlong b hbB]

/-- The true split threshold is `Z^d`. Paying the actual dyadic factor
two with `2 ≤ Z^(d/3)` leaves a cube center at least `2d/3`. Calling the
provider with step `2d/3` then gives its full row drop `d`, while the
short completion still has length at most the original terminal `d`. -/
theorem long_block_log_lower (B : Finset β) (q : β → ℝ) (Z d : ℝ) (j : ℕ)
    (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ (d / 3))
    (hq : ∀ b ∈ B, 1 ≤ q b) (hlong : ∀ b ∈ B, Z ^ d ≤ q b)
    (hne : (block B q j).Nonempty) : 2 * d / 3 ≤ Real.logb Z (scale j) := by
  have hlow := long_block_lower B q (Z ^ d) j hq hlong hne
  have hp : Z ^ d = Z ^ (2 * d / 3) * Z ^ (d / 3) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  rw [hp] at hlow
  have hpositive : 0 < Z ^ (2 * d / 3) := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hscale : Z ^ (2 * d / 3) ≤ scale j := by nlinarith
  have hh := Real.logb_le_logb_of_le hZ
    hpositive hscale
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks
