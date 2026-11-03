import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A single Mellin profile for a complete reflected block

The line and the normalized phase depend on the frozen block scale `Y` only.
They do not depend on the row, mark or either dual column.  The kernel's
small-argument gain is extracted as the scalar `min (Y^(1/4)) 1` before a
finite sum is enlarged or estimated.  The resulting density has exactly the
same absolute value as the amplitude on the selected Mellin line.

The actual multiplier adapter is in `ActualCommonMellin.lean`.  No energy
estimate is used in these identities or in the weighted L1 theorem.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.CommonMellin
open MeasureTheory
open scoped BigOperators Topology

/-- One line is chosen for the whole block. -/
def line (Y : ℝ) : ℝ := if Y ≤ 1 then -(1 / 4 : ℝ) else 0

def vertical (Y t : ℝ) : ℂ := (line Y : ℂ) + (t : ℂ) * Complex.I

def smallScalar (Y : ℝ) : ℝ := min (Y ^ (1 / 4 : ℝ)) 1

/-- The scale dependence remaining after extracting the small scalar is a phase. -/
def phase (Y t : ℝ) : ℂ := (Y : ℂ) ^ (-vertical Y t) / (smallScalar Y : ℂ)

def density (a : ℝ → ℂ) (Y t : ℝ) : ℂ := a t * phase Y t

def rowFactor (Y d t : ℝ) : ℂ := (d : ℂ) ^ (2 * vertical Y t)

def markFactor (Y P t : ℝ) : ℂ := (P : ℂ) ^ (2 * vertical Y t)

def columnFactor (Y n b t : ℝ) : ℂ :=
  (n : ℂ) ^ (-vertical Y t) * (b : ℂ) ^ (-(3 * vertical Y t))

def argument (Y d P n b : ℝ) : ℝ := Y * n * b ^ 3 / (d ^ 2 * P ^ 2)

theorem line_bounds (Y : ℝ) : -(1 / 4 : ℝ) ≤ line Y ∧ line Y ≤ 0 := by
  unfold line
  split_ifs <;> norm_num

theorem smallScalar_pos {Y : ℝ} (hY : 0 < Y) : 0 < smallScalar Y := by
  exact lt_min (Real.rpow_pos_of_pos hY _) zero_lt_one

theorem smallScalar_eq {Y : ℝ} (hY : 0 < Y) :
    smallScalar Y = Y ^ (-line Y) := by
  unfold smallScalar line
  split_ifs with h
  · rw [min_eq_left (Real.rpow_le_one hY.le h (by norm_num))]
    congr 1
    ring
  · have h1 : 1 ≤ Y := (lt_of_not_ge h).le
    rw [min_eq_right (Real.one_le_rpow h1 (by norm_num))]
    simp

@[simp] theorem vertical_re (Y t : ℝ) : (vertical Y t).re = line Y := by
  simp [vertical]

@[simp] theorem norm_phase {Y : ℝ} (hY : 0 < Y) (t : ℝ) : ‖phase Y t‖ = 1 := by
  rw [phase, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.neg_re, vertical_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (smallScalar_pos hY)]
  rw [← smallScalar_eq hY, div_self (smallScalar_pos hY).ne']

@[simp] theorem norm_density (a : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    ‖density a Y t‖ = ‖a t‖ := by
  simp only [density, norm_mul, norm_phase hY, mul_one]

theorem ofReal_mul_cpow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (w : ℂ) :
    ((a * b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w * (b : ℂ) ^ w := by
  rw [Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg ha hb w

theorem ofReal_pow_cpow (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (w : ℂ) :
    ((x ^ j : ℝ) : ℂ) ^ w = (x : ℂ) ^ ((j : ℂ) * w) := by
  rw [Complex.ofReal_pow]
  symm
  apply Complex.cpow_nat_mul'
  · simp [Complex.arg_ofReal_of_nonneg hx, Real.pi_pos]
  · simp [Complex.arg_ofReal_of_nonneg hx, Real.pi_pos.le]

theorem argument_pos {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    0 < argument Y d P n b := by
  unfold argument
  positivity

/-- Exact separation, retaining all four positive normalized coordinates. -/
theorem argument_cpow {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b)
    (w : ℂ) :
    ((argument Y d P n b : ℝ) : ℂ) ^ (-w) =
      (Y : ℂ) ^ (-w) * (d : ℂ) ^ (2 * w) * (P : ℂ) ^ (2 * w) *
        ((n : ℂ) ^ (-w) * (b : ℂ) ^ (-(3 * w))) := by
  unfold argument
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity),
    ofReal_mul_cpow (Y * n) (b ^ 3) (by positivity) (by positivity),
    ofReal_mul_cpow Y n hY.le hn.le,
    ofReal_mul_cpow (d ^ 2) (P ^ 2) (by positivity) (by positivity),
    ofReal_pow_cpow b hb.le 3, ofReal_pow_cpow d hd.le 2,
    ofReal_pow_cpow P hP.le 2]
  norm_num only [Nat.cast_ofNat]
  have h2 : (2 : ℂ) * -w = -(2 * w) := by ring
  have h3 : (3 : ℂ) * -w = -(3 * w) := by ring
  simp only [h2, h3, Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The scalar and density are common to all rows, marks and columns. -/
theorem amplitude_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b)
    (t : ℝ) :
    a t * ((argument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t) =
      (smallScalar Y : ℂ) *
        (density a Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t) := by
  rw [argument_cpow hY hd hP hn hb]
  unfold density phase rowFactor markFactor columnFactor
  have hS : (smallScalar Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (smallScalar_pos hY).ne'
  field_simp [hS]
  <;> ring

/-- Separation commutes with the actual Mellin integral. -/
theorem integral_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    (∫ t : ℝ, a t * ((argument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t)) =
      (smallScalar Y : ℂ) * ∫ t : ℝ,
        density a Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (amplitude_separation a hY hd hP hn hb)

theorem norm_rowFactor_le_one {Y d : ℝ} (hd : 1 ≤ d) (t : ℝ) :
    ‖rowFactor Y d t‖ ≤ 1 := by
  rw [rowFactor, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hd)]
  have he : (2 * vertical Y t).re = 2 * line Y := by simp
  rw [he]
  exact Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith [(line_bounds Y).2])

theorem norm_markFactor_le_one {Y P : ℝ} (hP : 1 ≤ P) (t : ℝ) :
    ‖markFactor Y P t‖ ≤ 1 := norm_rowFactor_le_one hP t

/-- Both column factors cost only one absolute factor `2` on dyads `[1,2]`. -/
theorem norm_columnFactor_le_two {Y n b : ℝ}
    (hn0 : 1 ≤ n) (hn1 : n ≤ 2) (hb0 : 1 ≤ b) (hb1 : b ≤ 2) (t : ℝ) :
    ‖columnFactor Y n b t‖ ≤ 2 := by
  have hn : 0 < n := zero_lt_one.trans_le hn0
  have hb : 0 < b := zero_lt_one.trans_le hb0
  rw [columnFactor, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.norm_cpow_eq_rpow_re_of_pos hb]
  have hre : (-(3 * vertical Y t)).re = -(3 * line Y) := by simp
  simp only [Complex.neg_re, vertical_re, hre]
  have hline := line_bounds Y
  have h1 : n ^ (-line Y) ≤ (2 : ℝ) ^ (-line Y) :=
    Real.rpow_le_rpow hn.le hn1 (by linarith)
  have h2 : b ^ (-(3 * line Y)) ≤ (2 : ℝ) ^ (-(3 * line Y)) :=
    Real.rpow_le_rpow hb.le hb1 (by linarith)
  calc
    _ ≤ (2 : ℝ) ^ (-line Y) * (2 : ℝ) ^ (-(3 * line Y)) :=
      mul_le_mul h1 h2 (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (-(4 * line Y)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 := Real.rpow_one _

/-- In the physical marked row the completed scale contains the active mark
norm itself. One power of that norm cancels against the squared conductor. -/
def physicalArgument (Y d P n b : ℝ) : ℝ := Y * n * b ^ 3 / (d ^ 2 * P)

def physicalMarkFactor (Y P t : ℝ) : ℂ := (P : ℂ) ^ vertical Y t

theorem physicalArgument_pos {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    0 < physicalArgument Y d P n b := by
  unfold physicalArgument
  positivity

/-- This is the literal cancellation caused by `X = Xinactive * NP`. -/
theorem physical_argument_cancel_mark {X A F d P n b : ℝ}
    (hF : 0 < F) (hd : 0 < d) (hP : 0 < P) :
    (X * P) * A * n * b ^ 3 / (d * F * P) ^ 2 =
      physicalArgument (X * A / F ^ 2) d P n b := by
  unfold physicalArgument
  field_simp [hF.ne', hd.ne', hP.ne']
  <;> ring

/-- All dyadic lower endpoints are incorporated in one scale.  That scale
is independent of the normalized row, active mark and dual columns. -/
theorem physicalArgument_normalized {Y D L N B d P n b : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hd : 0 < d) (hP : 0 < P) :
    physicalArgument Y (D * d) (L * P) (N * n) (B * b) =
      physicalArgument (Y * N * B ^ 3 / (D ^ 2 * L)) d P n b := by
  unfold physicalArgument
  field_simp [hD.ne', hL.ne', hd.ne', hP.ne']
  <;> ring

/-- Exact physical-scale separation: the active mark occurs to `w`, not `2w`. -/
theorem physicalArgument_cpow {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b)
    (w : ℂ) :
    ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-w) =
      (Y : ℂ) ^ (-w) * (d : ℂ) ^ (2 * w) * (P : ℂ) ^ w *
        ((n : ℂ) ^ (-w) * (b : ℂ) ^ (-(3 * w))) := by
  unfold physicalArgument
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity),
    ofReal_mul_cpow (Y * n) (b ^ 3) (by positivity) (by positivity),
    ofReal_mul_cpow Y n hY.le hn.le,
    ofReal_mul_cpow (d ^ 2) P (by positivity) hP.le,
    ofReal_pow_cpow b hb.le 3, ofReal_pow_cpow d hd.le 2]
  norm_num only [Nat.cast_ofNat]
  have h2 : (2 : ℂ) * -w = -(2 * w) := by ring
  have h3 : (3 : ℂ) * -w = -(3 * w) := by ring
  simp only [h2, h3, Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem amplitude_physical_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b)
    (t : ℝ) :
    a t * ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t) =
      (smallScalar Y : ℂ) *
        (density a Y t * rowFactor Y d t * physicalMarkFactor Y P t * columnFactor Y n b t) := by
  rw [physicalArgument_cpow hY hd hP hn hb]
  unfold density phase rowFactor physicalMarkFactor columnFactor
  have hS : (smallScalar Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (smallScalar_pos hY).ne'
  field_simp [hS]
  <;> ring

theorem integral_physical_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    (∫ t : ℝ, a t * ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t)) =
      (smallScalar Y : ℂ) * ∫ t : ℝ,
        density a Y t * rowFactor Y d t * physicalMarkFactor Y P t * columnFactor Y n b t := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (amplitude_physical_separation a hY hd hP hn hb)

theorem norm_physicalMarkFactor_le_one {Y P : ℝ} (hP : 1 ≤ P) (t : ℝ) :
    ‖physicalMarkFactor Y P t‖ ≤ 1 := by
  rw [physicalMarkFactor, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hP),
    vertical_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos hP (line_bounds Y).2

/-- The common scalar is exactly the kernel saving used by the exponent ledger. -/
theorem smallScalar_rpow (Z e : ℝ) (hZ : 1 ≤ Z) :
    smallScalar (Z ^ e) = Z ^ (-max (-e) 0 / 4) := by
  unfold smallScalar
  rw [← Real.rpow_mul (zero_le_one.trans hZ)]
  by_cases he : 0 ≤ e
  · rw [min_eq_right (Real.one_le_rpow hZ (by linarith : 0 ≤ e * (1 / 4 : ℝ))),
      max_eq_right (by linarith : -e ≤ 0)]
    simp
  · have he' : e ≤ 0 := (lt_of_not_ge he).le
    rw [min_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ
      (by linarith : e * (1 / 4 : ℝ) ≤ 0)), max_eq_left (by linarith : 0 ≤ -e)]
    congr 1
    ring

/-- Squaring the scalar gives the exact `-max(T-v-3b,0)/2` energy exponent. -/
theorem smallScalar_sq_exponent (Z T v b : ℝ) (hZ : 1 ≤ Z) :
    smallScalar (Z ^ (v + 3 * b - T)) ^ 2 =
      Z ^ (-max (T - v - 3 * b) 0 / 2) := by
  rw [smallScalar_rpow Z _ hZ, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
  have he : -(v + 3 * b - T) = T - v - 3 * b := by ring
  rw [he]
  congr 1
  ring

/-- A fixed polynomial moment of the common density is controlled by its
proved vertical-line decay.  The majorant integral is independent of `Y`. -/
theorem weighted_density_integrable_and_bound
    (a : ℝ → ℂ) (ha : Continuous a) {Y C : ℝ} (hY : 0 < Y) (hC : 0 ≤ C)
    (p : ℕ)
    (hbound : ∀ t : ℝ, ‖a t‖ ≤ C * (1 + |t|) ^ (-((p : ℝ) + 2))) :
    Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖density a Y t‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ p * ‖density a Y t‖) ≤
        C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (2 : ℝ)) (by norm_num))
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (1 + |t|) ^ p * ‖density a Y t‖) volume := by
    simp_rw [norm_density a hY]
    exact (((continuous_const.add continuous_abs).pow p).mul ha.norm).aestronglyMeasurable
  have hp (t : ℝ) : (1 + |t|) ^ p * ‖density a Y t‖ ≤
      C * (1 + |t|) ^ (-(2 : ℝ)) := by
    rw [norm_density a hY]
    have h := mul_le_mul_of_nonneg_left (hbound t)
      (show 0 ≤ (1 + |t|) ^ p by positivity)
    refine h.trans_eq ?_
    rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hint : Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖density a Y t‖) := by
    refine (hbase.const_mul C).mono' hmeas (ae_of_all _ (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hp t
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, C * (1 + |t|) ^ (-(2 : ℝ)) :=
      integral_mono_ae hint (hbase.const_mul C) (ae_of_all _ hp)
    _ = _ := integral_const_mul C _

#print axioms amplitude_separation
#print axioms physical_argument_cancel_mark
#print axioms physicalArgument_normalized
#print axioms amplitude_physical_separation
#print axioms integral_physical_separation
#print axioms integral_separation
#print axioms norm_columnFactor_le_two
#print axioms weighted_density_integrable_and_bound
#print axioms smallScalar_sq_exponent

end HeckeSkeleton.LowEnergy.CommonMellin
