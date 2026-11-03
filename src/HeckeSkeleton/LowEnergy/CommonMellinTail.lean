import HeckeSkeleton.LowEnergy.CommonMellin

/-!
# One common Mellin profile including the positive-line dual tail

The whole block uses line -1/4 at small argument and line 2 at large argument.
After extracting `min(Y^(1/4),Y^-2)`, the scale dependence is still a phase.
On normalized dyads every separate coefficient has a fixed absolute bound.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.CommonMellinTail
open MeasureTheory HeckeSkeleton.LowEnergy.CommonMellin
open scoped Topology

def line (Y : ℝ) : ℝ := if Y ≤ 1 then -(1 / 4 : ℝ) else 2

def vertical (Y t : ℝ) : ℂ := (line Y : ℂ) + (t : ℂ) * Complex.I

def scalar (Y : ℝ) : ℝ := min (Y ^ (1 / 4 : ℝ)) (Y ^ (-(2 : ℝ)))

def phase (Y t : ℝ) : ℂ := (Y : ℂ) ^ (-vertical Y t) / (scalar Y : ℂ)

def density (a : ℝ → ℂ) (Y t : ℝ) : ℂ := a t * phase Y t

def rowFactor (Y d t : ℝ) : ℂ := (d : ℂ) ^ (2 * vertical Y t)

def markFactor (Y P t : ℝ) : ℂ := (P : ℂ) ^ vertical Y t

def columnFactor (Y n b t : ℝ) : ℂ :=
  (n : ℂ) ^ (-vertical Y t) * (b : ℂ) ^ (-(3 * vertical Y t))

theorem line_bounds (Y : ℝ) : -(1 / 4 : ℝ) ≤ line Y ∧ line Y ≤ 2 := by
  unfold line
  split_ifs <;> norm_num

@[simp] theorem vertical_re (Y t : ℝ) : (vertical Y t).re = line Y := by
  simp [vertical]

theorem scalar_pos {Y : ℝ} (hY : 0 < Y) : 0 < scalar Y :=
  lt_min (Real.rpow_pos_of_pos hY _) (Real.rpow_pos_of_pos hY _)

theorem scalar_eq {Y : ℝ} (hY : 0 < Y) : scalar Y = Y ^ (-line Y) := by
  unfold scalar line
  split_ifs with h
  · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge hY h
      (by norm_num : -(2 : ℝ) ≤ 1 / 4))]
    congr 1
    ring
  · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge h))
      (by norm_num : -(2 : ℝ) ≤ 1 / 4))]

@[simp] theorem norm_phase {Y : ℝ} (hY : 0 < Y) (t : ℝ) : ‖phase Y t‖ = 1 := by
  rw [phase, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.neg_re, vertical_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (scalar_pos hY)]
  rw [← scalar_eq hY, div_self (scalar_pos hY).ne']

@[simp] theorem norm_density (a : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    ‖density a Y t‖ = ‖a t‖ := by
  simp only [density, norm_mul, norm_phase hY, mul_one]

/-- Physical marks have exponent one after their completed scale cancels. -/
theorem amplitude_physical_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) (t : ℝ) :
    a t * ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t) =
      (scalar Y : ℂ) *
        (density a Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t) := by
  rw [physicalArgument_cpow hY hd hP hn hb]
  unfold density phase rowFactor markFactor columnFactor
  have hS : (scalar Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scalar_pos hY).ne'
  field_simp [hS]
  <;> ring

theorem integral_physical_separation (a : ℝ → ℂ) {Y d P n b : ℝ}
    (hY : 0 < Y) (hd : 0 < d) (hP : 0 < P) (hn : 0 < n) (hb : 0 < b) :
    (∫ t : ℝ, a t * ((physicalArgument Y d P n b : ℝ) : ℂ) ^ (-vertical Y t)) =
      (scalar Y : ℂ) * ∫ t : ℝ,
        density a Y t * rowFactor Y d t * markFactor Y P t * columnFactor Y n b t := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (amplitude_physical_separation a hY hd hP hn hb)

/-- A positive dyad controls any real exponent from above. -/
theorem rpow_on_dyad_le {x a A : ℝ} (hx0 : 1 ≤ x) (hx1 : x ≤ 2)
    (hA : 0 ≤ A) (ha : a ≤ A) : x ^ a ≤ (2 : ℝ) ^ A :=
  (Real.rpow_le_rpow_of_exponent_le hx0 ha).trans
    (Real.rpow_le_rpow (zero_le_one.trans hx0) hx1 hA)

theorem norm_rowFactor_le {Y d : ℝ} (hd0 : 1 ≤ d) (hd1 : d ≤ 2) (t : ℝ) :
    ‖rowFactor Y d t‖ ≤ 16 := by
  rw [rowFactor, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hd0)]
  have he : (2 * vertical Y t).re = 2 * line Y := by simp
  rw [he]
  have h := rpow_on_dyad_le hd0 hd1 (by norm_num : (0 : ℝ) ≤ 4)
    (show 2 * line Y ≤ 4 by linarith [(line_bounds Y).2])
  norm_num at h ⊢
  exact h

theorem norm_markFactor_le {Y P : ℝ} (hP0 : 1 ≤ P) (hP1 : P ≤ 2) (t : ℝ) :
    ‖markFactor Y P t‖ ≤ 4 := by
  rw [markFactor, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hP0), vertical_re]
  have h := rpow_on_dyad_le hP0 hP1 (by norm_num : (0 : ℝ) ≤ 2) (line_bounds Y).2
  norm_num at h ⊢
  exact h

theorem norm_columnFactor_le {Y n b : ℝ}
    (hn0 : 1 ≤ n) (hn1 : n ≤ 2) (hb0 : 1 ≤ b) (hb1 : b ≤ 2) (t : ℝ) :
    ‖columnFactor Y n b t‖ ≤ 4 := by
  rw [columnFactor, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hn0),
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hb0)]
  have he : (-(3 * vertical Y t)).re = -(3 * line Y) := by simp
  simp only [Complex.neg_re, vertical_re, he]
  have h1 := rpow_on_dyad_le hn0 hn1 (by norm_num : (0 : ℝ) ≤ 1)
    (show -line Y ≤ 1 by linarith [(line_bounds Y).1])
  have h2 := rpow_on_dyad_le hb0 hb1 (by norm_num : (0 : ℝ) ≤ 1)
    (show -(3 * line Y) ≤ 1 by linarith [(line_bounds Y).1])
  norm_num at h1 h2
  exact (mul_le_mul h1 h2 (by positivity) (by norm_num)).trans_eq (by norm_num)

/-- Both sides of the kernel minimum have their exact exponent, with no
constant depending on the dual dyad. -/
theorem scalar_rpow (Z e : ℝ) (hZ : 1 ≤ Z) :
    scalar (Z ^ e) = Z ^ (-max (-e) 0 / 4 - 2 * max e 0) := by
  unfold scalar
  rw [← Real.rpow_mul (zero_le_one.trans hZ), ← Real.rpow_mul (zero_le_one.trans hZ)]
  by_cases he : 0 ≤ e
  · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le hZ
      (show e * -(2 : ℝ) ≤ e * (1 / 4 : ℝ) by linarith)),
      max_eq_right (by linarith : -e ≤ 0), max_eq_left he]
    congr 1
    ring
  · have he' : e ≤ 0 := (lt_of_not_ge he).le
    rw [min_eq_left (Real.rpow_le_rpow_of_exponent_le hZ
      (show e * (1 / 4 : ℝ) ≤ e * -(2 : ℝ) by linarith)),
      max_eq_left (by linarith : 0 ≤ -e), max_eq_right he']
    congr 1
    ring

theorem scalar_sq_exponent (Z T v b : ℝ) (hZ : 1 ≤ Z) :
    scalar (Z ^ (v + 3 * b - T)) ^ 2 =
      Z ^ (-max (T - v - 3 * b) 0 / 2 - 4 * max (v + 3 * b - T) 0) := by
  rw [scalar_rpow Z _ hZ, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)]
  have he : -(v + 3 * b - T) = T - v - 3 * b := by ring
  rw [he]
  congr 1
  ring

/-- The density has the same modulus as the amplitude, so the previous
weighted-L1 argument applies with its unchanged universal majorant. -/
theorem weighted_density_integrable_and_bound
    (a : ℝ → ℂ) (ha : Continuous a) {Y C : ℝ} (hY : 0 < Y) (hC : 0 ≤ C)
    (p : ℕ)
    (hbound : ∀ t : ℝ, ‖a t‖ ≤ C * (1 + |t|) ^ (-((p : ℝ) + 2))) :
    Integrable (fun t : ℝ => (1 + |t|) ^ p * ‖density a Y t‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ p * ‖density a Y t‖) ≤
        C * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  have h := CommonMellin.weighted_density_integrable_and_bound a ha hY hC p hbound
  simpa only [norm_density a hY, CommonMellin.norm_density a hY] using h

#print axioms integral_physical_separation
#print axioms scalar_sq_exponent
#print axioms weighted_density_integrable_and_bound

end HeckeSkeleton.LowEnergy.CommonMellinTail
