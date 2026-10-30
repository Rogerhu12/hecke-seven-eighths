import Zeta23.GammaFacts.StirlingVert
import HeckeGeneral.Analysis.HeckeArchimedeanGamma
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharp horizontal Gamma ratios at large imaginary height

The digamma estimate is the proved theorem from Anthropic's `zeta23`,
not its abstract `GammaFacts` hypotheses. Horizontal differentiation of
`log ‖Γ(a + it)‖` and the mean value inequality transfer that estimate to
the actual Gamma ratio. The initial range is `0 < a,b ≤ 1` and `|t| ≥ 1/2`.
The strip extension covers all bounded positive abscissae, with its constant
explicitly depending on the upper abscissa bound. There is no bounded-height
claim or assertion about nonpositive real shifts.

The bounded-strip real-part argument refines the decomposition used in
the real-part section of `Zeta23/GammaFacts/StirlingVert.lean`: its new constant allows positive
abscissae. The derivative, horizontal ratio, and actual character-product
bridges below are local proofs built on that estimate.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Characters
open scoped ComplexConjugate BigOperators Classical

private theorem hasDerivAt_log_norm_of_mul
    {f : ℝ → ℂ} {a : ℝ} {ψ : ℂ} (h : HasDerivAt f (ψ * f a) a)
    (h0 : f a ≠ 0) : HasDerivAt (fun x => Real.log ‖f x‖) ψ.re a := by
  have hn : ‖f a‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hi : inner ℝ (f a) (ψ * f a) = ψ.re * ‖f a‖ ^ 2 := by
    rw [Complex.inner]
    rw [show ψ * f a * conj (f a) = ψ * (f a * conj (f a)) by ring,
      Complex.mul_conj, Complex.mul_re]
    simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  have hs := (h.norm_sq.log (pow_ne_zero 2 hn)).const_mul (1 / 2 : ℝ)
  rw [hi] at hs
  convert hs using 1
  · funext x
    rw [Real.log_pow]
    ring
  · field_simp

/-- The real derivative along a horizontal line is the real digamma value.
Positive abscissa ensures the Gamma function is differentiable and nonzero. -/
theorem hasDerivAt_log_norm_Gamma_horizontal {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + Complex.I * t)‖)
      (Complex.digamma ((a : ℂ) + Complex.I * t)).re a := by
  let z : ℂ := (a : ℂ) + Complex.I * t
  have hz : 0 < z.re := by simpa [z] using ha
  have h0 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hd := (Complex.differentiableAt_Gamma z (fun n h => by
    have he := congrArg Complex.re h
    simp at he
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).hasDerivAt
  have hh : HasDerivAt (fun x : ℝ => Complex.Gamma ((x : ℂ) + Complex.I * t))
      (Complex.digamma z * Complex.Gamma z) a := by
    have hc := (hd.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).add_const
      (Complex.I * (t : ℂ)))).comp_ofReal
    simpa only [Complex.digamma, logDeriv_apply, div_mul_cancel₀ _ h0, mul_one,
      Function.comp_def, id_eq] using hc
  exact hasDerivAt_log_norm_of_mul hh h0

/-- The derivative error on the horizontal unit strip has an explicit
height-uniform constant, inherited from the proved digamma Stirling estimate. -/
theorem hasDerivAt_log_norm_Gamma_horizontal_error {a t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 / 2 ≤ |t|) :
    HasDerivAt
      (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + Complex.I * t)‖ -
        Real.log (abs t) * x)
      ((Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)) a ∧
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by
  constructor
  · simpa only [Pi.sub_apply, mul_one] using! (hasDerivAt_log_norm_Gamma_horizontal ha t).sub
      ((hasDerivAt_id a).const_mul (Real.log (abs t)))
  · exact Zeta23.StirlingVert.re_digamma_stirling' ha ha1 ht

/-- Integrating the true logarithmic derivative over an ordered horizontal
segment gives the sharp `b-a` exponent and an error of size `(b-a)/t²`. -/
theorem log_norm_Gamma_horizontal_sub_bound {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (ht : 1 / 2 ≤ |t|) :
    |Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
      (b - a) * Real.log (abs t)| ≤ (5 / t ^ 2) * (b - a) := by
  let f : ℝ → ℝ := fun x =>
    Real.log ‖Complex.Gamma ((x : ℂ) + Complex.I * t)‖ - Real.log (abs t) * x
  let f' : ℝ → ℝ := fun x =>
    (Complex.digamma ((x : ℂ) + Complex.I * t)).re - Real.log (abs t)
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x := by
    intro x hx
    exact (hasDerivAt_log_norm_Gamma_horizontal_error (lt_of_lt_of_le ha hx.1)
      (hx.2.trans hb) ht).1
  have hbound : ∀ x ∈ Set.Icc a b, ‖f' x‖ ≤ 5 / t ^ 2 := by
    intro x hx
    exact (hasDerivAt_log_norm_Gamma_horizontal_error (lt_of_lt_of_le ha hx.1)
      (hx.2.trans hb) ht).2
  have hm := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hbound
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have he : f b - f a =
      Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
      (b - a) * Real.log (abs t) := by dsimp [f]; ring
  simpa only [he, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hm

/-- The same error estimate for either direction along the horizontal segment. -/
theorem log_norm_Gamma_horizontal_sub_bound_abs {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    |Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
      (b - a) * Real.log (abs t)| ≤ (5 / t ^ 2) * |b - a| := by
  by_cases hab : a ≤ b
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      log_norm_Gamma_horizontal_sub_bound ha hab hb1 ht
  · have hba : b ≤ a := le_of_not_ge hab
    have h := log_norm_Gamma_horizontal_sub_bound hb hba ha1 ht
    have he : Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
        (b - a) * Real.log (abs t) =
      -(Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
        Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
        (a - b) * Real.log (abs t)) := by ring
    rw [he, abs_neg, abs_of_nonpos (sub_nonpos.mpr hba)]
    simpa only [neg_sub] using h

private theorem norm_ratio_bounds_of_log_error {u v : ℂ} {x δ E : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hx : 0 < x)
    (h : |Real.log ‖u‖ - Real.log ‖v‖ - δ * Real.log x| ≤ E) :
    Real.exp (-E) * x ^ δ ≤ ‖u / v‖ ∧
      ‖u / v‖ ≤ Real.exp E * x ^ δ := by
  have hup := norm_pos_iff.mpr hu
  have hvp := norm_pos_iff.mpr hv
  rcases abs_le.mp h with ⟨hl, hr⟩
  constructor
  · have he := Real.exp_le_exp.mpr (show
      -E + Real.log x * δ ≤ Real.log ‖u‖ - Real.log ‖v‖ by linarith)
    simpa only [Real.exp_sub, Real.exp_log hup, Real.exp_log hvp,
      Real.exp_add, ← Real.rpow_def_of_pos hx, norm_div] using he
  · have he := Real.exp_le_exp.mpr (show
      Real.log ‖u‖ - Real.log ‖v‖ ≤ E + Real.log x * δ by linarith)
    simpa only [Real.exp_sub, Real.exp_log hup, Real.exp_log hvp,
      Real.exp_add, ← Real.rpow_def_of_pos hx, norm_div] using he

/-- Sharp vertical Gamma ratio upper bound on the positive horizontal unit strip.
The exponent is exactly `b-a`, including negative exponents. -/
theorem norm_Gamma_ratio_vertical_le {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    ‖Complex.Gamma ((b : ℂ) + Complex.I * t) /
      Complex.Gamma ((a : ℂ) + Complex.I * t)‖ ≤
      Real.exp ((5 / t ^ 2) * |b - a|) * |t| ^ (b - a) := by
  exact (norm_ratio_bounds_of_log_error
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
    (lt_of_lt_of_le (by norm_num) ht)
    (log_norm_Gamma_horizontal_sub_bound_abs ha ha1 hb hb1 ht)).2

/-- The matching lower bound excludes loss of powers in the vertical estimate. -/
theorem exp_mul_rpow_le_norm_Gamma_ratio_vertical {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    Real.exp (-((5 / t ^ 2) * |b - a|)) * |t| ^ (b - a) ≤
      ‖Complex.Gamma ((b : ℂ) + Complex.I * t) /
        Complex.Gamma ((a : ℂ) + Complex.I * t)‖ := by
  exact (norm_ratio_bounds_of_log_error
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
    (lt_of_lt_of_le (by norm_num) ht)
    (log_norm_Gamma_horizontal_sub_bound_abs ha ha1 hb hb1 ht)).1

/-- An explicit error constant for a bounded positive abscissa strip. -/
def gammaVerticalStripConstant (A : ℝ) : ℝ := 3 + A + A ^ 2

/-- The complex digamma Stirling theorem yields a real-part estimate on every
bounded positive strip, with an explicit constant depending only on its width. -/
theorem re_digamma_vertical_strip_error {a A t : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤
      gammaVerticalStripConstant A / t ^ 2 := by
  let w : ℂ := (a : ℂ) + Complex.I * t
  have hre : w.re = a := by simp [w]
  have him : w.im = t := by simp [w]
  have hA : 0 < A := ha.trans_le haA
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have htne : t ≠ 0 := by intro h; simp [h] at ht0
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hnorm : 0 < a ^ 2 + t ^ 2 := by positivity
  have hmain := Zeta23.StirlingVert.digamma_stirling (w := w) (by simpa [hre] using ha)
    (by simpa [him] using ht)
  rw [him] at hmain
  have hlogre : (Complex.log w).re = (1 / 2) * Real.log (a ^ 2 + t ^ 2) := by
    rw [Complex.log_re, Complex.norm_eq_sqrt_sq_add_sq, hre, him,
      Real.log_sqrt hnorm.le]
    ring
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring,
      Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hInv : |a / (2 * (a ^ 2 + t ^ 2))| ≤ A / t ^ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) ht2]
    nlinarith [sq_nonneg a]
  have hPsi : |(Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)| ≤
      (3 + A) / t ^ 2 := by
    have he : (Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2) =
      (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re -
        a / (2 * (a ^ 2 + t ^ 2)) := by
      rw [Complex.add_re, Complex.sub_re, hlogre, hinvre]; ring
    rw [he]
    have hRe := (Complex.abs_re_le_norm _).trans hmain
    have hTriangle := abs_sub (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re
      (a / (2 * (a ^ 2 + t ^ 2)))
    calc
      _ ≤ 3 / t ^ 2 + A / t ^ 2 := hTriangle.trans (add_le_add hRe hInv)
      _ = (3 + A) / t ^ 2 := by ring
  have hLog : |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| ≤
      A ^ 2 / t ^ 2 := by
    have he : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by field_simp [htne]; ring
    have hgap : (1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t) =
        (1 / 2) * Real.log (1 + a ^ 2 / t ^ 2) := by
      rw [he, Real.log_mul ht2.ne' (by positivity), ← sq_abs, Real.log_pow]
      ring
    have hx0 : 0 ≤ a ^ 2 / t ^ 2 := by positivity
    have hg0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) := Real.log_nonneg (by linarith)
    have hg1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / t ^ 2)
    have hsq : a ^ 2 / t ^ 2 ≤ A ^ 2 / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ ht2.le
      nlinarith
    rw [hgap, abs_of_nonneg (by positivity)]
    linarith
  calc
    _ ≤ |(Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)| +
      |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| := abs_sub_le _ _ _
    _ ≤ (3 + A) / t ^ 2 + A ^ 2 / t ^ 2 := add_le_add hPsi hLog
    _ = gammaVerticalStripConstant A / t ^ 2 := by dsimp [gammaVerticalStripConstant]; ring

/-- The genuine horizontal integral estimate on an arbitrary bounded positive strip. -/
theorem log_norm_Gamma_horizontal_strip_sub_bound {a b A t : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbA : b ≤ A)
    (ht : 1 / 2 ≤ |t|) :
    |Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
      (b - a) * Real.log (abs t)| ≤
      (gammaVerticalStripConstant A / t ^ 2) * |b - a| := by
  let f : ℝ → ℝ := fun x =>
    Real.log ‖Complex.Gamma ((x : ℂ) + Complex.I * t)‖ - Real.log (abs t) * x
  let f' : ℝ → ℝ := fun x =>
    (Complex.digamma ((x : ℂ) + Complex.I * t)).re - Real.log (abs t)
  have hx : ∀ x ∈ Set.uIcc a b, 0 < x ∧ x ≤ A := by
    intro x hx
    exact ⟨(lt_min ha hb).trans_le hx.1, hx.2.trans (max_le haA hbA)⟩
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x := by
    intro x hmem
    simpa only [Pi.sub_apply, mul_one] using!
      (hasDerivAt_log_norm_Gamma_horizontal (hx x hmem).1 t).sub
        ((hasDerivAt_id x).const_mul (Real.log (abs t)))
  have hbound : ∀ x ∈ Set.uIcc a b, ‖f' x‖ ≤ gammaVerticalStripConstant A / t ^ 2 := by
    intro x hmem
    exact re_digamma_vertical_strip_error (hx x hmem).1 (hx x hmem).2 ht
  have hm := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hmem => (hd x hmem).hasDerivWithinAt) hbound
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have he : f b - f a =
      Real.log ‖Complex.Gamma ((b : ℂ) + Complex.I * t)‖ -
      Real.log ‖Complex.Gamma ((a : ℂ) + Complex.I * t)‖ -
      (b - a) * Real.log (abs t) := by dsimp [f]; ring
  simpa only [he, Real.norm_eq_abs] using hm

/-- Sharp Gamma ratio bounds for any fixed positive abscissa strip.
All constants are uniform in height and in both abscissae within that strip. -/
theorem norm_Gamma_ratio_vertical_strip_bounds {a b A t : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbA : b ≤ A)
    (ht : 1 / 2 ≤ |t|) :
    Real.exp (-((gammaVerticalStripConstant A / t ^ 2) * |b - a|)) * |t| ^ (b - a) ≤
      ‖Complex.Gamma ((b : ℂ) + Complex.I * t) /
        Complex.Gamma ((a : ℂ) + Complex.I * t)‖ ∧
    ‖Complex.Gamma ((b : ℂ) + Complex.I * t) /
      Complex.Gamma ((a : ℂ) + Complex.I * t)‖ ≤
      Real.exp ((gammaVerticalStripConstant A / t ^ 2) * |b - a|) * |t| ^ (b - a) := by
  apply norm_ratio_bounds_of_log_error
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
    (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
    (lt_of_lt_of_le (by norm_num) ht)
  exact log_norm_Gamma_horizontal_strip_sub_bound ha haA hb hbA ht

/-- The explicit abscissa bound for all angular weights on the quarter strip. -/
def angularGammaVerticalUpper (m : ℤ) : ℝ := angularHalfWeight m + 1

/-- The actual local multiplier has the sharp height exponent `2 Re(s)`.
The height is the shifted radial parameter `Im(s)+τ`, and the same bound
applies to either of the two sixth offsets. -/
theorem norm_localGammaRatio_vertical_bounds (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ)
    (hs : |s.re| ≤ 1 / 4) (ht : 1 / 2 ≤ |s.im + τ|) :
    Real.exp (-((gammaVerticalStripConstant (angularGammaVerticalUpper m) /
      (s.im + τ) ^ 2) * |2 * s.re|)) * |s.im + τ| ^ (2 * s.re) ≤
      ‖localGammaRatio m τ b s‖ ∧
    ‖localGammaRatio m τ b s‖ ≤
      Real.exp ((gammaVerticalStripConstant (angularGammaVerticalUpper m) /
        (s.im + τ) ^ 2) * |2 * s.re|) * |s.im + τ| ^ (2 * s.re) := by
  let a : ℝ := angularGammaShift m b - s.re
  let c : ℝ := angularGammaShift m b + s.re
  have hlow := angularGammaShift_ge_third m b
  have hhigh : angularGammaShift m b ≤ angularHalfWeight m + 1 / 6 := by
    dsimp [angularGammaShift]
    simpa only [add_comm] using add_le_add_left (gammaSixthOffset_upper b) (angularHalfWeight m)
  rcases abs_le.mp hs with ⟨hslo, hshi⟩
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have haA : a ≤ angularGammaVerticalUpper m := by
    dsimp [a, angularGammaVerticalUpper]; linarith
  have hcA : c ≤ angularGammaVerticalUpper m := by
    dsimp [c, angularGammaVerticalUpper]; linarith
  have hnum : angularGammaArgument m τ b s = (c : ℂ) + Complex.I * (s.im + τ) := by
    apply Complex.ext <;> simp [angularGammaArgument, c]
  have hden : angularGammaArgument m (-τ) b (-s) =
      conj ((a : ℂ) + Complex.I * (s.im + τ)) := by
    apply Complex.ext <;> simp [angularGammaArgument, a] <;> ring
  have hnorm : ‖localGammaRatio m τ b s‖ =
      ‖Complex.Gamma ((c : ℂ) + Complex.I * (s.im + τ)) /
        Complex.Gamma ((a : ℂ) + Complex.I * (s.im + τ))‖ := by
    rw [localGammaRatio, hnum, hden, Complex.Gamma_conj, norm_div, norm_div,
      RCLike.norm_conj]
  have hdelta : c - a = 2 * s.re := by dsimp [c, a]; ring
  rw [hnorm]
  simpa only [hdelta, Complex.ofReal_add] using
    norm_Gamma_ratio_vertical_strip_bounds ha haA hc hcA ht

private theorem exp_mul_rpow_square (E x σ : ℝ) (hx : 0 < x) :
    (Real.exp E * x ^ (2 * σ)) * (Real.exp E * x ^ (2 * σ)) =
      Real.exp (2 * E) * x ^ (4 * σ) := by
  rw [mul_mul_mul_comm, ← Real.exp_add, ← Real.rpow_add hx]
  rw [show E + E = 2 * E by ring, show 2 * σ + 2 * σ = 4 * σ by ring]

/-- The two actual sixth-offset factors at a complex place have sharp
height exponent `4 Re(s)`, uniformly for every integer angular weight. -/
theorem norm_complexPlaceGammaRatio_vertical_bounds (m : ℤ) (τ : ℝ) (s : ℂ)
    (hs : |s.re| ≤ 1 / 4) (ht : 1 / 2 ≤ |s.im + τ|) :
    Real.exp (-(2 * ((gammaVerticalStripConstant (angularGammaVerticalUpper m) /
      (s.im + τ) ^ 2) * |2 * s.re|))) * |s.im + τ| ^ (4 * s.re) ≤
      ‖complexPlaceGammaRatio m τ s‖ ∧
    ‖complexPlaceGammaRatio m τ s‖ ≤
      Real.exp (2 * ((gammaVerticalStripConstant (angularGammaVerticalUpper m) /
        (s.im + τ) ^ 2) * |2 * s.re|)) * |s.im + τ| ^ (4 * s.re) := by
  have htrue := norm_localGammaRatio_vertical_bounds m τ true s hs ht
  have hfalse := norm_localGammaRatio_vertical_bounds m τ false s hs ht
  have hp : 0 < |s.im + τ| := lt_of_lt_of_le (by norm_num) ht
  rw [complexPlaceGammaRatio, norm_prod, Fintype.prod_bool]
  constructor
  · have h := mul_le_mul htrue.1 hfalse.1 (by positivity)
      (norm_nonneg (localGammaRatio m τ true s))
    rw [exp_mul_rpow_square _ _ _ hp] at h
    simpa only [mul_neg] using h
  · have h := mul_le_mul htrue.2 hfalse.2
      (norm_nonneg (localGammaRatio m τ false s)) (by positivity)
    rw [exp_mul_rpow_square _ _ _ hp] at h
    exact h

/-- The explicit Stirling error for the two factors at one complex place. -/
def complexGammaVerticalError (m : ℤ) (τ : ℝ) (s : ℂ) : ℝ :=
  2 * ((gammaVerticalStripConstant (angularGammaVerticalUpper m) /
    (s.im + τ) ^ 2) * |2 * s.re|)

/-- Lower (`false`) and upper (`true`) envelopes with the exact height exponent. -/
def complexGammaVerticalEnvelope (m : ℤ) (τ : ℝ) (s : ℂ) (upper : Bool) : ℝ :=
  Real.exp (if upper then complexGammaVerticalError m τ s
    else -complexGammaVerticalError m τ s) * |s.im + τ| ^ (4 * s.re)

theorem complexGammaVerticalEnvelope_nonneg (m : ℤ) (τ : ℝ) (s : ℂ) (upper : Bool) :
    0 ≤ complexGammaVerticalEnvelope m τ s upper := by
  unfold complexGammaVerticalEnvelope
  positivity

/-- Multiplying genuine local bounds retains each individual radial height. -/
theorem norm_archimedeanGammaRatio_vertical_bounds {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) (s : ℂ) (hs : |s.re| ≤ 1 / 4)
    (ht : ∀ v, 1 / 2 ≤ |s.im + τ v|) :
    (∏ v, complexGammaVerticalEnvelope (m v) (τ v) s false) ≤
      ‖archimedeanGammaRatio m τ s‖ ∧
    ‖archimedeanGammaRatio m τ s‖ ≤
      ∏ v, complexGammaVerticalEnvelope (m v) (τ v) s true := by
  have hlocal : ∀ v,
      complexGammaVerticalEnvelope (m v) (τ v) s false ≤
        ‖complexPlaceGammaRatio (m v) (τ v) s‖ ∧
      ‖complexPlaceGammaRatio (m v) (τ v) s‖ ≤
        complexGammaVerticalEnvelope (m v) (τ v) s true := by
    intro v
    simpa only [complexGammaVerticalEnvelope, complexGammaVerticalError,
      Bool.false_eq_true, ↓reduceIte] using
      norm_complexPlaceGammaRatio_vertical_bounds (m v) (τ v) s hs (ht v)
  rw [archimedeanGammaRatio, norm_prod]
  constructor
  · exact Finset.prod_le_prod₀
      (fun v _ => complexGammaVerticalEnvelope_nonneg (m v) (τ v) s false)
      (fun v _ => (hlocal v).1)
  · exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _)
      (fun v _ => (hlocal v).2)

/-- The envelopes formed from actual complex-place parameters of a Hecke character.
This definition includes complex places only; real-place bounds are a separate obligation. -/
def heckeGammaVerticalEnvelope (K : Type*) [Field K] [NumberField K]
    (χ : HeckeCharacter K) (s : ℂ) (upper : Bool) : ℝ :=
  ∏ v : {v : InfinitePlace K // v.IsComplex},
    complexGammaVerticalEnvelope (heckeComplexWeight K v.val v.property χ)
      (heckeComplexParameter K v.val v.property χ) s upper

/-- Sharp bounds for the existing actual Hecke Gamma product, with no theta identity assumed. -/
theorem norm_heckeArchimedeanGammaRatio_vertical_bounds
    (K : Type*) [Field K] [NumberField K] (χ : HeckeCharacter K) (s : ℂ)
    (hs : |s.re| ≤ 1 / 4)
    (ht : ∀ v : {v : InfinitePlace K // v.IsComplex},
      1 / 2 ≤ |s.im + heckeComplexParameter K v.val v.property χ|) :
    heckeGammaVerticalEnvelope K χ s false ≤ ‖heckeArchimedeanGammaRatio K χ s‖ ∧
      ‖heckeArchimedeanGammaRatio K χ s‖ ≤ heckeGammaVerticalEnvelope K χ s true := by
  exact norm_archimedeanGammaRatio_vertical_bounds _ _ s hs ht

/-- For an actual finite-order child and norm twist, the height shift is exactly
`Im(s)-t+τ_v(χ)`, matching the previously proved idelic norm convention. -/
theorem norm_heckeArchimedeanGammaRatio_child_vertical_bounds
    (K : Type*) [Field K] [NumberField K] (χ θ : HeckeCharacter K)
    (hθ : FiniteOrder θ) (t : ℝ) (s : ℂ) (hs : |s.re| ≤ 1 / 4)
    (ht : ∀ v : {v : InfinitePlace K // v.IsComplex},
      1 / 2 ≤ |s.im - t + heckeComplexParameter K v.val v.property χ|) :
    heckeGammaVerticalEnvelope K χ (s - (t : ℂ) * Complex.I) false ≤
      ‖heckeArchimedeanGammaRatio K (θ * χ * heckeNormTwist K t) s‖ ∧
    ‖heckeArchimedeanGammaRatio K (θ * χ * heckeNormTwist K t) s‖ ≤
      heckeGammaVerticalEnvelope K χ (s - (t : ℂ) * Complex.I) true := by
  rw [heckeArchimedeanGammaRatio_child K χ θ hθ t s]
  apply norm_heckeArchimedeanGammaRatio_vertical_bounds
  · simpa using hs
  · simpa using ht

end HeckeGeneral.Analysis


