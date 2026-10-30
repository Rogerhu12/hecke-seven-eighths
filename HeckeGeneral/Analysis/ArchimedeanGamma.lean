import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions

/-!+# The explicit archimedean Gamma multiplier

For an integer angular weight `m`, the shift is `(|m|+1)/2 ± 1/6`.
Both numerator Gamma arguments have positive real part on `Re(s)>-1/3`.
The denominator is handled by the entire reciprocal Gamma function, including
its zeros at nonpositive integers. Thus this actual special-function multiplier
is analytic across `Re(s)=-1/4`. This file proves neither the theta-period
identity that would produce the multiplier nor its Stirling growth estimate.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped BigOperators ComplexConjugate

/-- The fixed half-integral shift attached to an integer angular weight. -/
def angularHalfWeight (m : ℤ) : ℝ := ((m.natAbs : ℝ) + 1) / 2

def gammaSixthOffset (b : Bool) : ℝ := if b then 1 / 6 else -(1 / 6)

def angularGammaShift (m : ℤ) (b : Bool) : ℝ := angularHalfWeight m + gammaSixthOffset b

theorem angularHalfWeight_ge_half (m : ℤ) : 1 / 2 ≤ angularHalfWeight m := by
  unfold angularHalfWeight
  have h : (0 : ℝ) ≤ m.natAbs := Nat.cast_nonneg _
  linarith

theorem angularHalfWeight_eq_abs (m : ℤ) : angularHalfWeight m = (|(m : ℝ)| + 1) / 2 := by
  unfold angularHalfWeight
  congr 2
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  rfl

@[simp] theorem angularHalfWeight_neg (m : ℤ) : angularHalfWeight (-m) = angularHalfWeight m := by
  simp [angularHalfWeight]

theorem gammaSixthOffset_lower (b : Bool) : -(1 / 6) ≤ gammaSixthOffset b := by
  cases b <;> norm_num [gammaSixthOffset]

theorem gammaSixthOffset_upper (b : Bool) : gammaSixthOffset b ≤ 1 / 6 := by
  cases b <;> norm_num [gammaSixthOffset]

theorem angularGammaShift_ge_third (m : ℤ) (b : Bool) : 1 / 3 ≤ angularGammaShift m b := by
  have hm := angularHalfWeight_ge_half m
  have hb := gammaSixthOffset_lower b
  unfold angularGammaShift
  linarith

theorem angularGammaShift_pos (m : ℤ) (b : Bool) : 0 < angularGammaShift m b :=
  lt_of_lt_of_le (by norm_num) (angularGammaShift_ge_third m b)

/-- The numerator Gamma argument, retaining each individual radial parameter. -/
def angularGammaArgument (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) : ℂ :=
  (angularGammaShift m b : ℂ) + s + (τ : ℂ) * Complex.I

@[simp] theorem angularGammaArgument_re (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) :
    (angularGammaArgument m τ b s).re = angularGammaShift m b + s.re := by
  simp [angularGammaArgument]

@[simp] theorem angularGammaArgument_im (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) :
    (angularGammaArgument m τ b s).im = s.im + τ := by
  simp [angularGammaArgument]

theorem angularGammaArgument_re_pos (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hs : -(1 / 3) < s.re) : 0 < (angularGammaArgument m τ b s).re := by
  rw [angularGammaArgument_re]
  have h := angularGammaShift_ge_third m b
  linarith

/-- The actual Gamma argument cannot encounter a pole on the specified half-plane. -/
theorem angularGammaArgument_ne_neg_nat (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hs : -(1 / 3) < s.re) (n : ℕ) : angularGammaArgument m τ b s ≠ -(n : ℂ) := by
  intro he
  have h := angularGammaArgument_re_pos m τ b hs
  rw [he] at h
  simp only [Complex.neg_re, Complex.natCast_re] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem angularGamma_ne_zero (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hs : -(1 / 3) < s.re) : Complex.Gamma (angularGammaArgument m τ b s) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (angularGammaArgument_re_pos m τ b hs)

theorem analyticAt_angularGammaArgument (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) :
    AnalyticAt ℂ (angularGammaArgument m τ b) s := by
  unfold angularGammaArgument
  exact (analyticAt_const.add analyticAt_id).add analyticAt_const

theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro n he
    rw [he] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

theorem analyticAt_angularGamma (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hs : -(1 / 3) < s.re) :
    AnalyticAt ℂ (fun z => Complex.Gamma (angularGammaArgument m τ b z)) s :=
  (analyticAt_Gamma_of_re_pos (angularGammaArgument_re_pos m τ b hs)).comp
    (analyticAt_angularGammaArgument m τ b s)

/-- Reciprocal Gamma is entire even when the reflected argument is a pole of Gamma. -/
theorem analyticAt_reflectedReciprocalGamma (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) :
    AnalyticAt ℂ (fun z => (Complex.Gamma (angularGammaArgument m (-τ) b (-z)))⁻¹) s := by
  exact (Complex.differentiable_one_div_Gamma.analyticAt _).comp
    ((analyticAt_angularGammaArgument m (-τ) b (-s)).comp analyticAt_id.neg)

def localGammaRatio (m : ℤ) (τ : ℝ) (b : Bool) (s : ℂ) : ℂ :=
  Complex.Gamma (angularGammaArgument m τ b s) /
    Complex.Gamma (angularGammaArgument m (-τ) b (-s))

theorem analyticAt_localGammaRatio (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hs : -(1 / 3) < s.re) : AnalyticAt ℂ (localGammaRatio m τ b) s := by
  unfold localGammaRatio
  simp only [div_eq_mul_inv]
  exact (analyticAt_angularGamma m τ b hs).mul (analyticAt_reflectedReciprocalGamma m τ b s)

theorem localGammaRatio_ne_zero (m : ℤ) (τ : ℝ) (b : Bool) {s : ℂ}
    (hl : -(1 / 3) < s.re) (hr : s.re < 1 / 3) : localGammaRatio m τ b s ≠ 0 := by
  apply div_ne_zero (angularGamma_ne_zero m τ b hl)
  apply angularGamma_ne_zero
  simp only [Complex.neg_re]
  linarith

/-- The two Gamma factors at one complex place. -/
def complexPlaceGammaRatio (m : ℤ) (τ : ℝ) (s : ℂ) : ℂ :=
  ∏ b : Bool, localGammaRatio m τ b s

theorem analyticAt_complexPlaceGammaRatio (m : ℤ) (τ : ℝ) {s : ℂ}
    (hs : -(1 / 3) < s.re) : AnalyticAt ℂ (complexPlaceGammaRatio m τ) s :=
  Finset.analyticAt_fun_prod _ fun b _ => analyticAt_localGammaRatio m τ b hs

theorem complexPlaceGammaRatio_ne_zero (m : ℤ) (τ : ℝ) {s : ℂ}
    (hl : -(1 / 3) < s.re) (hr : s.re < 1 / 3) : complexPlaceGammaRatio m τ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  exact localGammaRatio_ne_zero m τ b hl hr

/-- The exact archimedean Gamma product for any finite set of complex places. -/
def archimedeanGammaRatio {ι : Type*} [Fintype ι] (m : ι → ℤ) (τ : ι → ℝ) (s : ℂ) : ℂ :=
  ∏ v, complexPlaceGammaRatio (m v) (τ v) s

theorem analyticAt_archimedeanGammaRatio {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) {s : ℂ} (hs : -(1 / 3) < s.re) :
    AnalyticAt ℂ (archimedeanGammaRatio m τ) s :=
  Finset.analyticAt_fun_prod _ fun v _ => analyticAt_complexPlaceGammaRatio (m v) (τ v) hs

theorem archimedeanGammaRatio_ne_zero {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) {s : ℂ} (hl : -(1 / 3) < s.re) (hr : s.re < 1 / 3) :
    archimedeanGammaRatio m τ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  exact complexPlaceGammaRatio_ne_zero (m v) (τ v) hl hr

theorem analyticOnNhd_archimedeanGammaRatio {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) :
    AnalyticOnNhd ℂ (archimedeanGammaRatio m τ) {s : ℂ | -(1 / 3) < s.re} :=
  fun _ hs => analyticAt_archimedeanGammaRatio m τ hs

/-- The line required for the quarter-power contour shift lies strictly inside this domain. -/
theorem analyticAt_archimedeanGammaRatio_quarter_line {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) (t : ℝ) :
    AnalyticAt ℂ (archimedeanGammaRatio m τ) (-(1 / 4) + (t : ℂ) * Complex.I) := by
  apply analyticAt_archimedeanGammaRatio
  norm_num

/-- On the imaginary axis the denominator argument is the conjugate of the numerator. -/
theorem angularGammaArgument_reflected_conj (m : ℤ) (τ t : ℝ) (b : Bool) :
    angularGammaArgument m (-τ) b (-((t : ℂ) * Complex.I)) =
      conj (angularGammaArgument m τ b ((t : ℂ) * Complex.I)) := by
  apply Complex.ext <;> simp [angularGammaArgument]

theorem norm_localGammaRatio_imaginary (m : ℤ) (τ t : ℝ) (b : Bool) :
    ‖localGammaRatio m τ b ((t : ℂ) * Complex.I)‖ = 1 := by
  unfold localGammaRatio
  rw [angularGammaArgument_reflected_conj, Complex.Gamma_conj, norm_div, RCLike.norm_conj]
  apply div_self
  exact norm_ne_zero_iff.mpr (angularGamma_ne_zero m τ b (by norm_num))

theorem norm_complexPlaceGammaRatio_imaginary (m : ℤ) (τ t : ℝ) :
    ‖complexPlaceGammaRatio m τ ((t : ℂ) * Complex.I)‖ = 1 := by
  unfold complexPlaceGammaRatio
  rw [norm_prod]
  simp only [norm_localGammaRatio_imaginary, Finset.prod_const_one]

theorem norm_archimedeanGammaRatio_imaginary {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (τ : ι → ℝ) (t : ℝ) :
    ‖archimedeanGammaRatio m τ ((t : ℂ) * Complex.I)‖ = 1 := by
  unfold archimedeanGammaRatio
  rw [norm_prod]
  simp only [norm_complexPlaceGammaRatio_imaginary, Finset.prod_const_one]

end HeckeGeneral.Analysis
