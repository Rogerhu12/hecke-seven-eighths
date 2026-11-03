import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Norm twists of Dirichlet series with arbitrary indices

The index type is not replaced by the natural numbers: it can be the actual
nonzero integral ideals of a number field. Norms and coefficients are explicit
functions on that type. A coefficient twist by `q ^ (it)` corresponds exactly
to replacing `s` by `s - it`.

`dirichletSeries` is a total `tsum`; its equality below is an identity of total
functions. The separate summability and absolute summability theorems ensure
that it is an actual convergent series whenever the stated majorant converges.
No Hecke coefficients, Euler product, or analytic continuation are constructed
or assumed in this file.
-/

namespace HeckeGeneral.Analysis

noncomputable section

variable {ι : Type*}

/-- A Dirichlet term with an arbitrary positive real norm attached to each index. -/
def dirichletTerm (q : ι → ℝ) (a : ι → ℂ) (s : ℂ) (i : ι) : ℂ :=
  a i * (q i : ℂ) ^ (-s)

/-- The actual sum, once summability has been established, of these indexed terms. -/
def dirichletSeries (q : ι → ℝ) (a : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i, dirichletTerm q a s i

/-- Ideal-value normalization of a vertical norm twist. -/
def normTwistedCoefficients (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (i : ι) : ℂ :=
  a i * (q i : ℂ) ^ ((t : ℂ) * Complex.I)

theorem dirichletTerm_normTwist (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (i : ι) :
    dirichletTerm q (normTwistedCoefficients q a t) s i =
      dirichletTerm q a (s - (t : ℂ) * Complex.I) i := by
  unfold dirichletTerm normTwistedCoefficients
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hq i).ne')]
  have hexponent : (t : ℂ) * Complex.I + -s = -(s - (t : ℂ) * Complex.I) := by ring
  rw [hexponent]

theorem summable_dirichletTerm_normTwist_iff (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) :
    Summable (dirichletTerm q (normTwistedCoefficients q a t) s) ↔
      Summable (dirichletTerm q a (s - (t : ℂ) * Complex.I)) := by
  have hterms := funext (dirichletTerm_normTwist q a t s hq)
  rw [hterms]

/-- The shift also identifies genuine convergent sums, independently of the `tsum` convention. -/
theorem hasSum_dirichletTerm_normTwist_iff (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s v : ℂ)
    (hq : ∀ i, 0 < q i) :
    HasSum (dirichletTerm q (normTwistedCoefficients q a t) s) v ↔
      HasSum (dirichletTerm q a (s - (t : ℂ) * Complex.I)) v := by
  have hterms := funext (dirichletTerm_normTwist q a t s hq)
  rw [hterms]

theorem dirichletSeries_normTwist (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) :
    dirichletSeries q (normTwistedCoefficients q a t) s =
      dirichletSeries q a (s - (t : ℂ) * Complex.I) := by
  exact tsum_congr (dirichletTerm_normTwist q a t s hq)

theorem norm_dirichletTerm (q : ι → ℝ) (a : ι → ℂ) (s : ℂ) (i : ι)
    (hq : 0 < q i) :
    ‖dirichletTerm q a s i‖ = ‖a i‖ * (q i) ^ (-s.re) := by
  unfold dirichletTerm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp only [Complex.neg_re]

theorem norm_normTwistedCoefficients (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (i : ι)
    (hq : 0 < q i) : ‖normTwistedCoefficients q a t i‖ = ‖a i‖ := by
  unfold normTwistedCoefficients
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp

/-- A vertical twist preserves the absolute size of every Dirichlet term at `s`. -/
theorem norm_dirichletTerm_normTwist (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (i : ι) :
    ‖dirichletTerm q (normTwistedCoefficients q a t) s i‖ =
      ‖dirichletTerm q a s i‖ := by
  rw [norm_dirichletTerm q _ s i (hq i), norm_normTwistedCoefficients q a t i (hq i),
    norm_dirichletTerm q a s i (hq i)]

theorem absolutelySummable_dirichletTerm_normTwist_iff
    (q : ι → ℝ) (a : ι → ℂ) (t : ℝ) (s : ℂ) (hq : ∀ i, 0 < q i) :
    Summable (fun i => ‖dirichletTerm q (normTwistedCoefficients q a t) s i‖) ↔
      Summable (fun i => ‖dirichletTerm q a s i‖) := by
  have hterms := funext (norm_dirichletTerm_normTwist q a t s hq)
  rw [hterms]

/-- Comparison with a genuinely summable positive-norm majorant gives absolute convergence. -/
theorem absolutelySummable_dirichletTerm_of_majorant
    (q : ι → ℝ) (a : ι → ℂ) (w : ι → ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (ha : ∀ i, ‖a i‖ ≤ w i)
    (hmajor : Summable (fun i => w i * (q i) ^ (-s.re))) :
    Summable (fun i => ‖dirichletTerm q a s i‖) := by
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hmajor
  intro i
  rw [norm_dirichletTerm q a s i (hq i)]
  exact mul_le_mul_of_nonneg_right (ha i) (Real.rpow_nonneg (hq i).le _)

theorem summable_dirichletTerm_of_majorant
    (q : ι → ℝ) (a : ι → ℂ) (w : ι → ℝ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (ha : ∀ i, ‖a i‖ ≤ w i)
    (hmajor : Summable (fun i => w i * (q i) ^ (-s.re))) :
    Summable (dirichletTerm q a s) :=
  (absolutelySummable_dirichletTerm_of_majorant q a w s hq ha hmajor).of_norm

theorem absolutelySummable_dirichletTerm_of_unit_coefficients
    (q : ι → ℝ) (a : ι → ℂ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hmajor : Summable (fun i => (q i) ^ (-s.re))) :
    Summable (fun i => ‖dirichletTerm q a s i‖) :=
  absolutelySummable_dirichletTerm_of_majorant q a (fun _ => 1) s hq ha
    (by simpa using hmajor)

theorem summable_dirichletTerm_of_unit_coefficients
    (q : ι → ℝ) (a : ι → ℂ) (s : ℂ)
    (hq : ∀ i, 0 < q i) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hmajor : Summable (fun i => (q i) ^ (-s.re))) :
    Summable (dirichletTerm q a s) :=
  (absolutelySummable_dirichletTerm_of_unit_coefficients q a s hq ha hmajor).of_norm

/-- A majorant at a smaller real exponent controls the terms further to the right.
`q ≥ 1` is explicit; positivity alone would not justify this monotonicity. -/
theorem absolutelySummable_dirichletTerm_of_majorant_at
    (q : ι → ℝ) (a : ι → ℂ) (w : ι → ℝ) (s : ℂ) (σ : ℝ)
    (hq : ∀ i, 1 ≤ q i) (ha : ∀ i, ‖a i‖ ≤ w i) (hσ : σ ≤ s.re)
    (hmajor : Summable (fun i => w i * (q i) ^ (-σ))) :
    Summable (fun i => ‖dirichletTerm q a s i‖) := by
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ hmajor
  intro i
  have hqpos : 0 < q i := lt_of_lt_of_le zero_lt_one (hq i)
  have hw : 0 ≤ w i := (norm_nonneg _).trans (ha i)
  rw [norm_dirichletTerm q a s i hqpos]
  exact (mul_le_mul_of_nonneg_right (ha i) (Real.rpow_nonneg hqpos.le _)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hq i) (neg_le_neg hσ)) hw)

/-- Absolute convergence on `Re s > 1`, from actual majorant summability there.
The hypotheses assert summability of real numerical functions, without a
Hecke L-function or an analytic-continuation structure as an input. -/
theorem absolutelySummable_dirichletTerm_on_one_lt_re
    (q : ι → ℝ) (a : ι → ℂ) (w : ι → ℝ)
    (hq : ∀ i, 1 ≤ q i) (ha : ∀ i, ‖a i‖ ≤ w i)
    (hmajor : ∀ σ : ℝ, 1 < σ → Summable (fun i => w i * (q i) ^ (-σ)))
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i => ‖dirichletTerm q a s i‖) := by
  apply absolutelySummable_dirichletTerm_of_majorant_at q a w s ((1 + s.re) / 2) hq ha
  · linarith
  · exact hmajor _ (by linarith)

theorem summable_dirichletTerm_on_one_lt_re
    (q : ι → ℝ) (a : ι → ℂ) (w : ι → ℝ)
    (hq : ∀ i, 1 ≤ q i) (ha : ∀ i, ‖a i‖ ≤ w i)
    (hmajor : ∀ σ : ℝ, 1 < σ → Summable (fun i => w i * (q i) ^ (-σ)))
    {s : ℂ} (hs : 1 < s.re) : Summable (dirichletTerm q a s) :=
  (absolutelySummable_dirichletTerm_on_one_lt_re q a w hq ha hmajor hs).of_norm

end

end HeckeGeneral.Analysis
