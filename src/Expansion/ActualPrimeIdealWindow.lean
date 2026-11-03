import Expansion.ActualZetaLogDerivative
import Expansion.ActualPrimeCancellation
import Expansion.ActualPrimeWindowPositivity
import HeckeGeneral.Analysis.MomentPrimeWindows
import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift

/-!
# A prime ideal theorem for the actual smooth normalizer windows

The initial integral is the actual logarithmic prime-power series of the
trivial character. A simple-pole shift across one produces its exact Mellin
residue and a fixed power saving. The divided profile is the original
window divided by `log (X*y)`; its seminorm constant is uniform before X.
Higher prime powers and the original fixed finite set S are then removed.
No prime-window lower bound or normalizer estimate is assumed or imported.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set Filter MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open ExpansionInterfaces.Mellin PrimeCancellationPrimeSeries
open DedekindZetaZeroFree
open DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift
open scoped Classical BigOperators Topology ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The literal trivial-character logarithmic derivative in the smoothed
prime-power integral. -/
def actualPrimeIdealWindowIntegrand (W : AnnularProfile) (X : ℝ) (s : ℂ) : ℂ :=
  mellin W.function s * actualPrimeLogFunction K 1 s * (X : ℂ) ^ s

/-- Absolute convergence on the initial line identifies the actual sum,
including every prime-power coefficient and its finite annular support. -/
theorem actualPrimeIdealWindow_initial (W : AnnularProfile) (X : ℝ) (hX : 0 < X) :
    comparisonVerticalIntegral 2 (actualPrimeIdealWindowIntegrand K W X) =
      actualAnnularPrimePowerSum K 1 W X 0 := by
  have hsum : Summable (fun np : ActualPrimeLogIndex K =>
      ‖actualPrimeLogCoefficient K 1 np‖ *
        actualPrimePowerNorm K np ^ (-((0 : ℂ).re + 2))) := by
    simpa only [Complex.zero_re, zero_add] using
      actualPrimeLog_absolutelySummable K 1 (σ := 2) (by norm_num)
  have hline : ∀ t, actualPrimeLogFunction K 1 (0 + vertical 2 t) =
      ExpansionInterfaces.Mellin.dirichletSeries (actualPrimeLogCoefficient K 1)
        (actualPrimePowerNorm K) (0 + vertical 2 t) := by
    intro t
    exact actualPrimeLogFunction_eq_dirichletSeries K 1 (by simp)
  have hh := annular_mellin_finite_of_initial_line W
    (actualPrimeLogCoefficient K 1) (actualPrimePowerNorm K) (actualPrimePowerNorm_pos K)
    (actualPrimeLogFunction K 1) 0 2 X hX hsum hline
    (actualPrimeLogWindow K (W.upper * X))
    (mem_actualPrimeLogWindow_of_le K (W.upper * X))
  have hc : (2 * (Real.pi : ℂ))⁻¹ = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [comparisonVerticalIntegral, actualPrimeIdealWindowIntegrand, hc,
    actualAnnularPrimePowerSum, vertical, Complex.ofReal_zero, zero_mul,
    zero_add] using hh

theorem actualPrimeIdealWindow_differentiable (W : AnnularProfile)
    (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ (actualPrimeIdealWindowIntegrand K W X)
      (comparisonClosedStrip (63 / 64) 2 \ {1}) := by
  have hF : DifferentiableOn ℂ (actualPrimeLogFunction K 1)
      (comparisonClosedStrip (63 / 64) 2 \ {1}) := by
    apply (actualZetaLog_differentiableOn K).mono
    intro s hs
    refine ⟨?_, hs.2⟩
    change (31 / 32 : ℝ) < s.re
    exact lt_of_lt_of_le (by norm_num) hs.1.1
  have hpower : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (W.mellin_differentiable.differentiableOn.mul hF).mul hpower.differentiableOn

/-- The simple pole has its actual residue, with the original smoothing
mass and the physical scale factor. -/
theorem actualPrimeIdealWindow_residue (W : AnnularProfile)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun s : ℂ => (s - 1) * actualPrimeIdealWindowIntegrand K W X s)
      (𝓝[≠] 1) (𝓝 ((X : ℂ) * mellin W.function 1)) := by
  have hM : Tendsto (mellin W.function) (𝓝[≠] (1 : ℂ))
      (𝓝 (mellin W.function 1)) :=
    W.mellin_differentiable.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpower : Tendsto (fun s : ℂ => (X : ℂ) ^ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (X : ℂ)) := by
    simpa only [Complex.cpow_one] using
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hX.ne')
        (b := (1 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have hprod := ((actualZetaLog_residue K).mul hM).mul hpower
  have he : (fun s : ℂ => (s - 1) * actualPrimeIdealWindowIntegrand K W X s) =
      fun s => ((s - 1) * actualPrimeLogFunction K 1 s) *
        mellin W.function s * (X : ℂ) ^ s := by
    funext s
    unfold actualPrimeIdealWindowIntegrand
    ring
  rw [he]
  simpa only [one_mul, mul_comm] using hprod

/-- A polynomially growing factor times the fixed Mellin decay has a
uniform integrable majorant. -/
theorem primeWindow_product_le_decay {u v C D t : ℝ} (m : ℕ)
    (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hu : u ≤ C * (1 + |t|) ^ m)
    (hdecay : (1 + |t|) ^ (m + 2) * v ≤ D) :
    v * u ≤ (C * D) * (1 + |t|) ^ (-2 : ℝ) := by
  have ht : 0 < 1 + |t| := by positivity
  have hweighted : (1 + |t|) ^ m * v ≤ D / (1 + |t|) ^ 2 := by
    apply (le_div_iff₀ (pow_pos ht 2)).mpr
    calc
      _ = (1 + |t|) ^ (m + 2) * v := by rw [pow_add]; ring
      _ ≤ D := hdecay
  calc
    v * u ≤ v * (C * (1 + |t|) ^ m) := mul_le_mul_of_nonneg_left hu hv
    _ = C * ((1 + |t|) ^ m * v) := by ring
    _ ≤ C * (D / (1 + |t|) ^ 2) := mul_le_mul_of_nonneg_left hweighted hC
    _ = (C * D) * (1 + |t|) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht.le, Real.rpow_two]
      ring

theorem actualZetaLog_left_bound (C : ℝ) (m : ℕ)
    (hbound : ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ,
      ‖(vertical σ t - 1) * actualPrimeLogFunction K 1 (vertical σ t)‖ ≤
        C * (1 + |t|) ^ m) (t : ℝ) :
    ‖actualPrimeLogFunction K 1 (vertical (63 / 64) t)‖ ≤
      (64 * C) * (1 + |t|) ^ m := by
  have hden : (1 / 64 : ℝ) ≤ ‖vertical (63 / 64) t - 1‖ := by
    have hh := Complex.abs_re_le_norm (vertical (63 / 64) t - 1)
    norm_num only [Complex.sub_re, vertical_re, Complex.one_re] at hh
    exact hh
  have hh := hbound (63 / 64) ⟨le_rfl, by norm_num⟩ t
  rw [norm_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hden
    (norm_nonneg (actualPrimeLogFunction K 1 (vertical (63 / 64) t)))
  nlinarith

theorem actualZetaLog_strip_bound (C : ℝ) (m : ℕ)
    (hbound : ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ,
      ‖(vertical σ t - 1) * actualPrimeLogFunction K 1 (vertical σ t)‖ ≤
        C * (1 + |t|) ^ m)
    (σ : ℝ) (hσ : σ ∈ Icc (63 / 64 : ℝ) 2) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖actualPrimeLogFunction K 1 (vertical σ t)‖ ≤ C * (1 + |t|) ^ m := by
  have hden : 1 ≤ ‖vertical σ t - 1‖ := by
    have hh := Complex.abs_im_le_norm (vertical σ t - 1)
    simp only [Complex.sub_im, vertical_im, Complex.one_im, sub_zero] at hh
    exact ht.trans hh
  have hh := hbound σ hσ t
  rw [norm_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hden
    (norm_nonneg (actualPrimeLogFunction K 1 (vertical σ t)))
  have hle : ‖actualPrimeLogFunction K 1 (vertical σ t)‖ ≤
      ‖vertical σ t - 1‖ * ‖actualPrimeLogFunction K 1 (vertical σ t)‖ := by
    simpa only [one_mul] using hm
  exact hle.trans hh

/-- The contour conversion uses only the actual pole data and a primitive
polynomial strip bound, together with a Mellin seminorm. -/
theorem actualPrimeIdealWindow_contour_error (W : AnnularProfile)
    (X C D : ℝ) (m : ℕ) (hX : 1 ≤ X) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ,
      ‖(vertical σ t - 1) * actualPrimeLogFunction K 1 (vertical σ t)‖ ≤
        C * (1 + |t|) ^ m)
    (hW : ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ,
      (1 + |t|) ^ (m + 2) * ‖mellin W.function (vertical σ t)‖ ≤ D) :
    ‖actualAnnularPrimePowerSum K 1 W X 0 - (X : ℂ) * mellin W.function 1‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * (64 * C * D) *
        (∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ))) * X ^ (63 / 64 : ℝ) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  let f := actualPrimeIdealWindowIntegrand K W X
  have hdiff : DifferentiableOn ℂ f (comparisonClosedStrip (63 / 64) 2 \ {1}) :=
    actualPrimeIdealWindow_differentiable K W X hXpos
  have hleft : ∀ t : ℝ, ‖f (vertical (63 / 64) t)‖ ≤
      (64 * C * D * X ^ (63 / 64 : ℝ)) * (1 + |t|) ^ (-2 : ℝ) := by
    intro t
    have hh := primeWindow_product_le_decay m (by positivity : 0 ≤ 64 * C)
      (norm_nonneg (mellin W.function (vertical (63 / 64) t)))
      (actualZetaLog_left_bound K C m hF t)
      (hW (63 / 64) ⟨le_rfl, by norm_num⟩ t)
    calc
      _ = (‖mellin W.function (vertical (63 / 64) t)‖ *
          ‖actualPrimeLogFunction K 1 (vertical (63 / 64) t)‖) *
            X ^ (63 / 64 : ℝ) := by
        simp only [f, actualPrimeIdealWindowIntegrand, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hXpos, vertical_re]
      _ ≤ ((64 * C) * D * (1 + |t|) ^ (-2 : ℝ)) * X ^ (63 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hXpos.le _)
      _ = _ := by ring
  have htail : ∀ σ ∈ Icc (63 / 64 : ℝ) 2, ∀ t : ℝ, 1 ≤ |t| →
      ‖f (vertical σ t)‖ ≤ (C * D * X ^ (2 : ℝ)) * (1 + |t|) ^ (-2 : ℝ) := by
    intro σ hσ t ht
    have hh := primeWindow_product_le_decay m hC
      (norm_nonneg (mellin W.function (vertical σ t)))
      (actualZetaLog_strip_bound K C m hF σ hσ t ht) (hW σ hσ t)
    have hpower : X ^ σ ≤ X ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX hσ.2
    calc
      _ = (‖mellin W.function (vertical σ t)‖ *
          ‖actualPrimeLogFunction K 1 (vertical σ t)‖) * X ^ σ := by
        simp only [f, actualPrimeIdealWindowIntegrand, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hXpos, vertical_re]
      _ ≤ (C * D * (1 + |t|) ^ (-2 : ℝ)) * X ^ σ :=
        mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hXpos.le _)
      _ ≤ (C * D * (1 + |t|) ^ (-2 : ℝ)) * X ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  have hshift := verticalIntegral_sub_eq_residue_of_decay
    (a := (63 / 64 : ℝ)) (b := 2) (p := (1 : ℂ)) (f := f)
    (by norm_num) (by norm_num) hdiff
    (actualPrimeIdealWindow_residue K W X hXpos) (C * D * X ^ (2 : ℝ)) 1 htail
  have hinitial := actualPrimeIdealWindow_initial K W X hXpos
  change comparisonVerticalIntegral 2 f = actualAnnularPrimePowerSum K 1 W X 0 at hinitial
  rw [hinitial] at hshift
  have he : actualAnnularPrimePowerSum K 1 W X 0 -
      (X : ℂ) * mellin W.function 1 = comparisonVerticalIntegral (63 / 64) f := by
    linear_combination hshift
  rw [he]
  have hcont : Continuous (fun t : ℝ => f (vertical (63 / 64) t)) := by
    refine hdiff.continuousOn.comp_continuous (by unfold vertical; fun_prop) ?_
    intro t
    refine ⟨⟨by simp only [vertical_re, le_refl], by simp only [vertical_re]; norm_num⟩, ?_⟩
    intro hh
    have hr := congrArg Complex.re hh
    norm_num only [vertical_re, Complex.one_re] at hr
  have hint : Integrable (fun t : ℝ => f (vertical (63 / 64) t)) :=
    integrable_vertical_of_decay f (63 / 64) (64 * C * D * X ^ (63 / 64 : ℝ))
      0 hcont (fun t _ => hleft t)
  have hmajor : Integrable (fun t : ℝ =>
      (64 * C * D * X ^ (63 / 64 : ℝ)) * (1 + |t|) ^ (-2 : ℝ)) :=
    AnnularProfile.decayWeight_integrable.const_mul _
  unfold comparisonVerticalIntegral
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ * (∫ t : ℝ, ‖f (vertical (63 / 64) t)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        (∫ t : ℝ, (64 * C * D * X ^ (63 / 64 : ℝ)) * (1 + |t|) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (integral_mono hint.norm hmajor hleft) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

/-- A single constant controls the divided prime-power error for all scales.
The polynomial strip bound and every Mellin constant precede X. -/
theorem exists_actual_primePower_window_error
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (W : AnnularProfile) (hs : Function.support W.function ⊆ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, Real.exp 4 ≤ X →
      ‖actualLogDividedPrimePowerSum K 1 W.function X -
        (X : ℂ) * mellin (PrimeCancellationLogWindow.logWindow X W.function) 1‖ ≤
          C * X ^ (63 / 64 : ℝ) := by
  obtain ⟨C, hC, m, hF⟩ := exists_actualZetaLog_poleCleared_bound K hcomplex
  obtain ⟨D, hD, hdecay⟩ :=
    uniform_logDivided_strip_decay W.function W.smooth hs (63 / 64) 2 (m + 2)
  let E : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖ * (64 * C * D) *
    (∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ))
  have hmass : 0 ≤ (∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)) :=
    integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨E, by dsimp [E]; positivity, ?_⟩
  intro X hX
  let V := logDividedAnnularProfile W.function W.smooth hs X (two_le_exp_four.trans hX)
  have hh := actualPrimeIdealWindow_contour_error K V X C D m
    (by linarith [two_le_exp_four.trans hX]) hC.le hD hF (hdecay X hX)
  simpa only [V, actualAnnularPrimePowerSum, logDividedAnnularProfile,
    actualLogDividedPrimePowerSum, smoothedTerm, vertical, Complex.ofReal_zero,
    zero_mul, zero_add, neg_zero, Complex.cpow_zero, mul_one, E] using hh

/-- Removing higher prime powers gives a theorem about the literal prime
series, with a uniform square-root error. -/
theorem exists_actual_prime_window_error
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (W : AnnularProfile) (hs : Function.support W.function ⊆ Icc (1 : ℝ) 2) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ X : ℝ, Real.exp 4 ≤ X →
      ‖primeSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X -
        (X : ℂ) * mellin (PrimeCancellationLogWindow.logWindow X W.function) 1‖ ≤
          C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X := by
  obtain ⟨C, hC, hmain⟩ := exists_actual_primePower_window_error K hcomplex W hs
  obtain ⟨B, hB, htail⟩ := exists_actual_primePower_tail_bound K W.function W.smooth hs
  refine ⟨C, B, hC, hB.le, ?_⟩
  intro X hX
  have heq := actualLogDividedPrimePowerSum_eq_prime_add_tail K 1 W.function W.smooth
    hs X (two_le_exp_four.trans hX)
  have hid : primeSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X -
      (X : ℂ) * mellin (PrimeCancellationLogWindow.logWindow X W.function) 1 =
      (actualLogDividedPrimePowerSum K 1 W.function X -
        (X : ℂ) * mellin (PrimeCancellationLogWindow.logWindow X W.function) 1) -
          tailSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X := by
    rw [heq]
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans
    (add_le_add (hmain X hX) (htail 1 X ((Real.exp_pos 4).trans_le hX)))

/-- The original envelope contains every nonzero term of the smooth prime
series; no extra ray, row or ramification deletion is introduced. -/
theorem actual_prime_window_envelope_eq (W : AnnularProfile)
    (hs : Function.support W.function ⊆ Ioo (1 : ℝ) 2) (X : ℝ) :
    (∑ p ∈ finitePrimeEnvelope K (dyadicIdealSupport K X),
      W.function ((p.asIdeal.absNorm : ℝ) / X)) =
      primeSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X := by
  symm
  unfold primeSum
  simp only [primeCoefficient_trivial, one_mul]
  apply tsum_eq_sum
  intro p hp
  by_contra hn
  have hmem := (analyticPrimeSupport_spec K W.function hs X p).mpr hn
  exact hp (Finset.mem_filter.mp hmem).1

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The fixed set S costs at most its cardinality times the original window
supremum, independent of the smoothing scale. -/
theorem actual_prime_window_deletion_bound (W : AnnularProfile)
    (hs : Function.support W.function ⊆ Ioo (1 : ℝ) 2)
    (M : ℝ) (hM : 0 ≤ M) (hW : ∀ y, ‖W.function y‖ ≤ M) (X : ℝ) :
    ‖(∑ p ∈ (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S),
        W.function ((p.asIdeal.absNorm : ℝ) / X)) -
      primeSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X‖ ≤
        (S.toFinset.card : ℝ) * M := by
  let pool := finitePrimeEnvelope K (dyadicIdealSupport K X)
  let f := fun p : HeightOneSpectrum (𝓞 K) => W.function ((p.asIdeal.absNorm : ℝ) / X)
  rw [← actual_prime_window_envelope_eq K W hs X]
  have hsplit := Finset.sum_filter_add_sum_filter_not pool (fun p => p ∈ S) f
  have he : (∑ p ∈ pool.filter (fun p => p ∉ S), f p) - ∑ p ∈ pool, f p =
      -(∑ p ∈ pool.filter (fun p => p ∈ S), f p) := by
    linear_combination hsplit
  change ‖(∑ p ∈ pool.filter (fun p => p ∉ S), f p) - ∑ p ∈ pool, f p‖ ≤ _
  rw [he, norm_neg]
  have hsub : pool.filter (fun p => p ∈ S) ⊆ S.toFinset := by
    intro p hp
    exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hp).2
  calc
    _ ≤ ∑ p ∈ pool.filter (fun p => p ∈ S), ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S.toFinset, ‖f p‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => norm_nonneg (f p))
    _ ≤ ∑ _p ∈ S.toFinset, M := Finset.sum_le_sum (fun p _ => hW _)
    _ = (S.toFinset.card : ℝ) * M := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The actual window prime ideal theorem for totally complex fields.
Every constant is fixed before the prime scale, and the finite sum is the
exact envelope used by the original normalizer. -/
theorem actual_annular_window_prime_lower
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (W : AnnularProfile) (hre : ∀ y, (W.function y).im = 0)
    (hnn : ∀ y, 0 ≤ (W.function y).re) (hne : ∃ y, W.function y ≠ 0)
    (hs : Function.support W.function ⊆ Ioo (1 : ℝ) 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S),
          (W.function ((p.asIdeal.absNorm : ℝ) / X)).re := by
  have hs' : Function.support W.function ⊆ Icc (1 : ℝ) 2 := hs.trans Ioo_subset_Icc_self
  obtain ⟨c, hc, hmass⟩ := exists_logWindow_mellin_one_lower W hre hnn hne hs
  obtain ⟨C, B, hC, hB, herr⟩ := exists_actual_prime_window_error K hcomplex W hs'
  obtain ⟨M, hM, hWin⟩ := exists_actualPrimeWindowBound W.function W.smooth hs'
  let D : ℝ := (S.toFinset.card : ℝ) * M
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (eventually_primeWindow_error_le c C B D hc hC hB hD)
  refine ⟨c / 2, max (Real.exp 4) X₀, div_pos hc (by norm_num),
    (by linarith [two_le_exp_four, le_max_left (Real.exp 4) X₀]), ?_⟩
  intro X hX
  have hXexp : Real.exp 4 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < X := (Real.exp_pos 4).trans_le hXexp
  let A : ℂ := ∑ p ∈ (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S),
    W.function ((p.asIdeal.absNorm : ℝ) / X)
  let Q : ℂ := primeSum (actualPrimeNorm K) (primeCoefficient K 1) W.function X
  let main : ℂ := (X : ℂ) * mellin (PrimeCancellationLogWindow.logWindow X W.function) 1
  have hdelete : ‖A - Q‖ ≤ D := actual_prime_window_deletion_bound K S W hs M hM.le hWin.bound X
  have htotal : ‖A - main‖ ≤ C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X + D := by
    have he : A - main = (A - Q) + (Q - main) := by ring
    rw [he]
    exact (norm_add_le _ _).trans
      ((add_le_add hdelete (herr X hXexp)).trans_eq (by ring))
  have hreal : main.re - A.re ≤ C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X + D := by
    calc
      _ = (main - A).re := (Complex.sub_re _ _).symm
      _ ≤ |(main - A).re| := le_abs_self _
      _ ≤ ‖main - A‖ := Complex.abs_re_le_norm _
      _ = ‖A - main‖ := norm_sub_rev _ _
      _ ≤ _ := htotal
  have hmain : c * X / Real.log X ≤ main.re := by
    calc
      _ = X * (c / Real.log X) := by ring
      _ ≤ X * (mellin (PrimeCancellationLogWindow.logWindow X W.function) 1).re :=
        mul_le_mul_of_nonneg_left (hmass X hXexp) hXpos.le
      _ = main.re := by simp only [main, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
  have hsmall := hX₀ X ((le_max_right _ _).trans hX)
  calc
    _ = c * X / Real.log X - (c / 2) * X / Real.log X := by ring
    _ ≤ main.re - (C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X + D) :=
      sub_le_sub hmain hsmall
    _ ≤ A.re := by linarith
    _ = _ := by simp only [A, Complex.re_sum]

/-- The original `SmoothAnnularTest` interface, without importing the
admitted normalizer window theorem. -/
theorem actual_window_prime_lower
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (w : SmoothAnnularTest) (hre : ∀ y, (w.toFun y).im = 0)
    (hnn : ∀ y, 0 ≤ (w.toFun y).re) (hne : ∃ y, w.toFun y ≠ 0)
    (hsupp : Function.support w.toFun ⊆ Ioo (1 : ℝ) 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S),
          (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re := by
  let W : AnnularProfile :=
    { function := w.toFun
      lower := w.lower
      upper := w.upper
      lower_pos := w.lower_pos
      lower_le_upper := w.upper_ge
      smooth := w.smooth
      supported := w.support }
  exact actual_annular_window_prime_lower K S hcomplex W hre hnn hne hsupp

end Expansion.Project

#print axioms Expansion.Project.actualPrimeIdealWindow_initial
#print axioms Expansion.Project.actualPrimeIdealWindow_contour_error
#print axioms Expansion.Project.exists_actual_primePower_window_error
#print axioms Expansion.Project.actual_window_prime_lower
