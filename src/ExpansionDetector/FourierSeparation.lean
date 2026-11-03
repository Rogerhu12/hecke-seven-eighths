import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Exact Fourier separation of the actual finite coefficient products.
Adapted from the supplied DetectorFourierSeparation and DetectorFourierWitness
proofs; all former FourierBridge inputs are derived below from Mathlib. -/
noncomputable section
namespace ExpansionDetector.Fourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap

def logPhase (t x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)

lemma logPhase_continuous_left (x : ℝ) : Continuous (fun t => logPhase t x) := by
  unfold logPhase
  fun_prop

@[simp] lemma logPhase_norm (t x : ℝ) : ‖logPhase t x‖ = 1 := by
  simp [logPhase, Complex.norm_exp]

lemma logPhase_add (t x y : ℝ) : logPhase t (x + y) = logPhase t x * logPhase t y := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma schwartz_log_inversion (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    g x = ∫ t : ℝ, Complex.exp (((2 * Real.pi * inner ℝ t x : ℝ) : ℂ) * Complex.I) * (𝓕 g) t := by
  have h : (𝓕⁻ ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x = g x := by
    rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
  simpa only [Real.fourierInv_eq', smul_eq_mul] using h.symm

lemma schwartz_one_plus_integrable (g : SchwartzMap ℝ ℂ) (N : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖)^N * ‖g t‖) := by
  have hi := (g.integrable.norm.add (g.integrable_pow_mul volume N)).const_mul ((2 : ℝ)^N)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with t
  have hp : (1 + ‖t‖)^N ≤ (2 : ℝ)^N * (1 + ‖t‖^N) := by
    by_cases ht : ‖t‖ ≤ 1
    · calc
        _ ≤ (2 : ℝ)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg (norm_nonneg t) N])
    · have ht' : 1 ≤ ‖t‖ := (lt_of_not_ge ht).le
      calc
        _ ≤ (2 * ‖t‖)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = (2 : ℝ)^N * ‖t‖^N := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (by dsimp only [Pi.add_apply]; ring)

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N * (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J * ‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N) * ‖(𝓕 g) t‖ := by
  have hiJ := schwartz_one_plus_integrable (𝓕 g) J
  have hiN := schwartz_one_plus_integrable (𝓕 g) (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le
    (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*logPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*logPhase t x*logPhase t y := by
  rw [schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      logPhase t x*logPhase t y := by
    rw [← logPhase_add]
    simp only [logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*logPhase t (x i))*(b j*logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*logPhase t (x i))*(b j*logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end ExpansionDetector.Fourier
