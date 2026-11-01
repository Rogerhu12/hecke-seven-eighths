import Expansion.SmoothDyadicPartition
import HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation
import HeckeSkeleton.Moments.MOM_INV_STEP.IntegralEnergy

/-!
# One actual smooth prefix for every smaller inverse scale

The finite polynomial below retains its original coefficients.  Fourier
inversion moves the smaller scale into a norm-one phase, while one smooth
prefix, fixed before that scale, retains every nonzero original summand.
The positive integral majorant is therefore the same for all smaller
scales of a row.  It is a genuine integrable finite polynomial, not a
supremum of separately chosen moment estimates.

The prefix has an exact finite decomposition into the fixed smooth dyadic
annulus.  These are the row-independent tests to which the zero-slot
canonical estimate is applied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSup

open MeasureTheory
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.Moments.MOMInvStep
open CommonKernel MellinSeparation
open scoped Classical BigOperators FourierTransform

variable {ι κ : Type*}

def prefixColumn (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ T, a i * columnPhase t (Real.log (N i)) *
    (Expansion.Dyadic.cutoff (N i / (2 : ℝ) ^ L) : ℂ)

def annularColumn (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (j : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ T, a i * columnPhase t (Real.log (N i)) *
    Expansion.Dyadic.annularProfile (N i / (2 : ℝ) ^ j)

theorem prefixColumn_continuous (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) : Continuous (prefixColumn T a N L) := by
  unfold prefixColumn
  apply continuous_finsetSum
  intro i hi
  exact (continuous_const.mul (continuous_columnPhase _)).mul continuous_const

theorem prefixColumn_norm_le (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) (t : ℝ) : ‖prefixColumn T a N L t‖ ≤ ∑ i ∈ T, ‖a i‖ := by
  unfold prefixColumn
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, norm_mul, norm_columnPhase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Expansion.Dyadic.cutoff_range _).1]
  exact mul_le_of_le_one_right (norm_nonneg _) (Expansion.Dyadic.cutoff_range _).2

/-- This equality retains the literal finite ideal coefficients, including
their zero masks.  The lower bound one is the integral-ideal norm bound. -/
theorem prefixColumn_eq_annular_sum (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i ∈ T, 1 ≤ N i) (L : ℕ) (t : ℝ) :
    prefixColumn T a N L t =
      ∑ j ∈ Finset.range (L + 1), annularColumn T a N j t := by
  unfold prefixColumn annularColumn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum]
  congr 1
  have h := congrArg Complex.ofReal (Expansion.Dyadic.sum_annular_telescope (N i) L)
  rw [Expansion.Dyadic.cutoff_zero (x := 2 * N i) (by linarith [hN i hi]), sub_zero] at h
  simpa only [Expansion.Dyadic.annularProfile, Complex.ofReal_sum] using h.symm

/-- The cost of the finite scale decomposition is its actual number of
dyadic blocks, which will be absorbed before the source is selected. -/
theorem prefixColumn_sq_le (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i ∈ T, 1 ≤ N i) (L : ℕ) (t : ℝ) :
    ‖prefixColumn T a N L t‖ ^ 2 ≤
      (L + 1 : ℕ) * ∑ j ∈ Finset.range (L + 1), ‖annularColumn T a N j t‖ ^ 2 := by
  rw [prefixColumn_eq_annular_sum T a N hN L t]
  calc
    _ ≤ (∑ j ∈ Finset.range (L + 1), ‖annularColumn T a N j t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.range (L + 1)).card : ℝ) *
        ∑ j ∈ Finset.range (L + 1), ‖annularColumn T a N j t‖ ^ 2 :=
      _root_.sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [Finset.card_range]

set_option maxHeartbeats 1600000 in
/-- Fourier inversion for the entire finite polynomial uses one density.
Its translation parameter has become a single common unit phase. -/
theorem finite_shifted_fourier (T : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (F : SchwartzMap ℝ ℂ) (v : ℝ) :
    (∑ i ∈ T, a i * F (x i - v)) =
      ∫ t : ℝ, (𝓕 F) t * columnPhase t (-v) *
        ∑ i ∈ T, a i * columnPhase t (x i) := by
  symm
  calc
    _ = ∫ t : ℝ, ∑ i ∈ T, a i * ((𝓕 F) t * columnPhase t (x i - v)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [sub_eq_add_neg, MellinWeightedTests.columnPhase_add]
        ring
    _ = ∑ i ∈ T, ∫ t : ℝ, a i * ((𝓕 F) t * columnPhase t (x i - v)) := by
      have hi (i : ι) : Integrable
          (fun t : ℝ => a i * ((𝓕 F) t * columnPhase t (x i - v))) :=
        (integrable_inverse F (x i - v)).const_mul (a i)
      exact integral_finsetSum T (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, ← fourier_inverse]

/-- A single fixed prefix keeps every original nonzero summand for each
permitted smaller scale.  No uniform-energy hypothesis occurs here. -/
theorem shifted_profile_eq_prefix_integral (T : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) (F : SchwartzMap ℝ ℂ) (L : ℕ) (D : ℝ)
    (hkeep : ∀ i ∈ T, F (Real.log (N i) - Real.log D) ≠ 0 →
      N i ≤ (2 : ℝ) ^ L) :
    (∑ i ∈ T, a i * F (Real.log (N i) - Real.log D)) =
      ∫ t : ℝ, (𝓕 F) t * columnPhase t (-Real.log D) * prefixColumn T a N L t := by
  have hsource : (∑ i ∈ T, a i * F (Real.log (N i) - Real.log D)) =
      ∑ i ∈ T, (a i * (Expansion.Dyadic.cutoff (N i / (2 : ℝ) ^ L) : ℂ)) *
        F (Real.log (N i) - Real.log D) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hF : F (Real.log (N i) - Real.log D) = 0
    · simp only [hF, mul_zero]
    · rw [Expansion.Dyadic.cutoff_one
        ((div_le_one (by positivity)).mpr (hkeep i hi hF)), Complex.ofReal_one, mul_one]
  rw [hsource, finite_shifted_fourier]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change (𝓕 F) t * columnPhase t (-Real.log D) *
        (∑ i ∈ T, a i * (Expansion.Dyadic.cutoff (N i / (2 : ℝ) ^ L) : ℂ) *
          columnPhase t (Real.log (N i))) =
      (𝓕 F) t * columnPhase t (-Real.log D) *
        (∑ i ∈ T, a i * columnPhase t (Real.log (N i)) *
          (Expansion.Dyadic.cutoff (N i / (2 : ℝ) ^ L) : ℂ))
    simp only [mul_assoc, mul_left_comm, mul_comm]

theorem prefix_energy_integrable (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) (W : ℝ → ℝ) (hW : Integrable W) :
    Integrable (fun t : ℝ => W t * ‖prefixColumn T a N L t‖ ^ 2) := by
  apply hW.mul_bdd (c := (∑ i ∈ T, ‖a i‖) ^ 2)
    ((prefixColumn_continuous T a N L).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    change ‖‖prefixColumn T a N L t‖ ^ 2‖ ≤ (∑ i ∈ T, ‖a i‖) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (prefixColumn_norm_le T a N L t) 2

def rowMajorant (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) (W : ℝ → ℝ) : ℝ :=
  (∫ t : ℝ, W t) * ∫ t : ℝ, W t * ‖prefixColumn T a N L t‖ ^ 2

theorem rowMajorant_nonneg (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (L : ℕ) (W : ℝ → ℝ) (hW : ∀ t, 0 ≤ W t) :
    0 ≤ rowMajorant T a N L W :=
  mul_nonneg (integral_nonneg hW)
    (integral_nonneg (fun t => mul_nonneg (hW t) (sq_nonneg _)))

/-- The same positive row majorant bounds every smaller scale retained by
the prefix, even when the original Schwartz profile varies by row. -/
theorem shifted_profile_sq_le (T : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (F : SchwartzMap ℝ ℂ) (L : ℕ) (D : ℝ)
    (hkeep : ∀ i ∈ T, F (Real.log (N i) - Real.log D) ≠ 0 →
      N i ≤ (2 : ℝ) ^ L)
    (W : ℝ → ℝ) (hW0 : ∀ t, 0 ≤ W t) (cW : Continuous W) (iW : Integrable W)
    (hF : ∀ t, ‖(𝓕 F) t‖ ≤ W t) :
    ‖∑ i ∈ T, a i * F (Real.log (N i) - Real.log D)‖ ^ 2 ≤
      rowMajorant T a N L W := by
  rw [shifted_profile_eq_prefix_integral T a N F L D hkeep]
  have hi := prefix_energy_integrable T a N L W iW
  have hb := IntegralEnergy.weighted_integral_cauchy volume W (fun _ => 1)
    (fun t => ‖prefixColumn T a N L t‖ ^ 2)
    (fun t => (𝓕 F) t * columnPhase t (-Real.log D) * prefixColumn T a N L t)
    hW0 (fun _ => zero_le_one) (fun _ => sq_nonneg _) cW continuous_const
    ((prefixColumn_continuous T a N L).norm.pow 2)
    (by simpa only [mul_one] using iW) hi (by
      intro t
      simp only [norm_mul, norm_columnPhase, mul_one, Real.sqrt_one,
        Real.sqrt_sq (norm_nonneg _), one_mul]
      exact mul_le_mul_of_nonneg_right (hF t) (norm_nonneg _))
  have hm : 0 ≤ ∫ t : ℝ, W t := integral_nonneg hW0
  have he : 0 ≤ ∫ t : ℝ, W t * ‖prefixColumn T a N L t‖ ^ 2 :=
    integral_nonneg (fun t => mul_nonneg (hW0 t) (sq_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [rowMajorant, mul_one, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt he] using hs

/-- Summation over complete rows commutes with the same positive
frequency integral.  No additional row count is introduced. -/
theorem sum_rowMajorant (R : Finset κ) (T : Finset ι) (a : κ → ι → ℂ)
    (N : ι → ℝ) (L : ℕ) (W : ℝ → ℝ) (iW : Integrable W) :
    (∑ u ∈ R, rowMajorant T (a u) N L W) =
      (∫ t : ℝ, W t) * ∫ t : ℝ, W t * ∑ u ∈ R, ‖prefixColumn T (a u) N L t‖ ^ 2 := by
  simp only [rowMajorant, ← Finset.mul_sum]
  congr 1
  rw [show (fun t : ℝ => W t * ∑ u ∈ R, ‖prefixColumn T (a u) N L t‖ ^ 2) =
      (fun t : ℝ => ∑ u ∈ R, W t * ‖prefixColumn T (a u) N L t‖ ^ 2) by
        funext t; rw [Finset.mul_sum]]
  exact (integral_finset_sum R (fun u hu => prefix_energy_integrable T (a u) N L W iW)).symm

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSup

end
