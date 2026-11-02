import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryPowerWindows
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionSmooth

/-!
# The actual finite ordinary reflection operator

Each retained annular piece of the reflected ideal sum is expressed as
one genuine common-frequency integral of the actual power-window column.
The square-root normalization is exact, including scales below one.
Finite summation and integration are exchanged only after proving L1 of
every term.  Coefficients remain arbitrary explicit functions, so inserting
the original Hecke character and complete common mask is literal.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology

private theorem normalized_power_ratio {N Y q : ℝ}
    (hN : 0 < N) (hY : 0 < Y) (hq : 0 < q) (s : ℂ) :
    (Real.sqrt Y : ℂ)⁻¹ * ((q / Y : ℝ) : ℂ) ^ (s - 1) =
      ((N / Y : ℝ) : ℂ) ^ (s - (1 / 2 : ℂ)) *
        (Real.sqrt N : ℂ)⁻¹ * ((q / N : ℝ) : ℂ) ^ (s - 1) := by
  have hr : 0 < N / Y := div_pos hN hY
  have hrootN : (Real.sqrt N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hrootY : (Real.sqrt Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hY).ne'
  have hsqrt : ((N / Y : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt N : ℂ) / (Real.sqrt Y : ℂ) := by
    have hh : ((N / Y : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (N / Y) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
      norm_num
    rw [hh, Real.sqrt_div hN.le, Complex.ofReal_div]
  have hscale : q / Y = (N / Y) * (q / N) := by field_simp [hN.ne', hY.ne']
  rw [show s - (1 / 2 : ℂ) = (s - 1) + (1 / 2 : ℂ) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'), hsqrt,
    hscale, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (div_pos hq hN).le]
  field_simp [hrootN, hrootY]
  <;> ring

variable (K : Type) [Field K] [NumberField K]

/-- A finite, explicit norm majorant for a frequency column.  It is
independent of the unbounded Fourier variable. -/
def ordinaryPowerColumnMajorant (a : NonzeroIdeal K → ℂ) (σ N : ℝ) : ℝ :=
  (Real.sqrt N)⁻¹ * ∑ I ∈ ordinaryPowerWindowSupport K N,
    ‖a I‖ * fixedDyadicWeight (idealNorm K I / N) * (idealNorm K I / N) ^ (σ - 1)

theorem ordinaryPowerColumn_norm_le (a : NonzeroIdeal K → ℂ)
    (σ t : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖ordinaryPowerColumn K a σ N t‖ ≤ ordinaryPowerColumnMajorant K a σ N := by
  unfold ordinaryPowerColumn ordinaryPowerColumnMajorant
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  rw [norm_mul, ordinaryPowerWindow_norm σ t (div_pos (idealNorm_pos K I) hN)]
  ring

theorem continuous_ordinaryPowerColumn (a : NonzeroIdeal K → ℂ) (σ N : ℝ) :
    Continuous (ordinaryPowerColumn K a σ N) := by
  unfold ordinaryPowerColumn
  exact continuous_const.mul (continuous_finset_sum _ (fun I _ =>
    continuous_const.mul (continuous_ordinaryPowerWindow_frequency σ _)))

/-- Absolute convergence of the original-frequency operator is obtained
from the genuine Mellin density and the finite actual column majorant. -/
theorem integrable_ordinaryWindowOperator
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a : NonzeroIdeal K → ℂ) {δ σ N Y : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) (hN : 0 < N) (hY : 0 < Y) :
    Integrable (fun t : ℝ => ordinaryMellinGamma K χ V σ t *
      ((N / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - (1 / 2 : ℂ)) *
        ordinaryPowerColumn K a σ N t) := by
  have hr : 0 < N / Y := div_pos hN hY
  have hc : Continuous (fun t : ℝ => ordinaryMellinGamma K χ V σ t *
      ((N / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - (1 / 2 : ℂ)) *
        ordinaryPowerColumn K a σ N t) :=
    ((continuous_ordinaryMellinGamma K χ V (by linarith [hσ.2])).mul
      (((differentiable_id.sub_const (1 / 2 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))).continuous.comp
          (continuous_idealVerticalPoint σ))).mul
      (continuous_ordinaryPowerColumn K a σ N)
  apply ((integrable_ordinaryMellinGamma K hcomplex χ V hδ hσ).norm.mul_const
    ((N / Y) ^ (σ - 1 / 2) * ordinaryPowerColumnMajorant K a σ N)).mono'
      hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
    show (idealVerticalPoint σ t - (1 / 2 : ℂ)).re = σ - 1 / 2 by
      simp [idealVerticalPoint]]
  exact (mul_le_mul_of_nonneg_left (ordinaryPowerColumn_norm_le K a σ t hN)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hr.le _))).trans_eq (by ring)

/-- The common-frequency formula for the exact normalized annular piece.
The finite support on the left is the original smooth cutoff support. -/
theorem ordinaryReflectedWindow_operator
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a : NonzeroIdeal K → ℂ) {δ σ N Y : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) (hN : 0 < N) (hY : 0 < Y) :
    (Real.sqrt Y : ℂ)⁻¹ *
        ∑ I ∈ ordinaryPowerWindowSupport K N,
          a I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
            (fixedDyadicWeight (idealNorm K I / N) : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        ordinaryMellinGamma K χ V σ t *
          ((N / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - (1 / 2 : ℂ)) *
            ordinaryPowerColumn K a σ N t := by
  let f (I : NonzeroIdeal K) (t : ℝ) : ℂ :=
    ((Real.sqrt Y : ℂ)⁻¹ * a I * (fixedDyadicWeight (idealNorm K I / N) : ℂ)) *
      (ordinaryMellinGamma K χ V σ t *
        ((idealNorm K I / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - 1))
  have hint (I : NonzeroIdeal K) : Integrable (f I) :=
    (integrable_ordinaryMellinGamma_ratio K hcomplex χ V hδ hσ
      (div_pos (idealNorm_pos K I) hY)).const_mul _
  have hpoint (t : ℝ) :
      (∑ I ∈ ordinaryPowerWindowSupport K N, f I t) =
        ordinaryMellinGamma K χ V σ t *
          ((N / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - (1 / 2 : ℂ)) *
            ordinaryPowerColumn K a σ N t := by
    simp only [ordinaryPowerColumn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    rw [ordinaryPowerWindow_eq_cpow σ t (div_pos (idealNorm_pos K I) hN)]
    have hscale := normalized_power_ratio hN hY (idealNorm_pos K I)
      (idealVerticalPoint σ t)
    calc
      f I t = (a I * (fixedDyadicWeight (idealNorm K I / N) : ℂ) *
          ordinaryMellinGamma K χ V σ t) *
            ((Real.sqrt Y : ℂ)⁻¹ *
              ((idealNorm K I / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - 1)) := by
        dsimp [f]
        ring
      _ = _ := by rw [hscale]; ring
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∑ I ∈ ordinaryPowerWindowSupport K N, ∫ t : ℝ, f I t := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [ordinaryReflectedProfile_eq_line K hcomplex χ V hδ hσ
        (div_pos (idealNorm_pos K I) hY)]
      dsimp [f]
      rw [integral_const_mul]
      ring
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, ∑ I ∈ ordinaryPowerWindowSupport K N, f I t := by
      rw [integral_finset_sum _ (fun I _ => hint I)]
    _ = _ := by simp_rw [hpoint]

/-- The same operator acts on the genuine smooth reflected window test,
with its literal finite support rather than an assumed model column. -/
theorem annularReflectedWindow_operator
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a : NonzeroIdeal K → ℂ) {δ σ N Y : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) (hN : 0 < N) (hY : 0 < Y) :
    (Real.sqrt Y : ℂ)⁻¹ * annularIdealSum K a
        (ordinaryReflectedWindowTest K hcomplex χ V hδ (div_pos hN hY)) N =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        ordinaryMellinGamma K χ V σ t *
          ((N / Y : ℝ) : ℂ) ^ (idealVerticalPoint σ t - (1 / 2 : ℂ)) *
            ordinaryPowerColumn K a σ N t := by
  have he : annularIdealSum K a
      (ordinaryReflectedWindowTest K hcomplex χ V hδ (div_pos hN hY)) N =
        ∑ I ∈ ordinaryPowerWindowSupport K N,
          a I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
            (fixedDyadicWeight (idealNorm K I / N) : ℂ) := by
    rw [annularIdealSum_eq_tsum K a _ hN]
    have hterm (I : NonzeroIdeal K) :
        a I * (ordinaryReflectedWindowTest K hcomplex χ V hδ
          (div_pos hN hY)).toFun (idealNorm K I / N) =
          a I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y) *
            (fixedDyadicWeight (idealNorm K I / N) : ℂ) := by
      change a I * ordinaryReflectedWindow K χ V δ (N / Y) (idealNorm K I / N) = _
      rw [ordinaryReflectedWindow_calibration K χ V δ N Y hN.ne']
      ring
    simp_rw [hterm]
    apply tsum_eq_sum
    intro I hI
    have hz : fixedDyadicWeight (idealNorm K I / N) = 0 := by
      by_contra hn
      exact hI ((mem_ordinaryPowerWindowSupport K σ 0 N I).2
        ((ordinaryPowerWindow_ne_zero_iff σ 0 _).2 hn))
    rw [hz, Complex.ofReal_zero, mul_zero]
  rw [he]
  exact ordinaryReflectedWindow_operator K hcomplex χ V a hδ hσ hN hY

end HeckeSkeleton.Moments.EngineInduction
