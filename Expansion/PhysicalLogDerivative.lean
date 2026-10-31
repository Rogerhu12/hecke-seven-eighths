import PrimeCancellationDiskGeometry
import ExpansionDetector.HeckeGammaDetector
import HeckeSkeleton.HeckeBufferedReciprocal

/-!
# An actual logarithmic-derivative bound inside a finite zero buffer

The fixed infinity type and conductor budget determine the constants before
any character, height, abscissa or evaluation point is chosen. Polynomial
growth and the center logarithm come from the actual Hecke providers.
Nonvanishing is proved only on the required disk, using the literal finite
upper-zero predicate. No all-height zero-free data are asserted here.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set Metric
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.HeckeUniformStripGrowth HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.ActualEulerLogarithm ExpansionDetector.Hecke
open PrimeCancellationDiskGeometry
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The critical-strip upper endpoint is already a premise in the literal
finite-height predicate. Capping its bound by one preserves the same H. -/
theorem zeroUpperBound_min_one (χ : HeckeCharacter K) (H α : ℝ)
    (hupper : ZeroUpperBound K χ H α) :
    ZeroUpperBound K χ H (min α 1) := by
  intro ρ hρ hlo hhi hheight
  exact le_min (hupper ρ hρ hlo hhi hheight) hhi

/-- A finite physical zero buffer is sufficient for a local logarithmic
 derivative estimate. The margin `3/2` is the actual outer-disk height.
 The zero boundary is explicitly restricted to `[1/2,1]`; no stronger
 zero-free statement is inferred from the finite detector. -/
theorem exists_actual_finite_height_logDeriv_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (χ : HeckeCharacter K) (U β δ σ t Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        β + δ ≤ σ → σ ≤ 2 → |t| + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖deriv (heckeContinuation K χ) (verticalPoint σ t) /
          heckeContinuation K χ (verticalPoint σ t)‖ ≤
          48 * (1 + Real.log C + (5 / 8) * Real.log U +
            heightDegree K * Real.log (4 + |t|) + A) / δ ^ 2 := by
  obtain ⟨CL, hCL, hstrip⟩ :=
    exists_actual_detector_strip_bound K hcomplex arch weight R hR
  obtain ⟨Cr, hCr, hright⟩ :=
    exists_uniform_rightHalfPlane_bound K (9 / 8) (by norm_num)
  obtain ⟨A, hA, hlog⟩ := exists_uniform_heckeEulerLog_bound K
  let C : ℝ := max 1 (max CL Cr)
  have hC : 1 ≤ C := le_max_left _ _
  have hCL' : CL ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCr' : Cr ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, A, hC, hA, ?_⟩
  intro χ U β δ σ t Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hσ hσ'
    hpadding hupper
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hdegree : 0 ≤ heightDegree K := by unfold heightDegree; positivity
  have hT : 1 ≤ 4 + |t| := by linarith [abs_nonneg t]
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hlogT : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg hT
  let M : ℝ := 1 + Real.log C + (5 / 8) * Real.log U +
    heightDegree K * Real.log (4 + |t|)
  have hM : 0 < M := by dsimp [M]; positivity
  have h0 : ∀ w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2),
      heckeContinuation K χ w ≠ 0 := by
    intro w hw
    apply continuation_ne_zero_of_upper K χ hχ Hupper β hβ hupper w
    · have hre := outer_ball_re_lower hw
      linarith
    · exact (outer_ball_im_bound hβ hδ hw).trans hpadding
  have hexp : C * U ^ (5 / 8 : ℝ) * (4 + |t|) ^ heightDegree K ≤ Real.exp M := by
    simpa only [M, heightDegree, Real.rpow_natCast] using
      (polynomial_le_exp_log_bound (p := (5 / 8 : ℝ))
        (2 * Fintype.card (InfinitePlace K)) hC hU hT)
  have hb : ∀ w ∈ ball (verticalPoint 2 t) (2 - β - δ / 2),
      ‖heckeContinuation K χ w‖ ≤ Real.exp M := by
    intro w hw
    have hre := outer_ball_re_lower hw
    have him := outer_ball_im_bound hβ hδ hw
    have hheight : 2 + |w.im| ≤ 4 + |t| := by linarith
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 + |w.im|)
      hheight hdegree
    refine le_trans ?_ hexp
    by_cases hleft : w.re ≤ 3
    · calc
        _ ≤ CL * U ^ (5 / 8 : ℝ) * (2 + |w.im|) ^ heightDegree K :=
          hstrip χ U hχ harch hweight hU hQ w (by linarith) hleft
        _ ≤ C * U ^ (5 / 8 : ℝ) * (4 + |t|) ^ heightDegree K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCL' (Real.rpow_nonneg hU0 _)) hpow
            (Real.rpow_nonneg (by positivity) _) (mul_nonneg hC0 (Real.rpow_nonneg hU0 _))
    · have hfactor : 1 ≤ U ^ (5 / 8 : ℝ) * (4 + |t|) ^ heightDegree K :=
        one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hU (by norm_num))
          (Real.one_le_rpow hT hdegree)
      calc
        _ ≤ Cr := hright χ w (by linarith)
        _ ≤ C := hCr'
        _ ≤ C * (U ^ (5 / 8 : ℝ) * (4 + |t|) ^ heightDegree K) :=
          le_mul_of_one_le_right hC0 hfactor
        _ = C * U ^ (5 / 8 : ℝ) * (4 + |t|) ^ heightDegree K := (mul_assoc _ _ _).symm
  have hm := exp_heckeEulerLog_eq_continuation K χ (verticalPoint 2 t) (by norm_num)
  have hmA := hlog χ (verticalPoint 2 t) (by norm_num)
  simpa only [M] using
    (PrimeCancellationLogDerivative.norm_logDeriv_le_on_bufferedDisk hβ hβ' hδ hδ'
      hM (differentiable_heckeContinuation_of_nonNorm K χ hχ).differentiableOn
      h0 hm hmA hb (verticalPoint_mem_inner hσ hσ'))

end Expansion.Project

#print axioms Expansion.Project.zeroUpperBound_min_one
#print axioms Expansion.Project.exists_actual_finite_height_logDeriv_bound
