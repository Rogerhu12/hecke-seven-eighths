import Expansion.ActualPrimeLogSeries
import Expansion.PhysicalLogDerivative
import ExpansionInterfaces.AnnularContourUniform
import ExpansionInterfaces.AnnularContourDataBound

/-!
# A finite contour bound for the actual annular prime-power polynomial

The coefficients, norms, finite support and initial-line calibration are the
actual Hecke prime-power data.  The finite zero buffer supplies nonvanishing
only on the rectangle that is used.  The estimate retains both horizontal
faces and the complementary initial-line tail.  The profile constant is
chosen before the character, frequency, scale and rectangle height.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionDetector.Hecke
open ExpansionInterfaces.Mellin
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The literal logarithmically weighted prime-power sum on a fixed annulus. -/
def actualAnnularPrimePowerSum (χ : HeckeCharacter K) (W : AnnularProfile)
    (X ν : ℝ) : ℂ :=
  ∑ np ∈ actualPrimeLogWindow K (W.upper * X),
    smoothedTerm W (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K)
      (vertical 0 ν) X np

/-- One rectangle envelope, with the character dependence confined to U. -/
def actualPrimeLogRectangleBound (C A U δ ν H : ℝ) : ℝ :=
  48 * (1 + Real.log C + (5 / 8) * Real.log U +
    heightDegree K * Real.log (4 + |ν| + H) + A) / δ ^ 2

/-- A finite-height estimate with explicit left-face, horizontal-face and
initial-tail terms. This theorem concerns the actual logarithmically weighted
prime-power polynomial; it does not assume an all-height zero-free region. -/
theorem exists_actual_primePower_bound_of_contour_data
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (χ : HeckeCharacter K) (W : AnnularProfile) (order : ℕ) (CW : ℝ), 0 ≤ CW →
        (∀ σ ∈ Icc (1 / 2 : ℝ) 2,
          (∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) ≤ CW ∧
          (∀ t : ℝ, (1 + |t|) ^ order * ‖mellin W.function (vertical σ t)‖ ≤ CW) ∧
          ∀ H : ℝ, 0 < H →
            (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical σ t)‖) ≤ CW / H ^ order) →
        ∀ (U β δ ν H X Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → 1 ≤ X → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        let M := actualPrimeLogRectangleBound K C A U δ ν H
        ‖actualAnnularPrimePowerSum K χ W X ν‖ ≤ (1 / (2 * Real.pi)) *
          ((M * X ^ (β + δ)) * CW +
            2 * (CW / (1 + H) ^ order) * M * X ^ (2 : ℝ) * (2 - (β + δ)) +
            (actualPrimeLogMass K 2 * X ^ (2 : ℝ)) * (CW / H ^ order)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ :=
    exists_actual_finite_height_logDeriv_bound K hcomplex arch weight R hR
  refine ⟨C, A, hC, hA, ?_⟩
  intro χ W order CW hCW hprofile U β δ ν H X Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hX hpadding hupper
  let s : ℂ := vertical 0 ν
  let M : ℝ := actualPrimeLogRectangleBound K C A U δ ν H
  have hdegree : 0 ≤ heightDegree K := by unfold heightDegree; positivity
  have hM : 0 ≤ M := by
    have hlogC := Real.log_nonneg hC
    have hlogU := Real.log_nonneg hU
    have hlogH := Real.log_nonneg (by linarith [abs_nonneg ν] : 1 ≤ 4 + |ν| + H)
    dsimp [M, actualPrimeLogRectangleBound]
    positivity
  have hheight : ∀ z ∈ closedRectangle (β + δ) 2 H,
      |(s + z).im| ≤ |ν| + H := by
    intro z hz
    calc
      |(s + z).im| = |ν + z.im| := by simp only [s, Complex.add_im, vertical_im]
      _ ≤ |ν| + |z.im| := abs_add _ _
      _ ≤ |ν| + H := add_le_add_left hz.2.2 _
  have hnonzero : ∀ z ∈ closedRectangle (β + δ) 2 H,
      heckeContinuation K χ (s + z) ≠ 0 := by
    intro z hz
    apply continuation_ne_zero_of_upper K χ hχ Hupper β hβ hupper (s + z)
    · have hre : (s + z).re = z.re := by simp only [s, Complex.add_re, vertical_re, zero_add]
      rw [hre]
      linarith [hz.1]
    · exact (hheight z hz).trans (by linarith)
  have hLdiff : DifferentiableOn ℂ (fun z => actualPrimeLogFunction K χ (s + z))
      (closedRectangle (β + δ) 2 H) := by
    intro z hz
    have ha := (differentiable_heckeContinuation_of_nonNorm K χ hχ).analyticAt (s + z)
    have hd : DifferentiableAt ℂ (actualPrimeLogFunction K χ) (s + z) :=
      (ha.deriv.neg.div ha (hnonzero z hz)).differentiableAt
    exact (hd.comp z (differentiableAt_const.add differentiableAt_id)).differentiableWithinAt
  have hLrect : ∀ z ∈ closedRectangle (β + δ) 2 H,
      ‖actualPrimeLogFunction K χ (s + z)‖ ≤ M := by
    intro z hz
    have him : |ν + z.im| ≤ |ν| + H := by
      simpa only [s, Complex.add_im, vertical_im] using hheight z hz
    have hpoint := hbound χ U β δ z.re (ν + z.im) Hupper hχ harch hweight hU hQ
      hβ hβ' hδ hδ' hz.1 hz.2.1 (by linarith) hupper
    have heq : PrimeCancellationDiskGeometry.verticalPoint z.re (ν + z.im) = s + z := by
      apply Complex.ext <;> simp [PrimeCancellationDiskGeometry.verticalPoint, s, vertical]
    rw [heq] at hpoint
    have hnorm : ‖actualPrimeLogFunction K χ (s + z)‖ =
        ‖deriv (heckeContinuation K χ) (s + z) / heckeContinuation K χ (s + z)‖ := by
      simp only [actualPrimeLogFunction, neg_div, norm_neg]
    rw [hnorm]
    apply hpoint.trans
    have hlog : Real.log (4 + |ν + z.im|) ≤ Real.log (4 + |ν| + H) :=
      Real.log_le_log (by positivity) (by linarith)
    have hterm := mul_le_mul_of_nonneg_left hlog hdegree
    dsimp [M, actualPrimeLogRectangleBound]
    apply div_le_div_of_nonneg_right _ (sq_nonneg δ)
    linarith
  have hLleft : ∀ t, |t| ≤ H →
      ‖actualPrimeLogFunction K χ (s + vertical (β + δ) t)‖ ≤ M := by
    intro t ht
    apply hLrect
    exact ⟨by simp, by simp only [vertical_re]; linarith, by simpa only [vertical_im] using ht⟩
  have hsum : Summable (fun np : ActualPrimeLogIndex K =>
      ‖actualPrimeLogCoefficient K χ np‖ * actualPrimePowerNorm K np ^ (-(s.re + 2))) := by
    simpa only [s, vertical_re, zero_add] using
      (actualPrimeLog_absolutelySummable K χ (σ := 2) (by norm_num))
  have hline : ∀ t, actualPrimeLogFunction K χ (s + vertical 2 t) =
      dirichletSeries (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K)
        (s + vertical 2 t) := by
    intro t
    exact actualPrimeLogFunction_eq_dirichletSeries K χ (by simp [s])
  have hraw := annular_polynomial_upper_with_contour_data W (1 / 2) 2 order CW hCW hprofile
    (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K) (actualPrimePowerNorm_pos K)
    (actualPrimeLogFunction K χ) s (X := X) (a := β + δ) (b := 2) (H := H)
    (Mleft := M) (M := M) hX (by linarith) (by linarith) le_rfl hH hM hM
    hsum hline hLdiff hLrect hLleft (actualPrimeLogWindow K (W.upper * X))
    (mem_actualPrimeLogWindow_of_le K (W.upper * X))
  have hmass := actualPrimeLog_absMass_le K χ (σ := 2) (by norm_num)
  have htail := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (zero_le_one.trans hX) (2 : ℝ)))
    (div_nonneg hCW (pow_nonneg hH.le order))
  change ‖actualAnnularPrimePowerSum K χ W X ν‖ ≤ (1 / (2 * Real.pi)) *
    ((M * X ^ (β + δ)) * CW +
      2 * (CW / (1 + H) ^ order) * M * X ^ (2 : ℝ) * (2 - (β + δ)) +
      (actualPrimeLogMass K 2 * X ^ (2 : ℝ)) * (CW / H ^ order))
  apply le_trans (by simpa only [actualAnnularPrimePowerSum, s, vertical_re, zero_add] using hraw)
  exact mul_le_mul_of_nonneg_left (add_le_add_left htail _)
    (by positivity : 0 ≤ 1 / (2 * Real.pi))

/-- Fixed-profile specialization; the constants are chosen before all row data. -/
theorem exists_actual_annular_primePower_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ (χ : HeckeCharacter K) (W : AnnularProfile) (order : ℕ)
        (U β δ ν H X Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → 1 ≤ X → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        let CW := W.contourConstant (1 / 2) 2 order
        let M := actualPrimeLogRectangleBound K C A U δ ν H
        ‖actualAnnularPrimePowerSum K χ W X ν‖ ≤ (1 / (2 * Real.pi)) *
          ((M * X ^ (β + δ)) * CW +
            2 * (CW / (1 + H) ^ order) * M * X ^ (2 : ℝ) * (2 - (β + δ)) +
            (actualPrimeLogMass K 2 * X ^ (2 : ℝ)) * (CW / H ^ order)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ :=
    exists_actual_primePower_bound_of_contour_data K hcomplex arch weight R hR
  refine ⟨C, A, hC, hA, ?_⟩
  intro χ W order U β δ ν H X Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hX hpadding hupper
  exact hbound χ W order (W.contourConstant (1 / 2) 2 order)
    (W.contourConstant_spec (1 / 2) 2 order).1
    (W.contourConstant_spec (1 / 2) 2 order).2 U β δ ν H X Hupper
    hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hX hpadding hupper

end Expansion.Project

#print axioms Expansion.Project.exists_actual_primePower_bound_of_contour_data
#print axioms Expansion.Project.exists_actual_annular_primePower_bound
