import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularMellinSeparation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual plain polynomials with fixed Mellin-window profiles

The finite support is the exact support of the fixed cutoff, independent
of the row and frequency.  Extending the original finite sum to this
support adds only proved zero terms.  Character coefficients, all common
masks and the square-root normalization are kept literally.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

/-- The exact all-real-scale finite support of the fixed norm cutoff. -/
def annularMellinSupport (B : SmoothAnnularTest) (N : ℝ) : Finset (NonzeroIdeal K) :=
  if 0 < N then annularIdealSupport K B N else ∅

theorem mem_annularMellinSupport (B : SmoothAnnularTest) (N frequency : ℝ)
    (I : NonzeroIdeal K) :
    I ∈ annularMellinSupport K B N ↔
      annularMellinWindow B frequency (idealNorm K I / N) ≠ 0 := by
  have hw : annularMellinWindow B frequency (idealNorm K I / N) ≠ 0 ↔
      B.toFun (idealNorm K I / N) ≠ 0 := by
    simp only [annularMellinWindow, mul_ne_zero_iff, profilePower_ne_zero, and_true]
  by_cases hN : 0 < N
  · rw [annularMellinSupport, if_pos hN, mem_annularIdealSupport K B hN, hw]
  · have hy : idealNorm K I / N ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (idealNorm_pos K I).le (le_of_not_gt hN)
    have hz : B.toFun (idealNorm K I / N) = 0 := (good_toFun B).zero _ (by
      intro hmem
      have := B.lower_pos.trans_le hmem.1
      linarith)
    simp [annularMellinSupport, hN, hw, hz]

/-- A row-independent actual ideal test, with frequency as its evaluation
parameter and an exact support at every real scale. -/
def annularMellinIdealTest (B : SmoothAnnularTest) : IdealTest K where
  profile _ frequency y := annularMellinWindow B frequency y
  support _ _ N := annularMellinSupport K B N
  support_spec _ frequency N I := mem_annularMellinSupport K B N frequency I

variable {K} {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The literal normalized finite plain column for this fixed window. -/
def annularMellinPlainColumn (d : MomentData K omegaCharacter psiCharacter)
    (B : SmoothAnnularTest) (u : NonzeroIdeal K) (N frequency : ℝ) : ℂ :=
  plainPolynomial d (annularMellinIdealTest K B) u N frequency

theorem continuous_annularMellinPlainColumn
    (d : MomentData K omegaCharacter psiCharacter) (B : SmoothAnnularTest)
    (u : NonzeroIdeal K) (N : ℝ) :
    Continuous (annularMellinPlainColumn d B u N) := by
  unfold annularMellinPlainColumn plainPolynomial annularMellinIdealTest
  exact continuous_const.mul (continuous_finset_sum _ (fun I _ =>
    (continuous_const.mul (continuous_annularMellinWindow B (idealNorm K I / N))).mul
      continuous_const))

/-- The finite arithmetic constant is used only for actual integrability.
It never enters the common Mellin kernel mass. -/
theorem annularMellinPlainColumn_bounded
    (d : MomentData K omegaCharacter psiCharacter) (B : SmoothAnnularTest)
    (u : NonzeroIdeal K) (N : ℝ) :
    ∃ C : ℝ, ∀ frequency : ℝ, ‖annularMellinPlainColumn d B u N frequency‖ ≤ C := by
  let c : NonzeroIdeal K → ℂ := fun I =>
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val
  let S := annularMellinSupport K B N
  let C := ‖(Real.sqrt N : ℂ)⁻¹‖ *
    ∑ I ∈ S, ‖c I‖ * ‖B.toFun (idealNorm K I / N)‖
  refine ⟨C, fun frequency => ?_⟩
  have he : annularMellinPlainColumn d B u N frequency =
      (Real.sqrt N : ℂ)⁻¹ *
        ∑ I ∈ S, c I * annularMellinWindow B frequency (idealNorm K I / N) := by
    unfold annularMellinPlainColumn plainPolynomial annularMellinIdealTest
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only [c]
    ring
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑ I ∈ S, ‖c I * annularMellinWindow B frequency (idealNorm K I / N)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul, annularMellinWindow_norm]

theorem annularMellinPlainColumn_memLp
    (d : MomentData K omegaCharacter psiCharacter) (B : SmoothAnnularTest)
    (u : NonzeroIdeal K) (N : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    MemLp (annularMellinPlainColumn d B u N) 2 μ := by
  obtain ⟨C, hC⟩ := annularMellinPlainColumn_bounded d B u N
  exact MemLp.of_bound (continuous_annularMellinPlainColumn d B u N).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem integrable_annularMellinCoefficient_plainColumn
    (d : MomentData K omegaCharacter psiCharacter) (B V : SmoothAnnularTest)
    (u : NonzeroIdeal K) (N : ℝ) :
    Integrable (fun frequency : ℝ =>
      annularMellinCoefficient V frequency * annularMellinPlainColumn d B u N frequency) := by
  obtain ⟨C, hC⟩ := annularMellinPlainColumn_bounded d B u N
  exact (integrable_annularMellinCoefficient V).mul_bdd
    (continuous_annularMellinPlainColumn d B u N).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- Mellin inversion of the actual finite polynomial. The same coefficient
function serves every scale `N`, which is essential for centering. -/
theorem plainPolynomial_annularMellin_separation
    (d : MomentData K omegaCharacter psiCharacter) (W : IdealTest K)
    (u : NonzeroIdeal K) (time : ℝ) (B V : SmoothAnnularTest)
    (hV : V.toFun = W.profile u time)
    (hB : ∀ y, V.toFun y ≠ 0 → B.toFun y = 1)
    {N : ℝ} (hN : 0 < N) :
    plainPolynomial d W u N time =
      ∫ frequency : ℝ, annularMellinCoefficient V frequency *
        annularMellinPlainColumn d B u N frequency := by
  let c : NonzeroIdeal K → ℂ := fun I =>
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val
  let S := W.support u time N
  let T := annularMellinSupport K B N
  have hST : S ⊆ T := by
    intro I hI
    have hVi : V.toFun (idealNorm K I / N) ≠ 0 := by
      rw [hV]
      exact (W.support_spec u time N I).1 hI
    change I ∈ annularMellinSupport K B N
    rw [annularMellinSupport, if_pos hN, mem_annularIdealSupport K B hN]
    rw [hB _ hVi]
    exact one_ne_zero
  have hsum : (∑ I ∈ S, c I * V.toFun (idealNorm K I / N)) =
      ∑ I ∈ T, c I * V.toFun (idealNorm K I / N) := by
    apply Finset.sum_subset hST
    intro I hIT hIS
    have hzero : V.toFun (idealNorm K I / N) = 0 := by
      by_contra h
      apply hIS
      exact (W.support_spec u time N I).2 (by simpa only [hV] using h)
    rw [hzero, mul_zero]
  have hcolumn (frequency : ℝ) :
      annularMellinPlainColumn d B u N frequency =
        (Real.sqrt N : ℂ)⁻¹ *
          ∑ I ∈ T, c I * annularMellinWindow B frequency (idealNorm K I / N) := by
    unfold annularMellinPlainColumn plainPolynomial annularMellinIdealTest
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only [c]
    ring
  calc
    plainPolynomial d W u N time = (Real.sqrt N : ℂ)⁻¹ *
        ∑ I ∈ S, c I * V.toFun (idealNorm K I / N) := by
      unfold plainPolynomial
      congr 1
      apply Finset.sum_congr rfl
      intro I hI
      rw [hV]
      dsimp only [c]
      ring
    _ = (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ T, c I * V.toFun (idealNorm K I / N) := by
      rw [hsum]
    _ = (Real.sqrt N : ℂ)⁻¹ *
        ∫ frequency : ℝ, annularMellinCoefficient V frequency *
          ∑ I ∈ T, c I * annularMellinWindow B frequency (idealNorm K I / N) := by
      rw [finite_sum_annularMellin_separation T c (fun I => idealNorm K I / N) B V hB]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun frequency => by rw [hcolumn]; ring

end HeckeSkeleton.Moments.EngineInduction
