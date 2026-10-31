import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualArithmetic
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedOrbital
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCompleteRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupClosure

/-!
# Complete ideal rows of the original unmarked source

The initial orbital source contains every complete exterior row, in its
original sixth-unit sector.  Positive orientation is handled by conjugating
the whole polynomial and its background.  The fixed small column range is
estimated directly.  Together they give the annular input for the common
scale-sup majorant, uniformly before the original source parameters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedComplete

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open SourceScaleSupRows SourceActualArithmetic SourceCompleteRows ProviderNodes
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => excludedPlaces K c
local notation "Sset" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Θ" => twists K c
local notation "ψ" => targetCharacter K c

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

local instance normOneSpace : MeasurableSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneSpace

local instance normOneBorel : BorelSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneBorel

local instance principal : IsPrincipalIdealRing (Set.integer Sset K) :=
  (axiomChoice K c).C.principal

/-- The complete-row annular estimate, with every character and mask
calibrated to the literal source.  Only the actual canonical node bound
remains as the induction input of this internal assembly theorem. -/
theorem annular_bound_of_uniform
    (gap eps : ℝ) (hgap0 : 0 < gap) (hgap1 : gap < 1) (heps : 0 < eps)
    (t : Finset (ℕ × ℕ)) (Cih Hih : ℝ) (hCih : 1 ≤ Cih) (hHih : 2 ≤ Hih)
    (hih : ∀ H : ℝ, Hih ≤ H →
      UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D P.Lambda P.G 0 H 1
        (3 * gap / 16) 0 1 2 (eps / 2) 1 Cih t) :
    ∃ q : Finset (ℕ × ℕ), ∃ C H₀ : ℝ, 0 ≤ C ∧ 2 ≤ H₀ ∧
      ∀ (i : Parameters K c) (H X : ℝ), H₀ ≤ H → 0 < X →
        X ≤ H ^ (1 - gap / 2) → ∀ W : SchwartzMap ℝ ℂ,
        tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
        (∑ u ∈ (originalData K c i).rows H,
          ‖SourceAnnularRows.polynomial K (pulledData K c i) u X W‖ ^ 2) ≤
          C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * H ^ (1 + eps) := by
  obtain ⟨qOrb, COrb, HOrb, hCOrb, hHOrb, horb⟩ :=
    SourceUnmarkedOrbital.exists_uniform_orbital_bound_of_scale K S D Γ le_rfl
      (allowedGenerators K c) (Expansion.ActualProbeContext.allLocalMeasures K)
      (Expansion.ActualProbeContext.finiteAdeleMeasure K)
      (Expansion.ActualProbeContext.adeleMeasure K) 0 gap eps hgap0 hgap1 heps t
  obtain ⟨s, CConj, hCConj, hconj⟩ := conjugateTest_seminorm qOrb
  obtain ⟨CSmall, hCSmall, hsmall⟩ := SourceAnnularRows.exists_small_scale_row_bound K
  let q := insert (0, 0) s
  let CLarge := (InverseRowMajorant.rowCovolume K S)⁻¹ * COrb * Cih * CConj ^ 2
  have hCLarge : 0 ≤ CLarge := by
    dsimp only [CLarge]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)
      (zero_le_one.trans hCOrb)) (zero_le_one.trans hCih)) (sq_nonneg _)
  refine ⟨q, CSmall + CLarge, max Hih HOrb, by positivity,
    hHih.trans (le_max_left _ _), ?_⟩
  intro i H X hH hX hXH W hW
  have hHi : Hih ≤ H := (le_max_left _ _).trans hH
  have hHo : HOrb ≤ H := (le_max_right _ _).trans hH
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH1
  have hq0 : SchwartzMap.seminorm ℝ 0 0 W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ)
      (Finset.mem_insert_self (0, 0) s)) W
  have hqs : s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) s)) W
  by_cases hx : X ≤ 1
  · have hs := hsmall (pulledData K c i) H X W hH1 hX hx hW
    rw [pulled_rows] at hs
    calc
      _ ≤ CSmall * H * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := hs
      _ ≤ CSmall * H ^ (1 + eps) *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
        gcongr
        · simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hH1 (show (1 : ℝ) ≤ 1 + eps by linarith)
        · exact hq0
      _ ≤ (CSmall + CLarge) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          H ^ (1 + eps) := by
        have hc : CSmall ≤ CSmall + CLarge := le_add_of_nonneg_right hCLarge
        nlinarith [mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sq_nonneg (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))
            (Real.rpow_nonneg hHp.le (1 + eps)))]
  · have hX1 : 1 ≤ X := (lt_of_not_ge hx).le
    obtain ⟨hrows, hchar, hmask⟩ := pulled_arithmetic K c i
    have hs := complete_positive_rows_le_orbital K S P (momentRowCharacters K c)
      (pulledData K c i) i.sector (pulled_direction K c i) hchar hmask hrows
      H X hHp hX W hW
    rw [pulled_rows] at hs
    have ho := horb Θ ψ P.Lambda P.G (pulledData K c i).inverseBackground⁻¹
      (calibration_mem K c) (arithmeticCalibration K c) (pulled_background K c i)
      (SourceActualArithmetic.admissible_unramified K c _ (pulled_background K c i))
      1 2 H X hHp (conjugateTest W)
      (by rw [conjugateTest_support]; exact hW) hHo hX1 hXH Cih hCih (hih H hHi)
    have hqconj : qOrb.sup (schwartzSeminormFamily ℝ ℝ ℂ) (conjugateTest W) ≤
        CConj * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      (hconj W).trans (mul_le_mul_of_nonneg_left hqs hCConj)
    calc
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          ‖SourceReductionPoisson.orbitalEnergy K S D Γ (pulledData K c i).inverseBackground⁻¹
            (fun _ => 1) (conjugateTest W) X ⟨H, hHp⟩‖ := hs
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          (COrb * Cih * (qOrb.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (conjugateTest W)) ^ 2 * H ^ (1 + eps)) :=
        mul_le_mul_of_nonneg_left ho
          (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)
      _ ≤ (InverseRowMajorant.rowCovolume K S)⁻¹ *
          (COrb * Cih * (CConj * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
            H ^ (1 + eps)) := by gcongr
      _ = CLarge * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * H ^ (1 + eps) := by
        dsimp only [CLarge]; ring
      _ ≤ (CSmall + CLarge) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          H ^ (1 + eps) := by gcongr; linarith

/-- The complete-row, all-smaller-scale conclusion for the literal
unmarked recipe follows from the actual canonical induction at row cap
one.  This is an internal assembly theorem; the canonical premise is
discharged from the two primitive sieves in the final source closure. -/
theorem strict_seed_of_canonical_uniform
    (hcanonical : ∀ margin loss : ℝ, 0 < margin → 0 < loss →
      ∃ q : Finset (ℕ × ℕ), ∃ C H₀ : ℝ, 1 ≤ C ∧ 2 ≤ H₀ ∧
        ∀ H : ℝ, H₀ ≤ H →
          UniformBound (Γ := Γ) (Θ := Θ) (ψ := ψ) D P.Lambda P.G 0 H 1 margin
            0 1 2 loss 1 C q) :
    CompleteUnmarkedScaleSupBound
      (recipeMomentModels K c (expansionRecipeRaw K c)).unmarked := by
  apply SourceScaleSupClosure.strict_seed_of_uniform_annular K c
  intro gap eps hgap0 hgap1 heps
  obtain ⟨q, C, H₀, hC, hH₀, hb⟩ :=
    hcanonical (3 * gap / 16) (eps / 2) (by positivity) (by positivity)
  exact annular_bound_of_uniform K c gap eps hgap0 hgap1 heps q C H₀ hC hH₀ hb

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceUnmarkedComplete

end
