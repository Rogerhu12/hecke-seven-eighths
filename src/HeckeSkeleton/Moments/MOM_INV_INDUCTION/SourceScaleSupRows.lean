import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualScale
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerEnergy

/-!
# Simultaneous scale bounds for the actual complete-row source family

This module constructs the nonnegative row function required by the
strict scale-sup seed, using the original independent parameters and the
actual sixth-power profile pullback.  Its sum is exactly the common
positive prefix integral.  The subsequent canonical estimate is applied
to the dyadic annular polynomials inside that integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupRows

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open SourceActualScale
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

abbrev Parameters := UnmarkedProfileParameters (places K c) 6

def originalData (i : Parameters K c) : MomentData K c.family.omega (targetCharacter K c) :=
  unmarkedProfileData (recipeMomentModels K c (expansionRecipeRaw K c)).unmarked i

def pulledData (i : Parameters K c) : MomentData K c.family.omega (targetCharacter K c) :=
  sixthRootInverseData (originalData K c i)

def realParameter (i : Parameters K c) (u : NonzeroIdeal K) : ℝ :=
  -(i.realShifts (sixthPowerFreePart u) 0)

def imagParameter (i : Parameters K c) (u : NonzeroIdeal K) : ℝ :=
  (expansionRecipeRaw K c).family.frequencyScale * i.imagShifts (sixthPowerFreePart u) 0

/-- The profile is literally that of the original source evaluated on
its sixth-free part; only its row parameter has been pulled back. -/
theorem pulled_profile (i : Parameters K c) (u : NonzeroIdeal K) :
    (pulledData K c i).inverseTest.profile u 0 =
      actualInverseScalarProfile K c u i.rowScale i.polynomialScale
        (realParameter K c i u) (imagParameter K c i u) (i.heights 3) := by
  change ((recipeMomentModels K c (expansionRecipeRaw K c)).unmarked
    i.rowScale i.polynomialScale i.sector i.heights i.realShifts i.imagShifts).inverseTest.profile
      (sixthPowerFreePart u) 0 = _
  rw [actual_unmarked_inverse_profile]
  rfl

theorem realParameter_bound (i : Parameters K c) (u : NonzeroIdeal K) :
    |realParameter K c i u| ≤ 8 := by
  simpa only [realParameter, abs_neg, ← Real.norm_eq_abs] using
    (norm_le_pi_norm (i.realShifts (sixthPowerFreePart u)) 0).trans
      (i.realShifts_bound (sixthPowerFreePart u))

theorem imagParameter_bound (i : Parameters K c) (u : NonzeroIdeal K)
    {T : ℝ} (hT : ‖i.heights‖ ≤ T) :
    |imagParameter K c i u| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) := by
  rw [imagParameter, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hu := (norm_le_pi_norm (i.imagShifts (sixthPowerFreePart u)) 0).trans
    (i.imagShifts_bound (sixthPowerFreePart u))
  rw [Real.norm_eq_abs] at hu
  exact hu.trans (add_le_add le_rfl hT)

def majorant (i : Parameters K c) (L : ℕ) (W : ℝ → ℝ) (u : NonzeroIdeal K) : ℝ :=
  SourceScaleSup.rowMajorant (dyadicIdealSupport K (8 * (2 : ℝ) ^ L))
    (normWeightedCoefficient (pulledData K c i) u) (idealNorm K) L W

theorem majorant_nonneg (i : Parameters K c) (L : ℕ)
    (W : ℝ → ℝ) (hW : ∀ t, 0 ≤ W t) (u : NonzeroIdeal K) :
    0 ≤ majorant K c i L W u := SourceScaleSup.rowMajorant_nonneg _ _ _ _ _ hW

/-- One kernel precedes every actual source index, every complete row,
and all smaller scales.  In particular no choice depends on D'. -/
theorem exists_actual_common_majorant (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∃ W : ℝ → ℝ,
      (∀ t, 0 ≤ W t) ∧ Continuous W ∧ Integrable W ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t) ∧
      (∫ t : ℝ, (1 + ‖t‖) ^ J * W t) ≤ C * (1 + T) ^ (J + 2 : ℕ) ∧
      ∀ i : Parameters K c, ‖i.heights‖ ≤ T → ∀ L : ℕ,
        (∀ u, 0 ≤ majorant K c i L W u) ∧
        (∀ u, ∀ D' : ℝ, 0 < D' → 2 * D' ≤ (2 : ℝ) ^ L →
          ‖inversePolynomial (pulledData K c i) u D' 0‖ ^ 2 ≤ majorant K c i L W u) := by
  obtain ⟨C, hC, hb⟩ := SourceActualScale.exists_common_majorant K c J
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨W, hW0, cW, iW, iWJ, hmass, hpoint⟩ := hb T hT
  refine ⟨W, hW0, cW, iW, iWJ, hmass, ?_⟩
  intro i hi L
  refine ⟨majorant_nonneg K c i L W hW0, ?_⟩
  intro u
  exact inversePolynomial_sq_le_rowMajorant (pulledData K c i) u
    i.rowScale i.polynomialScale (realParameter K c i u) (imagParameter K c i u)
    (i.heights 3) L (zero_lt_one.trans_le i.rowScale_one_le)
    (zero_le_one.trans i.polynomialScale_one_le) (pulled_profile K c i u) W hW0 cW iW
    (hpoint i.rowScale (zero_lt_one.trans_le i.rowScale_one_le)
      i.polynomialScale (zero_le_one.trans i.polynomialScale_one_le)
      (realParameter K c i u) (imagParameter K c i u) (i.heights 3)
      (realParameter_bound K c i u) (imagParameter_bound K c i u hi))

/-- This is the complete row sum occurring in the strict seed.  It is
the same fixed-prefix energy under one common measure, before any
moment estimate or sixth-free row restriction. -/
theorem complete_row_sum (i : Parameters K c) (H : ℝ) (L : ℕ)
    (W : ℝ → ℝ) (iW : Integrable W) :
    (∑ u ∈ (originalData K c i).rows H, majorant K c i L W u) =
      (∫ t : ℝ, W t) * ∫ t : ℝ, W t *
        ∑ u ∈ (originalData K c i).rows H,
          ‖SourceScaleSup.prefixColumn (dyadicIdealSupport K (8 * (2 : ℝ) ^ L))
            (normWeightedCoefficient (pulledData K c i) u) (idealNorm K) L t‖ ^ 2 :=
  SourceScaleSup.sum_rowMajorant _ _ _ _ _ _ iW

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupRows

end
