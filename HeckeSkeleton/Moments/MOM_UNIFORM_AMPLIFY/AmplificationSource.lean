import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerRecipe
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerEnergy

/-!
# Uniform independent amplification of the single source recipe

The corrected canonical inverse input uses complete ideal rows and one
majorant over all strict smaller scales.  Original U,D and the original
profile are frozen in its index before the amplified row scale is chosen.
This retains the paper's permitted profile supremum and the polynomial
height factor; the conclusion is the literal original sixth-free sector
sum with independent U,D.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {E : MomentSourceData K c}

local instance sourceMomentSectorFintype : Fintype (SixthUnitClasses K (places K c)) :=
  Fintype.ofFinite _

abbrev UnmarkedProfileIndex (M : SourceMomentModelsFor K c E) :=
  UnmarkedProfileParameters (places K c) M.dimension

/-- Corrected output required from the canonical inverse theorem in the
no-slot case: all complete ideal rows, one fixed original profile, all
strict smaller scales, and quantitative polynomial height growth. -/
def CompleteUnmarkedScaleSupBoundFor (M : SourceMomentModelsFor K c E) : Prop :=
  CompleteUnmarkedScaleSupBound M.unmarked

theorem dyadic_amplifier_factor_le {U D c ε : ℝ}
    (hU : 1 ≤ U) (hD : 1 ≤ D) :
    max (2 * U) ((2 * U) ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) *
        ((2 * U) * D) ^ ε ≤
      (2 * (2 : ℝ) ^ ε) *
        (max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε) := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hroot : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (1 / 6 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  have hmax : max (2 * U) ((2 * U) ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) ≤
      2 * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) := by
    apply max_le
    · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    · rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hU0]
      calc
        ((2 : ℝ) ^ (1 / 6 : ℝ) * U ^ (1 / 6 : ℝ)) * D ^ (5 * (1 + c) / 6) ≤
            (2 * U ^ (1 / 6 : ℝ)) * D ^ (5 * (1 + c) / 6) := by
          gcongr
        _ = 2 * (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  have hscale : ((2 * U) * D) ^ ε = (2 : ℝ) ^ ε * (U * D) ^ ε := by
    rw [mul_assoc, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hU0 hD0)]
  calc
    _ ≤ (2 * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6))) *
        ((2 * U) * D) ^ ε := mul_le_mul_of_nonneg_right hmax
          (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [hscale]; ring

/-- MI-I-INDEPENDENT-AMPLIFICATION for the actual algebraic source recipe.
The strict complete-row seed is the canonical inverse input; all arithmetic
masks, divisor identities, multiplier counting and profile transport are
proved internally. -/
theorem recipe_inverse_independent_amplification
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (hMI : CompleteUnmarkedScaleSupBoundFor (recipeMomentModels K c R)) :
    AmplifiedIndependentMomentBoundFor (recipeMomentModels K c R) := by
  let M := recipeMomentModels K c R
  have harith (i : UnmarkedProfileIndex M) :=
    recipe_unmarked_arithmetic R i.rowScale i.polynomialScale i.sector
      i.heights i.realShifts i.imagShifts
  intro a ε ha hε
  obtain ⟨C, A, h, hC, hA, hh, hbound⟩ := completeIdeal_independent_energy
    (places K c) (fun i : UnmarkedProfileIndex M => unmarkedProfileData M.unmarked i)
    (fun i => ‖i.heights‖)
    (fun i => norm_nonneg _) (fun i => (harith i).1) (fun i => (harith i).2.2)
    (by
      intro i u b hu
      rw [(harith i).2.1]
      exact completeIdealRowCharacter_mul_sixth (places K c) (probeData K c)
        (momentRowCharacters K c) u b (by simpa only [(harith i).1] using hu) i.sector)
    hMI ha hε
  let N : ℝ := Fintype.card (SixthUnitClasses K (places K c))
  let C' : ℝ := max 1 N * (C * (2 * (2 : ℝ) ^ ε))
  have hC' : 0 < C' := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (mul_pos hC (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)))
  refine ⟨C', A, h, hC', hA, hh, ?_⟩
  intro U D hU hD ξ σ τ hheight hσ hτ
  have hU2 : 1 ≤ 2 * U := by linarith
  have hUD : 0 ≤ U * D := mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hD)
  have hheight' : ‖ξ‖ ≤ ((2 * U) * D) ^ h := hheight.trans
    (Real.rpow_le_rpow hUD (by nlinarith [hUD]) hh.le)
  let F : ℝ := max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) *
    (U * D) ^ ε * (1 + ‖ξ‖) ^ A
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have heach (s : SixthUnitClasses K (places K c)) :
      unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D ≤ C * (2 * (2 : ℝ) ^ ε) * F := by
    let i : UnmarkedProfileIndex M :=
      ⟨U, D, hU, hD, s, ξ, σ, τ, hσ, hτ⟩
    have he := hbound i (2 * U) D hU2 hD hheight'
      (((unmarkedProfileData M.unmarked i).rows (2 * U)).filter (SixthPowerFreeIdeal (K := K))) (by
        intro u hu
        obtain ⟨hurow, hufree⟩ := Finset.mem_filter.mp hu
        have hr := ((unmarkedProfileData M.unmarked i).rows_spec (2 * U) u).mp hurow
        exact ⟨hr.1, hufree, hr.2⟩)
    change unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D ≤
      C * max (2 * U) ((2 * U) ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) *
        ((2 * U) * D) ^ ε * (1 + ‖ξ‖) ^ A at he
    calc
      _ ≤ C * (max (2 * U) ((2 * U) ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) *
          ((2 * U) * D) ^ ε) * (1 + ‖ξ‖) ^ A := by simpa only [mul_assoc] using he
      _ ≤ C * ((2 * (2 : ℝ) ^ ε) *
          (max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) * (U * D) ^ ε)) *
          (1 + ‖ξ‖) ^ A := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (dyadic_amplifier_factor_le hU hD) hC.le)
            (Real.rpow_nonneg (by positivity) _)
      _ = _ := by dsimp [F]; ring
  calc
    (∑ s : SixthUnitClasses K (places K c),
        unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D) ≤
        ∑ _s : SixthUnitClasses K (places K c), C * (2 * (2 : ℝ) ^ ε) * F :=
      Finset.sum_le_sum (fun s _ => heach s)
    _ = N * (C * (2 * (2 : ℝ) ^ ε) * F) := by simp [N]
    _ ≤ max 1 N * (C * (2 * (2 : ℝ) ^ ε) * F) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by dsimp [C', F]; ring

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.recipe_inverse_independent_amplification
