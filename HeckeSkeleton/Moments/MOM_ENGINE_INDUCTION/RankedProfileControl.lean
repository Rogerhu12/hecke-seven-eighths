import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalNodeFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceProfileAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependent

/-!
# One actual profile budget for the literal root and all earlier children

The source root need not lie in a unit ball.  Its unchanged profiles use
the one height budget selected from the source.  Actual normalized
children satisfy a unit estimate at the parent's predecessor order and
therefore satisfy their own lower rank's order in this same budget.

The finite backward sequence is fixed before the moving height.  These
are primitive profile facts, with no energy, kernel mass, parent step or
recursive child estimate in their hypotheses.  Arithmetic and mixed-row
source admissibility remain separate requirements of the actual engine.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The original height envelope is enlarged once, before the height is
chosen, so that it also contains every actually normalized child. -/
def profileFamilyBudget (C H T : ℝ) : ℝ := (1 + C) * (1 + T) ^ H

theorem profileFamilyBudget_one_le {C H T : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    1 ≤ profileFamilyBudget C H T := by
  have hpow : 1 ≤ (1 + T) ^ H := Real.one_le_rpow (by linarith) hH
  unfold profileFamilyBudget
  nlinarith

theorem profileFamilyBudget_dominates (C H : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    C * (1 + T) ^ H ≤ profileFamilyBudget C H T := by
  have hp := Real.rpow_nonneg (by linarith : 0 ≤ 1 + T) H
  unfold profileFamilyBudget
  nlinarith

/-- A fixed finite-order coefficient can be paid once in the original
source envelope, before its height or any descendant is chosen. -/
theorem coefficient_le_profileFamilyBudget {D C H T : ℝ}
    (hC : 0 ≤ C) (hDC : D ≤ C) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    D ≤ profileFamilyBudget C H T := by
  have hheight : 1 ≤ (1 + T) ^ H := Real.one_le_rpow (by linarith) hH
  exact hDC.trans ((le_mul_of_one_le_right hC hheight).trans
    (profileFamilyBudget_dominates C H hT))

/-- Every fixed power of the source budget has one fixed height degree.
No continuous child frequency is inserted into the source height box. -/
theorem profileFamilyBudget_pow (C H : ℝ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    profileFamilyBudget C H T ^ n =
      (1 + C) ^ n * (1 + T) ^ (H * (n : ℝ)) := by
  unfold profileFamilyBudget
  rw [mul_pow, ← Real.rpow_natCast ((1 + T) ^ H) n,
    ← Real.rpow_mul (by linarith : 0 ≤ 1 + T)]

theorem modelProfileControl_mono_budget {d : MomentData K ω ψ}
    {J : ℕ} {A P Q lower upper : ℝ}
    (h : ModelProfileControl d J A P 0 lower upper 0) (hPQ : P ≤ Q) :
    ModelProfileControl d J A Q 0 lower upper 0 := by
  intro q
  refine ⟨(h q).1, (h q).2.1, ?_⟩
  simpa only [Real.rpow_zero, mul_one] using
    (show testSeminorm (modelProfile d q) J A ≤ P from
      by simpa only [Real.rpow_zero, mul_one] using (h q).2.2).trans hPQ

/-- The true parameter rank is bounded before any data or profile is
chosen.  The outer zero-slot stage is included in this same bound. -/
theorem parameterCoreRank_lt_bound {σ W padding : ℝ} (a : RealParameters)
    (hσ : 0 < σ) (hwidth : a.m + a.q ≤ W) :
    parameterCoreRank σ W padding a < 6 * (widthBand σ W + 1) := by
  have hb := widthBand_mono hσ hwidth
  unfold parameterCoreRank
  split_ifs <;> omega

/-- The profile part of actual admissibility depends on precisely the
numerical quantities preserved by quarter centering and comparison. -/
def rankedProfilePrimitive (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ W padding A P lower upper : ℝ)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  ModelProfileControl d
    (backwardProfileOrder ground engine reflection
      (parameterCoreRank σ W padding p.parameters)) A P 0 lower upper 0

theorem rankedProfilePrimitive_iff (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ W padding A P lower upper : ℝ) (d : MomentData K ω ψ) (a : RealParameters) :
    admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper) d a ↔
      ModelProfileControl d (backwardProfileOrder ground engine reflection
        (parameterCoreRank σ W padding a)) A P 0 lower upper 0 := by
  unfold admissibleOfInvariant rankedProfilePrimitive
  rw [pairedInvariantParameters_coreRank]

/-- The unchanged source can be placed in its actual rank's profile
class using the one preselected maximal finite Euler order. -/
theorem rankedProfilePrimitive_of_top
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {d : MomentData K ω ψ} {a : RealParameters}
    (hσ : 0 < σ) (hwidth : a.m + a.q ≤ W)
    (h : ModelProfileControl d
      (backwardProfileOrder ground engine reflection (6 * (widthBand σ W + 1)))
      A P 0 lower upper 0) :
    admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper) d a := by
  rw [rankedProfilePrimitive_iff]
  exact modelProfileControl_mono_order h
    (backwardProfileOrder_monotone ground engine reflection
      (parameterCoreRank_lt_bound a hσ hwidth).le)

/-- Ground-level base and terminal seminorms are available at every node. -/
theorem rankedProfilePrimitive_ground
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {d : MomentData K ω ψ} {a : RealParameters}
    (h : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper) d a) :
    ModelProfileControl d ground A P 0 lower upper 0 := by
  rw [rankedProfilePrimitive_iff] at h
  exact modelProfileControl_mono_order h
    (backwardProfileOrder_ground_le ground engine reflection _)

/-- The two actual analytic calls may each ask for their own higher
Euler order.  Both orders were paid by the predecessor recursion. -/
theorem rankedProfilePrimitive_parent_orders
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {d : MomentData K ω ψ} {a : RealParameters}
    (h : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper) d a)
    (hrank : 0 < parameterCoreRank σ W padding a) :
    let J := backwardProfileOrder ground engine reflection
      (parameterCoreRank σ W padding a - 1)
    ModelProfileControl d (engine J) A P 0 lower upper 0 ∧
      ModelProfileControl d (reflection J) A P 0 lower upper 0 := by
  rw [rankedProfilePrimitive_iff] at h
  have ho := backwardProfileOrder_parent_orders ground engine reflection hrank
  exact ⟨modelProfileControl_mono_order h ho.1, modelProfileControl_mono_order h ho.2⟩

/-- A genuinely normalized child at the requested predecessor order
enters its own earlier profile class with the same root budget. -/
theorem rankedProfilePrimitive_normalized_child
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {child : MomentData K ω ψ}
    {childParameters parentParameters : RealParameters} (hP : 1 ≤ P)
    (hearlier : parameterCoreRank σ W padding childParameters <
      parameterCoreRank σ W padding parentParameters)
    (h : ModelProfileControl child
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank σ W padding parentParameters - 1)) A 1 0 lower upper 0) :
    admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper)
      child childParameters := by
  rw [rankedProfilePrimitive_iff]
  exact modelProfileControl_mono_budget
    (normalized_child_rank_profile_control ground engine reflection hearlier h) hP

/-- At time zero the frozen data have exactly the original four kinds
of actual profile slices. No uniformity at other evaluation times is
assumed; the canonical engine's zero-twist equations justify this use. -/
theorem freezeMomentTime_zero_control {d : MomentData K ω ψ}
    {J : ℕ} {A C H lower upper T : ℝ}
    (h : ModelProfileControl d J A C H lower upper T) :
    ModelProfileControl (freezeMomentTime d 0) J A C H lower upper T := by
  intro q
  cases q with
  | inverse u =>
    simpa only [modelProfile, freezeMomentTime, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using
        modelProfileControl_inverse h u
  | plain₁ u =>
    simpa only [modelProfile, freezeMomentTime, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using
        modelProfileControl_plain₁ h u
  | plain₂ u =>
    simpa only [modelProfile, freezeMomentTime, MomentData.separatedProfiles,
      IdealTest.freezeTwist, profilePower_zero, mul_one] using
        modelProfileControl_plain₂ h u
  | prime j =>
    simpa only [modelProfile, freezeMomentTime, MomentData.separatedProfiles,
      SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_zero, mul_one] using
        modelProfileControl_prime h j

theorem rankedProfilePrimitive_freeze_zero
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A P lower upper : ℝ} {d : MomentData K ω ψ} {a : RealParameters}
    (h : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper) d a) :
    admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A P lower upper)
      (freezeMomentTime d 0) a := by
  rw [rankedProfilePrimitive_iff] at h ⊢
  exact freezeMomentTime_zero_control h

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- All original roots, including the no-slot index, enter the same
finite-order profile family. The annulus precedes the analytic order
functions; the constants then precede every original scale, height,
index and sector. The original root is never rescaled. -/
theorem recipeRoot_ranked_profile_budget {lengthBound : ℝ}
    (hgeom : R.MomentGeometry lengthBound)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R)) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∀ (ground : ℕ) (engine reflection : ℕ → ℕ) (σ padding A : ℝ),
      0 < σ → 0 ≤ A → ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
        ∀ Z T : ℝ, 0 ≤ T →
        ∀ (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
          (s : SixthUnitClasses K (places K c)),
        admissibleOfInvariant
          (rankedProfilePrimitive ground engine reflection σ 2 padding A
            (profileFamilyBudget C H T) lower upper)
          (recipeRoot R i s).data (recipeRoot R i s).parameters := by
  obtain ⟨lower, upper, hlower, hsmall, hlarge, hinterval, hsource⟩ :=
    recipeRoot_fixed_annulus_profiles R hgeom hprofiles
  refine ⟨lower, upper, hlower, hsmall, hlarge, hinterval, ?_⟩
  intro ground engine reflection σ padding A hσ hA
  obtain ⟨C, H, hC, hH, hbound⟩ := hsource
    (backwardProfileOrder ground engine reflection (6 * (widthBand σ 2 + 1))) A hA
  refine ⟨C, H, hC, hH, ?_⟩
  intro Z T hT i s
  apply rankedProfilePrimitive_of_top ground engine reflection hσ
    (recipeRoot_width_range R i s).2
  exact modelProfileControl_fixed_budget (hbound Z T i s)
    (profileFamilyBudget_dominates C H hT)

end Source

end HeckeSkeleton.Moments.EngineInduction
