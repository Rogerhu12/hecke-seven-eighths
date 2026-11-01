import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeMovingThreshold
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeReflectionRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeReflectionParameters
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedAnnulusReflectionAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeInduction
import HeckeSkeleton.ExpansionModels.ScaleCutoff

/-!
# The literal source recipe in the ranked-annulus reflection family

The original source annulus and finite geometric depth are fixed before
all analytic orders. Reflection constants are selected on its maximal
scheduled enlargement; actual roots and descendants retain their own
rank's tighter support. The one highest source Euler order still
precedes the original source coefficient and height degree.

The existing source preparation is used unchanged, including its full
model ball, complete arithmetic calibration and separate no-slot and
capacity-eligible positive entrances. Its literal root is then put in
the stronger actual support subtype. No new source assumption or
admission is introduced, and no completed strict step or moment bound
is part of the constructed result.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- The source uses its actual rank's annulus with the same height
budget, full arithmetic mask and joint remaining-ideal calibration. -/
def recipeRankedAnnulusReflectionPrimitive (c : TargetContext K)
    (theta : Finset (HeckeCharacter K))
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma padding A C H lower upper U T : ℝ) :
    MomentData K c.family.omega (targetCharacter K c) → PairedInvariantParameters → Prop :=
  reflectionRankedAnnulusPrimitive (places K c) (probeData K c) (momentRowCharacters K c) theta U
    ground engine reflection sigma 2 padding A (profileFamilyBudget C H T) lower upper

def recipeRankedAnnulusReflectionSystem (c : TargetContext K)
    (theta : Finset (HeckeCharacter K))
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (A Cp Hp lower upper U T : ℝ) :
    PolynomialSystem.{0} K c.family.omega (targetCharacter K c) (recipeInductionSigma c) 2 :=
  universalPolynomialSystem.{0}
    (recipeRankedAnnulusReflectionPrimitive c theta ground engine reflection (recipeInductionSigma c)
      (recipeInductionSigma c / 16) A Cp Hp lower upper U T)
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) c.geometry.slots
    (recipeInduction_budget (c := c)).1

variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- The unchanged source node, now with its proved scheduled support.
The original highest-order source profile estimate is retained. -/
structure RecipeRankedAnnulusReflectionRootData
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma padding A C H lower upper : ℝ)
    {Z T : ℝ} (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) where
  root : ULift.{0} (UniversalNode
    (recipeRankedAnnulusReflectionPrimitive c (recipeThetaFamily R) ground engine reflection sigma padding
      A C H lower upper (momentBaseFor i) T) 2 padding c.geometry.slots)
  root_eq : root.down.val = recipeRoot R i s
  budget_one_le : 1 ≤ profileFamilyBudget C H T
  source_top_profile : ModelProfileControl (recipeRoot R i s).data
    (backwardProfileOrder ground engine reflection (6 * (widthBand sigma 2 + 1)))
    A C H lower upper T

/-- Strengthen only the actual source support invariant. Every original
node field, geometric proof and arithmetic calibration is retained. -/
def RecipeReflectionRootData.withRankedAnnulus
    {ground : ℕ} {engine reflection : ℕ → ℕ}
    {sigma padding A C H lower upper : ℝ} {Z T : ℝ}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (prepared : RecipeReflectionRootData R ground engine reflection
      sigma padding A C H lower upper i s)
    (hsigma : 0 < sigma) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (hT : 0 ≤ T) :
    RecipeRankedAnnulusReflectionRootData R ground engine reflection
      sigma padding A C H lower upper i s := by
  have htop : ModelProfileControl prepared.root.down.val.data
      (backwardProfileOrder ground engine reflection (6 * (widthBand sigma 2 + 1)))
      A C H lower upper T := by
    simpa only [prepared.root_eq] using prepared.source_top_profile
  have hprofile : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma 2 padding A
        (profileFamilyBudget C H T) lower upper)
      prepared.root.down.val.data prepared.root.down.val.parameters :=
    rankedAnnulusProfilePrimitive_of_top ground engine reflection
      hsigma prepared.root.down.property.width_le hlower hupper
      (modelProfileControl_fixed_budget htop (profileFamilyBudget_dominates C H hT))
  let primitive := recipeRankedAnnulusReflectionPrimitive c (recipeThetaFamily R) ground engine reflection
    sigma padding A C H lower upper (momentBaseFor i) T
  have hinvariant : UniversalNodeInvariant primitive 2 padding c.geometry.slots
      prepared.root.down.val := {
    length := prepared.root.down.property.length
    plain_left_nonneg := prepared.root.down.property.plain_left_nonneg
    plain_right_nonneg := prepared.root.down.property.plain_right_nonneg
    kappa_lower := prepared.root.down.property.kappa_lower
    kappa_upper := prepared.root.down.property.kappa_upper
    capacity := prepared.root.down.property.capacity
    width_nonneg := prepared.root.down.property.width_nonneg
    width_le := prepared.root.down.property.width_le
    slot_count := prepared.root.down.property.slot_count
    admissible := ⟨prepared.root.down.property.admissible.1, hprofile⟩
    centered_core := prepared.root.down.property.centered_core
    centered_left := prepared.root.down.property.centered_left
    centered_right := prepared.root.down.property.centered_right
    comparison_left := prepared.root.down.property.comparison_left
    comparison_right := prepared.root.down.property.comparison_right }
  exact {
    root := ⟨⟨prepared.root.down.val, hinvariant⟩⟩
    root_eq := prepared.root_eq
    budget_one_le := prepared.budget_one_le
    source_top_profile := prepared.source_top_profile }

/-- Constructed reflection-side data for one original root. Every
branch keeps its genuine children, kernel and remainder. There is no
strict step, final moment estimate or closed reduction among the fields. -/
structure RecipeRankedAnnulusReflectionFamilyData
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (A Cp Hp lower upper C H : ℝ)
    {Z T : ℝ} (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) where
  source : RecipeRankedAnnulusReflectionRootData R ground engine reflection (recipeInductionSigma c)
    (recipeInductionSigma c / 16) A Cp Hp lower upper i s
  scale : 1 < momentBaseFor i
  base : ∀ x : (recipeRankedAnnulusReflectionSystem c (recipeThetaFamily R) ground engine reflection A Cp Hp lower upper
      (momentBaseFor i) T).Label,
    x.down.val.width ≤ 16 * recipeInductionSigma c →
    x.down.val.parameters.n₁ + x.down.val.parameters.n₂ + x.down.val.data.geometry.totalLength ≤
      16 * recipeInductionSigma c + recipeInductionSigma c / 16 +
        (16 * recipeInductionSigma c) / 6 →
    Nonempty (TerminalComponents.{0} (x.down.val.normalizedEnergy (momentBaseFor i) 0)
      (momentBaseFor i) T C H (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
      (recipeInductionSigma c) (sourceReserve c.family.lamA))
  shortReflection : ∀ x : (recipeRankedAnnulusReflectionSystem c (recipeThetaFamily R) ground engine reflection A Cp Hp lower upper
      (momentBaseFor i) T).Label,
    16 * recipeInductionSigma c < x.down.val.width →
    x.down.val.totalLength ≤ x.down.val.width + recipeInductionSigma c / 16 →
    x.down.val.centered = false → 5 * x.down.val.width / 6 < x.down.val.totalLength →
    (x.down.val.parameters.n₁ ≤ x.down.val.width / 4 ∨
      x.down.val.parameters.n₂ ≤ x.down.val.width / 4) →
    Nonempty (ShortReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
      (recipeRankedAnnulusReflectionSystem c (recipeThetaFamily R) ground engine reflection A Cp Hp lower upper (momentBaseFor i) T)
      x (momentBaseFor i) (sourceReserve c.family.lamA) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) C ((1 + T) ^ H))
  outerReflection : ∀ x : (recipeRankedAnnulusReflectionSystem c (recipeThetaFamily R) ground engine reflection A Cp Hp lower upper
      (momentBaseFor i) T).Label,
    x.down.val.width + recipeInductionSigma c / 16 < x.down.val.totalLength →
    x.down.val.parameters.z = 0 → x.down.val.centered = false →
    Nonempty (OuterReflectionBranchAt (Ω := (ℕ × Bool) × ℝ)
      (recipeRankedAnnulusReflectionSystem c (recipeThetaFamily R) ground engine reflection A Cp Hp lower upper (momentBaseFor i) T)
      x (momentBaseFor i) (recipeInductionSigma c / 16) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) C ((1 + T) ^ H))

private def recipe_ranked_annulus_reflection_production
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) {upper : ℝ} (hupper : 2 ≤ upper) :=
  uniform_rankedAnnulusReflection_branches hcomplex c.family.omega (targetCharacter K c) c.geometry.slots
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    (sourceReserve c.family.lamA / 8) 2 (sourceReserve c.family.lamA / 4) 0
    (sourceReserve c.family.lamA / 8) (sourceReserve c.family.lamA / 8)
    (sourceReserve c.family.lamA / 2) (1 / 8)
    (recipeReflectionEulerParameter c.family.lamA) upper
    (recipeInduction_budget (c := c)).1 (by norm_num)
    (by have h := (recipeInduction_budget (c := c)).1; positivity)
    (by have h := (moment_mesh_engine_bounds c.family.lamA_pos).2.1; positivity) (by norm_num)
    (by have h := (moment_mesh_engine_bounds c.family.lamA_pos).2.1; positivity) (by norm_num)
    (by have h := (moment_mesh_engine_bounds c.family.lamA_pos).2.1; positivity)
    (by have h := (moment_mesh_engine_bounds c.family.lamA_pos).2.1; positivity)
    (by have h := (moment_mesh_engine_bounds c.family.lamA_pos).2.1; positivity)
    (by norm_num) (by norm_num) (recipeReflectionEulerParameter_pos c.family.lamA_pos)
    (recipeReflectionEulerParameter_budget c.family.lamA_pos) hupper

/-- The full reflection-side family is uniform before every original
scale and height, and therefore before tau. Both target projections use
the same annulus, analytic orders, source envelope, scalar, height degree
and physical cutoff. The source itself is never rescaled or restricted
to the padded core. -/
theorem recipeRankedAnnulusReflectionFamily_preparation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    {lengthBound : ℝ} (hgeom : R.MomentGeometry lengthBound)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R))
    (w : InfinitePlace K) (hψ : heckeRadialParameter K w (targetCharacter K c) = 0) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∃ decay : ℝ, 1 < decay ∧ ∃ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) ∧
      ∀ (ground : ℕ) (engine : ℕ → ℕ), 1 ≤ ground →
      ∃ Cp Hp C H Z₀ : ℝ,
      0 < Cp ∧ 0 ≤ Hp ∧ 0 ≤ C ∧ 0 ≤ H ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ T : ℝ, 0 ≤ T →
      ∀ (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
        (s : SixthUnitClasses K (places K c)),
      Nonempty (RecipeRankedAnnulusReflectionFamilyData R ground engine reflection
        decay Cp Hp lower upper C H i.noSlots s) ∧
      ((∀ j : Fin R.family.presentationCount,
          FiniteOrder (R.family.presentation j).plainBackground →
            (R.family.presentation j).plainBackground⁻¹ ∈ (R.family.presentation j).theta) →
        pairedCapacityFor i →
        Nonempty (RecipeRankedAnnulusReflectionFamilyData R ground engine reflection
          decay Cp Hp lower upper C H i s)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval, hsource⟩ :=
    recipeReflectionRoot_preparation R hgeom hprofiles w hψ
  obtain ⟨decay, hdecay, _hδdecay, reflection, hreflection, hbranches⟩ :=
    recipe_ranked_annulus_reflection_production (c := c) hcomplex hupper
  refine ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
    decay, hdecay, reflection, hreflection, ?_⟩
  intro ground engine hground
  have hσ := (recipeInduction_budget (c := c)).1
  obtain ⟨Cp, Hp, hCp, _hminimumCp, hHp, roots⟩ := hsource ground engine reflection
    (recipeInductionSigma c) (recipeInductionSigma c / 16) decay 0 hσ (by linarith)
  obtain ⟨C, H, hC, hH, produce⟩ := hbranches ground engine Cp Hp lower
    (16 * recipeInductionSigma c) (sourceReserve c.family.lamA)
    hground hCp.le hHp hlower hlowerSmall
  obtain ⟨U₀, hU₀, hthreshold⟩ := recipe_source_moving_conductor_threshold R
  let Z₀ := U₀ ^ (16 : ℕ)
  have hZ₀ : 1 ≤ Z₀ := one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 2).trans hU₀)
  refine ⟨Cp, Hp, C, H, Z₀, hCp, hHp, hC, hH, hZ₀, ?_⟩
  intro Z hZ T hT
  have hUbase (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
      U₀ ≤ momentBaseFor i :=
    _root_.ExpansionRecipe.shell_base_ge_of_physical_cutoff
      ((by norm_num : (1 : ℝ) ≤ 2).trans hU₀) hZ (recipeMoment_shell_lower i)
  have hmassLoss : sourceReserve c.family.lamA / 2 + 2 * (sourceReserve c.family.lamA / 4) ≤
      recipeInductionEdgeLoss c := by
    change sourceReserve c.family.lamA / 2 + 2 * (sourceReserve c.family.lamA / 4) ≤
      sourceReserve c.family.lamA + HeckePort.Schedule.momentMeshValue c.family.lamA +
        sourceReserve c.family.lamA
    rw [(recipe_reflection_loss_bounds c.family.lamA_pos).1]
    exact (recipe_reflection_loss_bounds c.family.lamA_pos).2.1
  have hterminalLoss : -2 * (0 : ℝ) ≤ recipeInductionTerminalLoss c := by
    simpa only [recipeInductionTerminalLoss, recipeInductionSigma, mul_zero, neg_zero] using
      (recipe_reflection_loss_bounds c.family.lamA_pos).2.2
  have hr : 0 < sourceReserve c.family.lamA :=
    (moment_mesh_engine_bounds c.family.lamA_pos).2.1
  have hgeometry := recipe_reflection_geometry_bounds c.family.lamA_pos
    (le_refl (sourceReserve c.family.lamA / 8))
  have build (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
      (s : SixthUnitClasses K (places K c))
      (prepared : RecipeReflectionRootData R ground engine reflection (recipeInductionSigma c)
        (recipeInductionSigma c / 16) decay Cp Hp lower upper i s) :
      Nonempty (RecipeRankedAnnulusReflectionFamilyData R ground engine reflection
        decay Cp Hp lower upper C H i s) := by
    have hU : 1 < momentBaseFor i :=
      (by norm_num : (1 : ℝ) < 2).trans_le (hU₀.trans (hUbase i))
    obtain ⟨hfixed, hround⟩ := hthreshold (momentBaseFor i) (hUbase i)
    have nodes := produce (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c)
      hmassLoss hterminalLoss T hT (places K c) (probeData K c) (momentRowCharacters K c)
      (recipeThetaFamily R) (momentBaseFor i) (sourceReserve c.family.lamA / 8) hU (by positivity) le_rfl hfixed hround
    refine ⟨{ source := RecipeReflectionRootData.withRankedAnnulus R prepared hσ
        hlower.le (by linarith) hT, scale := hU, base := ?_,
      shortReflection := ?_, outerReflection := ?_ }⟩
    · intro x _hwidth hlength
      exact (nodes x x.down.property.slot_length_le_bound).1 hlength
    · intro x hwidth hcore hordinary hlarge hshort
      have hmargins := recipe_reflection_comparison_floor c.family.lamA_pos hwidth.le
      exact ((nodes x x.down.property.slot_length_le_bound).2 hordinary).1
        (sourceReserve c.family.lamA) hgeometry.1 hmargins.1 hshort hcore hmargins.2 hlarge
    · intro x hnoncore hzero hordinary
      exact ((nodes x x.down.property.slot_length_le_bound).2 hordinary).2
        hnoncore hzero hgeometry.2
  intro i s
  obtain ⟨zero, positive⟩ := roots Z T hT i s
  constructor
  · obtain ⟨prepared⟩ := zero
    exact build i.noSlots s prepared
  · intro hfinite hcapacity
    obtain ⟨prepared⟩ := positive hfinite hcapacity
    exact build i s prepared

end HeckeSkeleton.Moments.EngineInduction.Source
