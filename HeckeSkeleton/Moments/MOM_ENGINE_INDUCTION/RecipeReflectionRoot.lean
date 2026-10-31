import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionPrimitiveFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalSourceRoot

/-!
# One source preparation for every literal reflection root

The original recipe is fixed throughout. Its common annulus is selected
before the analytic order functions, and its highest finite rank order
is selected before the profile constants. Those constants precede every
moving height, source index and sector, hence also every later choice of
tau. The original root is placed in the universal family unchanged.

Both the unrestricted no-slot root and every capacity-eligible positive
root use these same constants. The no-slot entrance needs only the true
radial anchor. The positive entrance additionally uses the actual finite
background absorption in each original presentation. No core condition,
reflection estimate, local-step conclusion or final moment bound is an
input or a field of the preparation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

/-- The actual reflection portion of the source's primitive family at
one scale and height. The source budget is shared by its unchanged root
and all genuinely normalized descendants. -/
def recipeReflectionPrimitive (c : TargetContext K)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ padding A C H lower upper U T : ℝ) :
    MomentData K c.family.omega (targetCharacter K c) → PairedInvariantParameters → Prop :=
  reflectionProfilePrimitive (places K c) (probeData K c) (momentRowCharacters K c) U
    ground engine reflection σ 2 padding A (profileFamilyBudget C H T) lower upper

variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- A literal source label with its original highest-order profile
estimate. The subtype itself contains the actual slot-count cap,
nonnegative plain lengths, width in [0,2], original capacity and the
complete reflection arithmetic/profile primitive. -/
structure RecipeReflectionRootData
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ padding A C H lower upper : ℝ)
    {Z T : ℝ} (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) where
  root : ULift.{0} (UniversalNode
    (recipeReflectionPrimitive c ground engine reflection σ padding A C H lower upper
      (momentBaseFor i) T) 2 padding c.geometry.slots)
  root_eq : root.down.val = recipeRoot R i s
  budget_one_le : 1 ≤ profileFamilyBudget C H T
  source_top_profile : ModelProfileControl (recipeRoot R i s).data
    (backwardProfileOrder ground engine reflection (6 * (widthBand σ 2 + 1)))
    A C H lower upper T

private def prepareRecipeReflectionRoot
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (σ padding A C H lower upper : ℝ) (hσ : 0 < σ)
    {lengthBound Z T : ℝ} (hgeom : R.MomentGeometry lengthBound)
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) (hT : 0 ≤ T)
    (hP : 1 ≤ profileFamilyBudget C H T)
    (hcapacity : (recipeRoot R i s).parameters.z = 0 ∨ pairedCapacityFor i)
    (harithmetic : admissibleOfInvariant
      (reflectionArithmeticPrimitive (places K c) (probeData K c) (momentRowCharacters K c)
        (momentBaseFor i)) (recipeRoot R i s).data (recipeRoot R i s).parameters)
    (htop : ModelProfileControl (recipeRoot R i s).data
      (backwardProfileOrder ground engine reflection (6 * (widthBand σ 2 + 1)))
      A C H lower upper T) :
    RecipeReflectionRootData R ground engine reflection σ padding A C H lower upper i s := by
  have hrank : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ 2 padding A
        (profileFamilyBudget C H T) lower upper)
      (recipeRoot R i s).data (recipeRoot R i s).parameters :=
    rankedProfilePrimitive_of_top ground engine reflection hσ
      (recipeRoot_width_range R i s).2
      (modelProfileControl_fixed_budget htop (profileFamilyBudget_dominates C H hT))
  let primitive := recipeReflectionPrimitive c ground engine reflection
    σ padding A C H lower upper (momentBaseFor i) T
  have hadmissible : admissibleOfInvariant primitive
      (recipeRoot R i s).data (recipeRoot R i s).parameters := ⟨harithmetic, hrank⟩
  exact {
    root := ⟨recipeUniversalRoot R i s primitive padding hgeom hcapacity hadmissible⟩
    root_eq := rfl
    budget_one_le := hP
    source_top_profile := htop }

/-- The prepared subtype is exactly a label of the same actual
polynomial system used by finite-rank induction, with no energy cast. -/
def RecipeReflectionRootData.label
    {ground : ℕ} {engine reflection : ℕ → ℕ}
    {σ padding A C H lower upper : ℝ} {Z T : ℝ}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (prepared : RecipeReflectionRootData R ground engine reflection
      σ padding A C H lower upper i s) (hσ : 0 < σ) :
    (universalPolynomialSystem.{0}
      (recipeReflectionPrimitive c ground engine reflection σ padding A C H lower upper
        (momentBaseFor i) T) σ 2 padding c.geometry.slots hσ).Label := prepared.root

theorem RecipeReflectionRootData.label_eq
    {ground : ℕ} {engine reflection : ℕ → ℕ}
    {σ padding A C H lower upper : ℝ} {Z T : ℝ}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (prepared : RecipeReflectionRootData R ground engine reflection
      σ padding A C H lower upper i s) (hσ : 0 < σ) :
    (universalPolynomialSystem.{0}
      (recipeReflectionPrimitive c ground engine reflection σ padding A C H lower upper
        (momentBaseFor i) T) σ 2 padding c.geometry.slots hσ).node
          (RecipeReflectionRootData.label R prepared hσ) =
      recipeRoot R i s := prepared.root_eq

/-- One annulus and one original height envelope prepare both target
projections. The full original index set is quantified before the
optional positive capacity; no root is restricted to the padded core.
The positive presentation exclusion is deliberately not required for
the zero-slot member of the same preparation. -/
theorem recipeReflectionRoot_preparation {lengthBound : ℝ}
    (hgeom : R.MomentGeometry lengthBound)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R))
    (w : InfinitePlace K) (hψ : heckeRadialParameter K w (targetCharacter K c) = 0) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∀ (ground : ℕ) (engine reflection : ℕ → ℕ) (σ padding A : ℝ),
      0 < σ → 0 ≤ A → ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
      ∀ Z T : ℝ, 0 ≤ T →
      ∀ (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
        (s : SixthUnitClasses K (places K c)),
      Nonempty (RecipeReflectionRootData R ground engine reflection
        σ padding A C H lower upper i.noSlots s) ∧
      ((∀ j : Fin R.family.presentationCount,
          FiniteOrder (R.family.presentation j).plainBackground →
            (R.family.presentation j).plainBackground⁻¹ ∈ (R.family.presentation j).theta) →
        pairedCapacityFor i →
        Nonempty (RecipeReflectionRootData R ground engine reflection
          σ padding A C H lower upper i s)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval, hprofiles⟩ :=
    recipeRoot_fixed_annulus_profiles R hgeom hprofiles
  refine ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval, ?_⟩
  intro ground engine reflection σ padding A hσ hA
  obtain ⟨C, H, hC, hH, htop⟩ := hprofiles
    (backwardProfileOrder ground engine reflection (6 * (widthBand σ 2 + 1))) A hA
  refine ⟨C, H, hC, hH, ?_⟩
  intro Z T hT i s
  have hP : 1 ≤ profileFamilyBudget C H T := profileFamilyBudget_one_le hC.le hH hT
  constructor
  · exact ⟨prepareRecipeReflectionRoot R ground engine reflection σ padding A C H lower upper hσ
      hgeom i.noSlots s hT hP (Or.inl (recipeRoot_noSlots_zero R i s))
      (recipeRoot_noSlots_reflectionArithmeticPrimitive R i s w hψ) (htop Z T i.noSlots s)⟩
  · intro hfinite hcapacity
    exact ⟨prepareRecipeReflectionRoot R ground engine reflection σ padding A C H lower upper hσ
      hgeom i s hT hP (Or.inr hcapacity)
      (recipeRoot_reflectionArithmeticPrimitive R i s w hψ hfinite) (htop Z T i s)⟩

end HeckeSkeleton.Moments.EngineInduction.Source
