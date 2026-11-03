import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceBudgets
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeMellinFamily
import HeckeSkeleton.ExpansionModels.ActualRowEligibility
import Expansion.CanonicalDetectorCharacters
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileControl

/-!
# The actual fixed-theta source enters the complete recursive family

The same original physical recipe supplies its complete ideal characters,
common zero mask, finite theta, actual profile formulas, and all-scale
length and parameter bounds. Both physical presentations have the same
canonical theta, and every initial slot coefficient is the identity.

The complete moving-row primitive is produced at the original root and
preserved by the literal reflection and Mellin data constructors. The
unrestricted zero-slot and capacity-eligible positive roots therefore
enter one recursive family with the original fixed kappa, mesh and
common profile-order schedule. All constants precede moving indices.

The strict callback is the remaining canonical engine step. This file
discharges the actual-source arithmetic, geometry, finite-background and
profile inputs; it does not take any final moment estimate as a premise.
The source and profile interfaces are consumed from their owners at
896cec08ff832c5fcf136adcc12f0239e7ab9728.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project
open scoped Classical

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- The actual theta set is fixed before every source scale, witness,
unit sector, recursive node and transform frequency. -/
def actualCompleteSourcePrimitive :
    MomentData K c.family.omega (targetCharacter K c) → Prop :=
  completeSourcePrimitive c (canonicalDetectorTheta K (targetCharacter K c))

/-- Original source data supply the full primitive, including on the
unrestricted no-slot index. No arithmetic calibration premise is added. -/
theorem actualRecipe_completeSourcePrimitive {Z T : ℝ}
    (i : SourceMomentIndexFor K c
      (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T)
    (s : SixthUnitClasses K (places K c)) :
    actualCompleteSourcePrimitive c (recipeRoot (expansionRecipeRaw K c) i s).data := by
  exact ⟨recipeRootCompleteSourceData (expansionRecipeRaw K c) i s
    (canonicalDetectorTheta K (targetCharacter K c)) (actualRecipeMoment_theta K c i s)
    (by
      intro j
      change (1 : HeckeCharacter K) ∈ canonicalDetectorTheta K (targetCharacter K c)
      exact one_mem_canonicalDetectorTheta K (targetCharacter K c))⟩

/-- The same actual recipe retains its displayed-support and joint
row/mask bounds at the actual scale and invariant parameters. -/
def actualCompleteSourceBudgetPrimitive :
    ℝ → MomentData K c.family.omega (targetCharacter K c) → PairedInvariantParameters → Prop :=
  completeSourceBudgetPrimitive c (canonicalDetectorTheta K (targetCharacter K c))

/-- Both arithmetic budgets follow from the original finite source
rows and its empty displayed moving list, including the no-slot root. -/
theorem actualRecipe_completeSourceBudgetPrimitive {Z T : ℝ}
    (i : SourceMomentIndexFor K c
      (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T)
    (s : SixthUnitClasses K (places K c)) :
    actualCompleteSourceBudgetPrimitive c (momentBaseFor i)
      (recipeRoot (expansionRecipeRaw K c) i s).data
      (pairedInvariantParameters (recipeRoot (expansionRecipeRaw K c) i s).parameters) := by
  exact ⟨recipeRootCompleteSourceBudgetData (expansionRecipeRaw K c) i s
    (canonicalDetectorTheta K (targetCharacter K c)) (actualRecipeMoment_theta K c i s)
    (by
      intro j
      change (1 : HeckeCharacter K) ∈ canonicalDetectorTheta K (targetCharacter K c)
      exact one_mem_canonicalDetectorTheta K (targetCharacter K c))⟩

private theorem actual_complete_finite_backgrounds :
    ∀ j : Fin (expansionRecipeRaw K c).family.presentationCount,
      FiniteOrder ((expansionRecipeRaw K c).family.presentation j).plainBackground →
        ((expansionRecipeRaw K c).family.presentation j).plainBackground⁻¹ ∈
          ((expansionRecipeRaw K c).family.presentation j).theta := by
  intro j hj
  exact canonicalDetectorPresentation_plain_inverse_mem K (targetCharacter K c) j hj

/-- The genuine reflection side now has complete-row/fixed-remaining
children with the original theta and mesh. All source arithmetic and
geometry premises of the generic factory are discharged here. -/
theorem actualRecipeCompleteReflectionFamily_preparation :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∃ decay : ℝ, 1 < decay ∧ ∃ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) ∧
      ∀ (ground : ℕ) (engine : ℕ → ℕ), 1 ≤ ground → ∀ minimumCp : ℝ,
      ∃ Cp Hp C H Z₀ : ℝ,
      0 < Cp ∧ minimumCp ≤ Cp ∧ 0 ≤ Hp ∧ 0 ≤ C ∧ 0 ≤ H ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ T : ℝ, 0 ≤ T →
      ∀ (i : SourceMomentIndexFor K c
          (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T)
        (s : SixthUnitClasses K (places K c)),
      Nonempty (RecipeDataReflectionFamilyData (expansionRecipeRaw K c)
        (actualCompleteSourceBudgetPrimitive c) ground engine reflection
        decay Cp Hp lower upper C H i.noSlots s) ∧
      (pairedCapacityFor i →
        Nonempty (RecipeDataReflectionFamilyData (expansionRecipeRaw K c)
          (actualCompleteSourceBudgetPrimitive c) ground engine reflection
          decay Cp Hp lower upper C H i s)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
      decay, hdecay, reflection, hreflection, hfamilies⟩ :=
    recipeDataReflectionFamily_preparation (expansionRecipeRaw K c)
      (actualCompleteSourceBudgetPrimitive c)
      (fun U => completeSourceBudgetPrimitive_fixedLine c
        (canonicalDetectorTheta K (targetCharacter K c)) U)
      (fun _ _ i s => actualRecipe_completeSourceBudgetPrimitive c i s)
      (isComplex_of_family K c) (expansionRecipeRaw_geometry K c)
      (UniformAmplify.actual_source_profile_control K c)
      (normNormalizationPlace K) (targetCharacter_radial_zero K c)
  refine ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
    decay, hdecay, reflection, hreflection, ?_⟩
  intro ground engine hground minimumCp
  obtain ⟨Cp, Hp, C, H, Z₀, hCp, hminimumCp, hHp, hC, hH, hZ₀, hdata⟩ :=
    hfamilies ground engine hground minimumCp
  refine ⟨Cp, Hp, C, H, Z₀, hCp, hminimumCp, hHp, hC, hH, hZ₀, ?_⟩
  intro Z hZ T hT i s
  have h := hdata Z hZ T hT i s
  exact ⟨h.1, h.2 (actual_complete_finite_backgrounds c)⟩

/-- The concrete primitive supplies every remaining arithmetic/root
input to the existing scalar assembly. Only its original actual strict
output callback remains visible; no second provider contract is added. -/
theorem actualRecipeCompleteMellinFamily_preparation :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∃ decay : ℝ, 1 < decay ∧ ∃ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) ∧
      ∀ (ground : ℕ) (engine : ℕ → ℕ), 1 ≤ ground → ∀ minimumCp : ℝ,
      ∃ Cp Hp : ℝ, 0 < Cp ∧ minimumCp ≤ Cp ∧ 0 ≤ Hp ∧
      ∀ (Ωengine : Type) [MeasurableSpace Ωengine],
      ∀ strict : RecipeMellinStrictFamily Ωengine (expansionRecipeRaw K c)
        (actualCompleteSourceBudgetPrimitive c) ground engine reflection decay Cp Hp lower upper,
      Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
        (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
      Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
        (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
      decay, hdecay, reflection, hreflection, hfamilies⟩ :=
    recipeMellinFamily_preparation (expansionRecipeRaw K c)
      (actualCompleteSourceBudgetPrimitive c)
      (fun U => completeSourceBudgetPrimitive_fixedLine c
        (canonicalDetectorTheta K (targetCharacter K c)) U)
      (fun _ _ i s => actualRecipe_completeSourceBudgetPrimitive c i s)
      (isComplex_of_family K c) (expansionRecipeRaw_geometry K c)
      (UniformAmplify.actual_source_profile_control K c)
      (normNormalizationPlace K) (targetCharacter_radial_zero K c)
  refine ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
    decay, hdecay, reflection, hreflection, ?_⟩
  intro ground engine hground minimumCp
  obtain ⟨Cp, Hp, hCp, hminimumCp, hHp, hdata⟩ := hfamilies ground engine hground minimumCp
  refine ⟨Cp, Hp, hCp, hminimumCp, hHp, ?_⟩
  intro Ωengine instΩengine strict
  have h := hdata Ωengine strict
  exact ⟨h.1, h.2 (actual_complete_finite_backgrounds c)⟩

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipe_completeSourcePrimitive
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipe_completeSourceBudgetPrimitive
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeCompleteReflectionFamily_preparation
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeCompleteMellinFamily_preparation
