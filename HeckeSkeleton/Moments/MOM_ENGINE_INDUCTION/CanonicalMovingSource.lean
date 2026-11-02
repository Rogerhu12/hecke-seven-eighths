import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# The same actual selected moving children are complete recursive sources

The original moving-row recipe is transported through the capacity
choice already made by the canonical normalized pair family. Its theta,
slots and final frozen time give the complete source dictionary needed
for the next Mellin and parent-source construction. No child is selected
again, and no phase, norm-profile recipe, or energy estimate is assumed.

The displayed q budget and the full joint mask budget remain separate
facts about precisely this transported recipe. Removing the last slot
does not invalidate either budget because the original canonical facts
hold on every allowed row.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {U : ℝ} {theta : Finset (HeckeCharacter K)}
variable {parent : MomentData K c.family.omega (targetCharacter K c)}
variable {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

variable (family : EngineStep.ActualNormalizedPairFamily
  (axiomChoice K c).A (complexEmbedding K c) V Λ c.family.omega (targetCharacter K c) U)
variable (labels : Finset Λ)
variable (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
variable (rows : family.MovingRowInputs
  (P := probeData K c) (R := momentRowCharacters K c) labels)
variable (htheta : parent.theta = theta)

/-- The left child uses the same original factor recipe and frozen
profiles that occur in the actual canonical output. -/
def movingLeftCompleteSourceData (b : family.active labels) (ξ : V) :
    CompleteSourceData c theta (family.leftData labels b ξ) where
  recipe := (rows.leftRecipe b).at ξ
  theta_eq := (geometry.left_theta b ξ).trans htheta
  slot_characters j := htheta ▸ geometry.left_slot_characters b ξ j
  timeIndependent := by
    rw [family.leftData_eq_frozen_normalized]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The right side keeps its own original factor recipe and the same
selected capacity deletion, rather than copying the left arithmetic. -/
def movingRightCompleteSourceData (b : family.active labels) (ξ : V) :
    CompleteSourceData c theta (family.rightData labels b ξ) where
  recipe := (rows.rightRecipe b).at ξ
  theta_eq := (geometry.right_theta b ξ).trans htheta
  slot_characters j := htheta ▸ geometry.right_slot_characters b ξ j
  timeIndependent := by
    rw [family.rightData_eq_frozen_normalized]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem movingLeftCompleteSourceData_supportBudget (b : family.active labels) (ξ : V) :
    (movingLeftCompleteSourceData family labels geometry rows htheta b ξ).recipe.SupportBudget
      U (family.leftParameters labels b).q :=
  (rows.leftRecipe b).at_supportBudget _ _ (rows.left_supportBudget b) ξ

theorem movingRightCompleteSourceData_supportBudget (b : family.active labels) (ξ : V) :
    (movingRightCompleteSourceData family labels geometry rows htheta b ξ).recipe.SupportBudget
      U (family.rightParameters labels b).q :=
  (rows.rightRecipe b).at_supportBudget _ _ (rows.right_supportBudget b) ξ

theorem movingLeftCompleteSourceData_fullJointBudget (b : family.active labels) (ξ : V) :
    (movingLeftCompleteSourceData family labels geometry rows htheta b ξ).recipe.FullJointBudget
      U ((family.leftParameters labels b).m + (family.leftParameters labels b).q) :=
  (rows.leftRecipe b).at_fullJointBudget _ _ (rows.left_fullJointBudget b) ξ

theorem movingRightCompleteSourceData_fullJointBudget (b : family.active labels) (ξ : V) :
    (movingRightCompleteSourceData family labels geometry rows htheta b ξ).recipe.FullJointBudget
      U ((family.rightParameters labels b).m + (family.rightParameters labels b).q) :=
  (rows.rightRecipe b).at_fullJointBudget _ _ (rows.right_fullJointBudget b) ξ

end HeckeSkeleton.Moments.EngineInduction
