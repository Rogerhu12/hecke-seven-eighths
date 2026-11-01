import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCompleteSourceFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinSourcePreparation
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeStrictEngineBox
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StrictChildRank

/-!
# Constructing the exact original source of every strict call

The prepared node's genuine rank chooses the backward Euler order and
positive annulus. Mellin normalization constructs its literal source,
and restriction to its exact parent rows supplies the full joint budget.
This record contains only those original arithmetic and profile inputs;
it contains no engine output, child energy or recursive inequality.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open Expansion.Project EngineStep

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]
variable {Ω : Type} [MeasurableSpace Ω]

def actualStrictProfileRange (c : TargetContext K) (lower upper : ℝ)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) : StrictProfileRange :=
  StrictProfileRange.ofSchedule lower upper hlower hinterval (recipeStrictRankBound c)

def actualStrictEngineOrder (c : TargetContext K) (lower upper : ℝ)
    (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (extraOrders : Finset (ℕ × ℕ)) (A : ℝ) : ℕ → ℕ :=
  (actualStrictProfileRange c lower upper hlower hinterval).engineOrder
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extraOrders A

variable (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper)
variable (extraOrders : Finset (ℕ × ℕ)) (ground : ℕ) (reflection : ℕ → ℕ)
variable (A Cp Hp U T : ℝ)

local notation "r" => actualStrictProfileRange c lower upper hlower hinterval
local notation "engine" => actualStrictEngineOrder c lower upper hlower hinterval extraOrders A
local notation "S" => recipeDataReflectionSystem c
  (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
  ground engine reflection A Cp Hp lower upper U T

variable (x : (S).Label)

local notation "n" => (S).node x
local notation "rank" => parameterCoreRank (recipeInductionSigma c) 2
  (recipeInductionSigma c / 16) (n).parameters
local notation "J" => backwardProfileOrder ground engine reflection (rank - 1)
local notation "lo" => clippedAnnulusLower lower upper (recipeStrictRankBound c) rank
local notation "hi" => rankedAnnulusUpper upper (recipeStrictRankBound c) rank
local notation "bounds" => clippedAnnulus_bounds hlower hinterval (recipeStrictRankBound c) rank
local notation "P" => profileFamilyBudget Cp Hp T
local notation "mellinJ" => (r).mellinOrder
  (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extraOrders J A
local notation "inputOrders" => (r).inputOrders
  (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extraOrders J A
local notation "amplitude" => (r).amplitude
  (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extraOrders J A

/-- The exact predecessor order is paid by the current node's already
proved profile primitive. No same-order closure assertion is required. -/
theorem actualStrictNode_profile
    (domain : PairedEngineDomain (n).centered (n).data (n).parameters U
      (U ^ (n).comparison₁) (U ^ (n).comparison₂)
      (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)) :
    ModelProfileControl (n).data (engine J) A P 0 lo hi 0 := by
  have hp : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection (recipeInductionSigma c) 2
        (recipeInductionSigma c / 16) A P lower upper) (n).data (n).parameters :=
    x.down.property.admissible.2.2.2.2
  rw [rankedAnnulusProfilePrimitive_iff] at hp
  apply modelProfileControl_mono_order hp
  exact (backwardProfileOrder_parent_orders ground engine reflection
    (parameterCoreRank_pos_of_strict_width (recipeInduction_budget (c := c)).1
      domain.width_floor)).1

/-- The complete source witness is the actual invariant carried by
the prepared label, including both budgets for its same moving recipe. -/
def actualStrictNode_complete : CompleteSourceBudgetData c
    (canonicalDetectorTheta K (targetCharacter K c)) U (n).data
    (pairedInvariantParameters (n).parameters) :=
  Classical.choice (recipeDataReflectionSystem_data
    (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
    ground engine reflection A Cp Hp lower upper U T x)

variable (hA : 0 ≤ A) (hP : 1 ≤ P)

def actualStrictMellinNode (frequency : ℝ × ℝ) :
    Node K c.family.omega (targetCharacter K c) :=
  (n).mellinStrictModel (Ω := Ω) c.geometry.slots mellinJ
    A lo hi hA (bounds).1 (bounds).2 P hP frequency

local notation "model" => actualStrictMellinNode (Ω := Ω) lower upper hlower hinterval
  extraOrders ground reflection A Cp Hp U T x hA hP

/-- Only original input data occur in this record. The full joint
budget is on the exact localized allowed rows of the actual parent. -/
structure ActualStrictSource (frequency : ℝ × ℝ) where
  complete : CompleteSourceBudgetData c
    (canonicalDetectorTheta K (targetCharacter K c)) U
    (localizeOriginalParent (model frequency).data (n).parameters U)
    (pairedInvariantParameters (n).parameters)
  fullBudget : complete.source.recipe.FullJointBudget U ((n).parameters.m + (n).parameters.q)
  normRecipe : NormProfileRecipe
    (fun _ : PUnit => localizeOriginalParent (model frequency).data (n).parameters U)
  profiles : RawProfileWindow Set.univ Set.univ (Set.Icc (lo / 2) (2 * hi))
    inputOrders
    (localizeOriginalParent (model frequency).data (n).parameters U)
    amplitude

/-- The source, its exact norms, representatives and support are all
constructed from the actual Mellin theorem, uniformly in frequency. -/
def actualStrictSource
    (domain : PairedEngineDomain (n).centered (n).data (n).parameters U
      (U ^ (n).comparison₁) (U ^ (n).comparison₂)
      (16 * recipeInductionSigma c) (recipeInductionSigma c / 16))
    (frequency : ℝ × ℝ) :
    ActualStrictSource (Ω := Ω) lower upper hlower hinterval extraOrders ground reflection
      A Cp Hp U T x hA hP frequency := by
  let D := actualStrictNode_complete lower upper hlower hinterval extraOrders ground reflection
    A Cp Hp U T x
  obtain ⟨raw⟩ := mellinStrictModel_rawWindow (Ω := Ω) r extraOrders J n c.geometry.slots
    A lo hi hA (bounds).1 (bounds).2
    (StrictProfileRange.expanded_contains_schedule lower upper hlower hinterval
      (recipeStrictRankBound c) rank)
    P hP U (zero_lt_one.trans domain.scale) x.down.property.slot_count
    (actualStrictNode_profile lower upper hlower hinterval extraOrders ground reflection
      A Cp Hp U T x domain) frequency
  exact {
    complete := D.localizedMellinSource (Ω := Ω) n c.geometry.slots
      mellinJ A lo hi hA (bounds).1 (bounds).2 P hP frequency
    fullBudget := D.localizedMellinSource_fullJointBudget (Ω := Ω) n c.geometry.slots
      mellinJ A lo hi hA (bounds).1 (bounds).2 P hP frequency
    normRecipe := (n).localizedMellinNormProfileRecipe (Ω := Ω) c.geometry.slots
      mellinJ A lo hi hA (bounds).1 (bounds).2 P hP frequency U
    profiles := localizedRawProfileWindow raw (n).parameters U }

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualStrictNode_profile
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualStrictSource
