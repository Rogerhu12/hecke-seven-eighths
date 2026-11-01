import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualStrictSource
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshPairedEngineStep
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineAnnulus

/-!
# Selecting every original source order before the backward schedule

The finite union below contains the genuine exceptional-volume orders
of all numerical rank boxes. It is selected before the backward Euler
order function. The current child Euler orders and that same union are
then the public producer's output request, so its internally added
volume orders do not force any new choice after a node is supplied.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open Expansion.Project EngineStep CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)
variable (lower upper : ℝ) (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2)
variable (hupper : 2 ≤ upper)

/-- Only the analytic annulus certificate is enlarged. All original
mesh, width, capacity, step and loss quantities are retained. -/
def actualStrictAnnularBox (rank : ℕ) : Box :=
  CanonicalPrimitiveEngineAnnulus.annularBox
    (recipeStrictEngineBox c lower upper hlower hlowerSmall hupper rank)

local notation "box" => actualStrictAnnularBox c lower upper hlower hlowerSmall hupper
local notation "theta" => canonicalDetectorTheta K (targetCharacter K c)

variable (volume : ∀ rank : ℕ, CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  (targetCharacter K c) theta (Set.Icc (box rank).lo (box rank).hi))

def actualStrictVolumeOrders (rank : ℕ) : Finset (ℕ × ℕ) :=
  CanonicalPrimitiveEngineSetup.volumeOrders
    (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
    (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS)
    (box rank) theta (volume rank)

/-- This fixed finite set is chosen before the rank-dependent Euler
requirements, common height budget and every moving source. -/
def actualStrictAllVolumeOrders : Finset (ℕ × ℕ) :=
  (Finset.range (recipeStrictRankBound c + 1)).biUnion
    (actualStrictVolumeOrders c lower upper hlower hlowerSmall hupper volume)

theorem actualStrictVolumeOrders_subset (rank : ℕ) (hrank : rank ≤ recipeStrictRankBound c) :
    actualStrictVolumeOrders c lower upper hlower hlowerSmall hupper volume rank ⊆
      actualStrictAllVolumeOrders c lower upper hlower hlowerSmall hupper volume := by
  intro order horder
  exact Finset.mem_biUnion.mpr
    ⟨rank, Finset.mem_range.mpr (by omega), horder⟩

variable (hinterval : lower ≤ upper) (J : ℕ) (A : ℝ)

local notation "r" => actualStrictProfileRange c lower upper hlower hinterval
local notation "extra" => actualStrictAllVolumeOrders c lower upper hlower hlowerSmall hupper volume

/-- The genuine child Euler requirements plus the already chosen
volume union. Prime orders are inserted by the original producer. -/
def actualStrictOutputOrders : Finset (ℕ × ℕ) :=
  eulerSchwartzOrders (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (r).lower (r).upper (r).lower_pos J A ∪ extra

/-- Internally adding the current volume orders causes no loss of
derivative order: they already belong to the preselected finite union. -/
theorem actualStrictOrders_eq (rank : ℕ) (hrank : rank ≤ recipeStrictRankBound c) :
    OriginalMeshPairedStep.orders
      (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
      (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS)
      (box rank) theta
      (actualStrictOutputOrders c lower upper hlower hlowerSmall hupper volume hinterval J A)
      (volume rank) =
      (r).childOrders (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extra J A := by
  have hsub := (actualStrictVolumeOrders_subset c lower upper hlower hlowerSmall hupper
    volume rank hrank).trans
    (Finset.subset_union_right : extra ⊆
      actualStrictOutputOrders c lower upper hlower hlowerSmall hupper volume hinterval J A)
  unfold OriginalMeshPairedStep.orders CanonicalPrimitiveEngineSetup.orders
    CanonicalPrimitiveEngineProfileOrders.orders StrictProfileRange.childOrders
  rw [Finset.union_eq_left.mpr hsub]
  rfl

/-- The actual normalized Mellin input supplies the public producer's
entire required profile window, with no additional derivative callback. -/
theorem actualStrictInputOrders_eq (rank : ℕ) (hrank : rank ≤ recipeStrictRankBound c) :
    OriginalMeshPairedStep.profileOrders
      (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
      (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS)
      (box rank) theta
      (actualStrictOutputOrders c lower upper hlower hlowerSmall hupper volume hinterval J A)
      (volume rank) =
      (r).inputOrders (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extra J A := by
  have h := actualStrictOrders_eq c lower upper hlower hlowerSmall hupper
    volume hinterval J A rank hrank
  change OriginalProfileAtomBounds.profileOrders
      (OriginalMeshPairedStep.orders (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
        (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS)
        (box rank) theta
        (actualStrictOutputOrders c lower upper hlower hlowerSmall hupper volume hinterval J A)
        (volume rank)) ∪
      CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders
        (OriginalMeshPairedStep.orders (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
          (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS)
          (box rank) theta
          (actualStrictOutputOrders c lower upper hlower hlowerSmall hupper volume hinterval J A)
          (volume rank))) = _
  rw [h]
  rfl

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualStrictOrders_eq
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualStrictInputOrders_eq
