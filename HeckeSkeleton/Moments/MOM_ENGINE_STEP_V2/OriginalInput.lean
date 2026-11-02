import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original complete arithmetic source of a strict call

Only the complete moving-row dictionary and the original norm-profile
identity enter this record.  The actual finite coefficient, its two
rectangles, and all prime slots are computed from those inputs.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open EngineStep EngineInduction

variable {K : Type} [Field K] [NumberField K]

structure OriginalInput (c : TargetContext K)
    (n : Node K c.family.omega (targetCharacter K c)) (Z : ℝ) where
  theta : Finset (HeckeCharacter K)
  source : CompleteSourceData c theta n.data
  normProfiles : NormProfileRecipe (fun _ : PUnit => n.data)

namespace OriginalInput

variable {c : TargetContext K}
variable {n : Node K c.family.omega (targetCharacter K c)} {Z : ℝ}

def raw (input : OriginalInput c n Z) :
    ParentRawAtoms (ActualSIntegerOrbit K (places K c)) n.data n.parameters
      Z 0 (Z ^ n.comparison₁) (Z ^ n.comparison₂) :=
  (input.source.arithmeticAtoms.constantAtoms input.normProfiles n.parameters Z 0).raw
    (Z ^ n.comparison₁) (Z ^ n.comparison₂)

/-- Both rectangles use the original finite Cartesian carrier. -/
theorem polynomial (input : OriginalInput c n Z) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows n.data n.parameters Z) :
    pairedStagePolynomial n.centered n.data u (Z ^ n.parameters.n₁)
      (Z ^ n.parameters.n₂) (Z ^ n.comparison₁) (Z ^ n.comparison₂) Z 0 =
      ∑ v ∈ input.raw.columns,
        input.raw.coefficient n.centered (input.raw.rowMap u) v *
          input.raw.phase (input.raw.rowMap u) v := by
  sorry

/-- The norm recipe only fixes row independence; every original ideal
and prime phase is still the canonical arithmetic residue. -/
theorem phase_dictionary (input : OriginalInput c n Z) :
    (∀ I ∈ input.raw.leftColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      input.raw.leftPhase q I = actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ I ∈ input.raw.rightColumns, ∀ q : ActualSIntegerOrbit K (places K c),
      input.raw.rightPhase q I = actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) I.val q.out.val) ∧
    (∀ i, ∀ p ∈ input.raw.slotColumns i, ∀ q : ActualSIntegerOrbit K (places K c),
      input.raw.primePhase q i p = actualIdealResidue (A := (axiomChoice K c).A)
        (σ := complexEmbedding K c) p.asIdeal q.out.val) := by
  sorry

end OriginalInput
end HeckeSkeleton.Moments.EngineStepV2
