import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedMetadata

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Every retained physical leaf carries its own literal coordinates

The dispatcher reads the actual dependent source key. It preserves the
first common pair, both independent divisors and phases, the first side,
the selected pool prime and valuation, the second common pair, both
occurrence branches and the exact allocation. No normalized family is
chosen here: the same packet feeds the single generic normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  selectedPrincipal selectedComplex selectedNormOneSpace selectedNormOneBorel
  selectedInfinityUnitSpace selectedInfinityUnitBorel selectedLocalUnitSpace selectedLocalUnitBorel

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

/-- The direct entrance retains its actual first sign and two original
occurrence labels. Its phase choice contains no artificial pool prime. -/
def directPacket (j : directKeys request frequency) :
    SelectedLeafPacket request frequency (directLeaf request frequency j) := by
  rcases j with ⟨⟨DE, D, S, χ, b⟩, hj⟩
  rcases b with b | b
  · exact {
      physical := directMetadata request frequency DE D S χ true
      cover := FirstBlockDirectData.leftSourceCover
        ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ
      key := b.1
      exceptional := (directPredicates request frequency DE D).left S χ
      firstKernel := ((firstSource request frequency).charts DE D).kernel
      location := ((firstSource request frequency).charts DE D).leftPoint
      allocation := b.2
      live := by sorry
      firstSign := 1
      leftInput := directLeftInput request frequency DE D S χ b.1.2.2.1
      rightInput := directLeftInput request frequency DE D S χ b.1.2.2.2.1
      phase_eq := rfl
      choice := .unamplified
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := directMetadata request frequency DE D S χ false
      cover := FirstBlockDirectData.rightSourceCover
        ((firstSource request frequency).pieces DE D) (atlas request frequency) S χ
      key := b.1
      exceptional := (directPredicates request frequency DE D).right S χ
      firstKernel := ((firstSource request frequency).charts DE D).kernel
      location := fun i => -((firstSource request frequency).charts DE D).rightPoint i
      allocation := b.2
      live := by sorry
      firstSign := -1
      leftInput := directRightInput request frequency DE D S χ b.1.2.2.1
      rightInput := directRightInput request frequency DE D S χ b.1.2.2.2.1
      phase_eq := rfl
      choice := .unamplified
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }

/-- The eight cases are exactly two first sides times the four original
pool summands. Every residual case keeps its own original prime. -/
def pooledPacket (j : pooledKeys request frequency) :
    SelectedLeafPacket request frequency (pooledLeaf request frequency j) := by
  rcases j with ⟨⟨DE, D, S, χ, b⟩, hj⟩
  rcases b with
    (b | (⟨q, b⟩ | (⟨q, b⟩ | ⟨q, b⟩))) |
      (b | (⟨q, b⟩ | (⟨q, b⟩ | ⟨q, b⟩)))
  · exact {
      physical := pooledMetadata request frequency DE D S χ true none
      cover := (((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).main
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).left S χ).main
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := ((pooledSource request frequency).charts DE D).leftPoint
      allocation := b.2
      live := by sorry
      firstSign := 1
      leftInput := mainLeftInput request frequency DE D S χ b.1.2.2.1
      rightInput := mainLeftInput request frequency DE D S χ b.1.2.2.2.1
      phase_eq := rfl
      choice := .unamplified
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ true (some (.one, q))
      cover := (((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual q 1
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).left S χ).one q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => ((pooledSource request frequency).charts DE D).leftPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := 1
      leftInput := poolLeftInput request frequency DE D S χ q 1 b.1.2.2.1
      rightInput := poolLeftInput request frequency DE D S χ q 1 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .one (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ true (some (.six, q))
      cover := (((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual q 6
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).left S χ).six q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => ((pooledSource request frequency).charts DE D).leftPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := 1
      leftInput := poolLeftInput request frequency DE D S χ q 6 b.1.2.2.1
      rightInput := poolLeftInput request frequency DE D S χ q 6 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .six (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ true (some (.seven, q))
      cover := (((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual q 7
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).left S χ).seven q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => ((pooledSource request frequency).charts DE D).leftPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := 1
      leftInput := poolLeftInput request frequency DE D S χ q 7 b.1.2.2.1
      rightInput := poolLeftInput request frequency DE D S χ q 7 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .seven (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ false none
      cover := (((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).main
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).right S χ).main
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => -((pooledSource request frequency).charts DE D).rightPoint i
      allocation := b.2
      live := by sorry
      firstSign := -1
      leftInput := mainRightInput request frequency DE D S χ b.1.2.2.1
      rightInput := mainRightInput request frequency DE D S χ b.1.2.2.2.1
      phase_eq := rfl
      choice := .unamplified
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ false (some (.one, q))
      cover := (((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual q 1
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).right S χ).one q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => -((pooledSource request frequency).charts DE D).rightPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := -1
      leftInput := poolRightInput request frequency DE D S χ q 1 b.1.2.2.1
      rightInput := poolRightInput request frequency DE D S χ q 1 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .one (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ false (some (.six, q))
      cover := (((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual q 6
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).right S χ).six q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => -((pooledSource request frequency).charts DE D).rightPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := -1
      leftInput := poolRightInput request frequency DE D S χ q 6 b.1.2.2.1
      rightInput := poolRightInput request frequency DE D S χ q 6 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .six (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }
  · exact {
      physical := pooledMetadata request frequency DE D S χ false (some (.seven, q))
      cover := (((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual q 7
      key := b.1
      exceptional := ((pooledPredicates request frequency DE D).right S χ).seven q
      firstKernel := ((pooledSource request frequency).charts DE D).kernel
      location := fun i => -((pooledSource request frequency).charts DE D).rightPoint i.val
      allocation := b.2
      live := by sorry
      firstSign := -1
      leftInput := poolRightInput request frequency DE D S χ q 7 b.1.2.2.1
      rightInput := poolRightInput request frequency DE D S χ q 7 b.1.2.2.2.1
      phase_eq := rfl
      choice := .amplified q.val .seven (by rfl)
      firstKernel_eq := by sorry
      secondKernel_eq := by sorry
      source_eq := by sorry }

end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2

