module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryFirstAtomFormula
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryMultiplierTransport

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The four original raw-leaf rectangles

The source trace fixes the original ancestor and both actual norm
tilts. The first atom formula absorbs their original residues, and
the second support extraction produces the same global table used
by the ordinary frames. Every identity concerns one rectangle before
the two comparisons are subtracted.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def ordinarySecondMultiplier : Bool → packet.second.physical.Column → ℂ
  | false => packet.leftSecondMultiplier
  | true => packet.rightSecondMultiplier

theorem ordinaryMultiplier_eq_residues (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    packet.second.physical.multiplier (packet.secondColumn side x) *
        packet.ordinarySecondMultiplier side (packet.secondColumn side x) =
      packet.poolScalar *
        (((Arithmetic.data c).exteriorNorm
          (packet.second.physical.source.ideal (packet.secondColumn side x)) ^
            (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.secondColumn side x)).val
          packet.second.physical.first.firstElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.secondColumn side x)).val
          phases.poolElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          (packet.second.physical.source.ideal (packet.secondColumn side x)).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c)) := by
  cases side with
  | false =>
    exact packet.leftMultiplier_eq_residues hpacket phases x
      (packet.leftReindex_cartesian.symm ▸ hx)
  | true =>
    exact packet.rightMultiplier_eq_residues hpacket phases x
      (packet.rightReindex_cartesian.symm ▸ hx)

/-- The table is the actual physical rectangle, after both genuine
support extractions and before its original divisor allocation. -/
theorem beforeAtomTable_eq_originalRectangle (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side rectangle : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.beforeAtomTable hpacket phases side).term rectangle
        (cast (congrArg (AllocationColumn K) (packet.secondAtomCount side)) x) =
      packet.second.physical.rectangle rectangle (packet.secondColumn side x) *
        packet.ordinarySecondMultiplier side (packet.secondColumn side x) := by
  have hJ : (packet.second.physical.source.ideal (packet.secondColumn side x)).val =
      allocationColumnIdeal (packet.firstResidualColumn hpacket side x) := by
    rw [packet.firstResidualColumn_ideal hpacket side x]
    exact packet.secondColumn_ideal side x hx
  have hfirst := packet.firstAtomFormula hpacket phases side rectangle
    ((packet.secondBranch side).reconstruct x) (packet.secondReconstruct_mem side x hx)
    (packet.second.physical.source.ideal (packet.secondColumn side x)) hJ
    (packet.secondColumn_coprime_deletion hpacket phases side x hx)
  have hmult := packet.ordinaryMultiplier_eq_residues hpacket phases side x hx
  have horiginal := packet.second.physical.rectangle_of_originalIndex rectangle
    (packet.secondColumn side x)
    ((packet.firstBranch side).reconstruct (packet.firstResidualColumn hpacket side x))
    (packet.ancestor_secondColumn hpacket side x hx)
  rw [← packet.beforeAtomTable_term hpacket phases side rectangle x hx, hfirst, ← hmult,
    horiginal]
  dsimp only [firstResidualColumn]
  ring

theorem beforeAtomTable_left (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (rectangle : Bool)
    (x : AllocationColumn K packet.leaf.leftSlots) (hx : x ∈ packet.leftReindex.cartesian) :
    (packet.beforeAtomTable hpacket phases false).term rectangle x =
      packet.originalLeftRectangle rectangle x := by
  exact packet.beforeAtomTable_eq_originalRectangle hpacket phases false rectangle x
    (packet.leftReindex_cartesian ▸ hx)

theorem beforeAtomTable_right (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (rectangle : Bool)
    (x : AllocationColumn K packet.leaf.rightSlots) (hx : x ∈ packet.rightReindex.cartesian) :
    (packet.beforeAtomTable hpacket phases true).term rectangle x =
      packet.originalRightRectangle rectangle x := by
  exact packet.beforeAtomTable_eq_originalRectangle hpacket phases true rectangle x
    (packet.rightReindex_cartesian ▸ hx)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.beforeAtomTable_left
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.beforeAtomTable_right
