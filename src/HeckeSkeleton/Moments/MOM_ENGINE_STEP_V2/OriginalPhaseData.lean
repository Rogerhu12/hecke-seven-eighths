module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceScalarData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassivePhases
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingFactorAppend

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original and paid phases use one actual pool choice

The finite first element is the one in the physical source. The only
additional datum is its actual pool valuation/prime, with an equality
to the recorded original tag. A Boolean selects the proved active
reduction of that same pool element. No independent character, mask or
new theta member is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance] sourcePrincipal

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

structure OriginalPhaseData (packet : RawLeafPacket call p) where
  first_nonzero : packet.second.physical.first.firstElement ≠ 0
  pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))
  pool_tag : match pool with
    | none => packet.second.physical.first.tag = .direct ∨
        packet.second.physical.first.tag = .main
    | some (e, q) => packet.second.physical.first.tag = .error e q.val
  pool_power : packet.second.physical.first.poolPower = match pool with
    | none => unitExterior (Arithmetic.data c)
    | some (e, q) => powerIdeal q e.multiplicity
  deletion_nonzero : (∏ I ∈ packet.second.physical.first.fullDeletion, I) ≠ 0

namespace OriginalPhaseData

variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)

def deletionIdeal : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨∏ I ∈ packet.second.physical.first.fullDeletion, I,
    mem_nonZeroDivisors_of_ne_zero P.deletion_nonzero⟩

def firstMoving : OriginalMovingFactors (Arithmetic.data c)
    (probeData K c) (momentRowCharacters K c) :=
  OriginalMovingFactors.singleton
    ⟨packet.second.physical.first.firstElement, P.first_nonzero⟩ 1

def poolMoving (paid : Bool) : OriginalMovingFactors (Arithmetic.data c)
    (probeData K c) (momentRowCharacters K c) :=
  match P.pool with
  | none => OriginalMovingFactors.singleton ⟨1, one_ne_zero⟩ 1
  | some (e, q) =>
    if paid then
      CanonicalLiteralPassivePhases.activeMoving (probeData K c)
        (momentRowCharacters K c) (Arithmetic.context c) q e
    else OriginalMovingFactors.singleton
      ⟨generator (Arithmetic.context c) q ^ (2 * e.multiplicity),
        (generator_power_generates (Arithmetic.context c) q (2 * e.multiplicity)).1⟩ 1

def moving (paid : Bool) : OriginalMovingFactors (Arithmetic.data c)
    (probeData K c) (momentRowCharacters K c) :=
  (((call.localizedSource.source.recipe.moving.append P.firstMoving).append
    (P.poolMoving paid)).append
      (CanonicalLiteralFixedPhases.emptyDivisorMoving
        (probeData K c) (momentRowCharacters K c)))

/-- The paid recipe keeps all its actual moving zeros. The unexpanded
recipe additionally retains the complete original first deletion. -/
def mask (paid : Bool) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  exteriorMomentIdeal ((P.moving paid).effectiveFullSupport
    call.localizedSource.source.recipe.remaining) *
      if paid then 1 else P.deletionIdeal

def characters (paid : Bool) {k : ℕ}
    (index : Fin k → Fin call.localizedData.geometry.slotCount) : FixedChildCharacters K k :=
  CanonicalOriginalPhaseCalibration.sourceCharacters call.localizedData
    (call.localizedSource.source.recipe.correction * (P.moving paid).character)
    (P.mask paid) index

end OriginalPhaseData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
