import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Explicit original scalar data shared by all normalization sides

The first branch is the actual combined occurrence extraction. On a
pool residual it already includes the removed prime power. Its bare
common scalar is therefore multiplied by the pool reciprocity factor
exactly once. The remaining scale product is computed from the same
plain quotient scales and surviving original slot occurrences.

No scalar is chosen by dividing two potentially small profile values.
The identities identifying these numbers with the original single
atoms are separate normalization tasks.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

variable (call : Call c)

def originalCharacters :=
  call.localizedSource.source.recipe.literalSourceCharacters PUnit.unit

def originalLength (i : Fin call.localizedData.geometry.slotCount) : ℝ :=
  (call.localizedData.geometry.slots i).length

def originalSlotWeight (i : Fin call.localizedData.geometry.slotCount)
    (q : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (call.localizedData.geometry.slots i).profile 0
    ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i)

def originalPlainScale (rectangle plain : Bool) : ℝ :=
  if rectangle then
    call.base ^ (if plain then call.node.comparison₂ else call.node.comparison₁)
  else call.base ^ (if plain then call.node.parameters.n₂ else call.node.parameters.n₁)

end Call

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def firstBranch (side : Bool) :=
  if side then packet.rightFirst else packet.leftFirst

def firstPlainScale (side rectangle plain : Bool) : ℝ :=
  call.originalPlainScale rectangle plain /
    idealNorm K (if plain then (packet.firstBranch side).plainDivisor₂
      else (packet.firstBranch side).plainDivisor₁)

def firstScaleProduct (side : Bool) : ℝ :=
  packet.firstPlainScale side false false * packet.firstPlainScale side false true *
    ∏ i : Fin (packet.firstBranch side).keep.card,
      call.base ^ call.originalLength (SlotRestriction.index (packet.firstBranch side).keep i)

/-- This complex factor is an original finite product, including all
frozen prime profiles and all coprimality zeros. -/
def firstCommonScalar (side : Bool) : ℂ :=
  (packet.firstBranch side).bareCommonScalar call.originalCharacters call.base
    call.originalLength call.originalSlotWeight

def poolScalar : ℂ :=
  (((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ^ p.tilt : ℝ) : ℂ) *
    actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
      packet.second.physical.first.poolPower.val packet.second.physical.first.firstElement

/-- Both original Fourier tilts contribute once. The original extra
Gauss denominator and the extracted profile scale combine to this
power of the same combined first scale product. -/
def firstExternalScalar (side : Bool) : ℂ :=
  packet.firstCommonScalar side * packet.poolScalar *
    ((packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) : ℝ) : ℂ)

/-- The actual first Poisson sign, before the left/right second column
orientation is applied. -/
def firstSign : ℝ := if packet.second.physical.first.firstRight then -1 else 1

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
