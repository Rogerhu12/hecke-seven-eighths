module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original individual rectangles at a raw leaf

The unweighted second-column factor is the actual norm tilt and the
actual divisor phase. Applying it to each of the two original first
rectangles fixes them separately; equality of their difference alone
would allow arbitrary large cancelling terms.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

def leftSecondMultiplier (i : packet.second.physical.Column) : ℂ :=
  (((Arithmetic.data c).exteriorNorm (packet.block.secondLeftIdeal i) ^ p.tilt : ℝ) : ℂ) *
    (generatedOriginalColumn (σ := Arithmetic.embedding c)
      (Arithmetic.units_are_sixth c) (packet.block.secondLeftIdeal i)
      (engineAllowedGenerator (Arithmetic.context c) packet.block.commonLeftIdeal *
        packet.block.leftGenerator i)
      (packet.block.secondLeft_generates (Arithmetic.context c) i)).divisorPhase
        (sIntegerMaskGenerator K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) packet.key.2.1.val).val

def rightSecondMultiplier (i : packet.second.physical.Column) : ℂ :=
  (((Arithmetic.data c).exteriorNorm (packet.block.secondRightIdeal i) ^ p.tilt : ℝ) : ℂ) *
    (generatedOriginalColumn (σ := Arithmetic.embedding c)
      (Arithmetic.units_are_sixth c) (packet.block.secondRightIdeal i)
      (engineAllowedGenerator (Arithmetic.context c) packet.block.commonRightIdeal *
        packet.block.rightGenerator i)
      (packet.block.secondRight_generates (Arithmetic.context c) i)).divisorPhase
        (sIntegerMaskGenerator K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) packet.key.2.1.val).val

def originalLeftRectangle (comparison : Bool)
    (i : AllocationColumn K packet.leaf.leftSlots) : ℂ :=
  packet.second.physical.rectangle comparison (packet.leftReindex.index i) *
    packet.leftSecondMultiplier (packet.leftReindex.index i)

def originalRightRectangle (comparison : Bool)
    (i : AllocationColumn K packet.leaf.rightSlots) : ℂ :=
  packet.second.physical.rectangle comparison (packet.rightReindex.index i) *
    packet.rightSecondMultiplier (packet.rightReindex.index i)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
