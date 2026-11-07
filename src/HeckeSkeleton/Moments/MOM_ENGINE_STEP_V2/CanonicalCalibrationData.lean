module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Canonical data for the original residual calibration

The class values, moving factors, remaining mask, raw parameters and
profile shape are fixed by the same original packet and seed. These
are the original definitions, separated from their task proofs.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace CalibrationClass

variable (packet : RawLeafPacket call p)

/-- The empty class has no later row obligation. In a nonempty class,
both fixed values below are taken from an actual original live row. -/
def pattern : Fin packet.block.primeCount → Bool :=
  if h : Nonempty packet.R.live then
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity
      (packet.R.frequency (Classical.choice h).val)
  else fun _ => false

def sector : SixthUnitClasses K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  if h : Nonempty packet.R.live then
    (packet.R.extractedRow (Arithmetic.context c) (Classical.choice h)).sector (probeData K c)
  else 1

end CalibrationClass

namespace CalibrationParameters

variable (packet : RawLeafPacket call p)

def rootLength : ℝ :=
  idealLogLength call.base
    (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity).val

def rowExponent (side : Bool) : ℝ :=
  (packet.nominal side).skeleton.nominalRow + 12 * p.loss

def supportExponent (side : Bool) : ℝ :=
  (packet.nominal side).skeleton.nominalSupport + 4 * p.loss + rootLength packet

variable {packet}
variable (seed : OrdinarySeed packet) (input : ProfileInput call)
variable (support : seed.ordinary.PassiveSupport input)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)

local notation "s" => seed.canonicalSource input support side a rectangle

def parameters : RealParameters :=
  { call.node.parameters with
    m := rowExponent packet side
    q := supportExponent packet side
    n₁ := Real.log ((s).scale₁ / idealNorm K ((s).allocation.plainDivisor 0)) / Real.log (s).base
    n₂ := Real.log ((s).scale₂ / idealNorm K ((s).allocation.plainDivisor (Fin.succ 0))) /
      Real.log (s).base
    z := ∑ i, (s).childLength i }

end CalibrationParameters

namespace CalibrationAtoms

variable {packet : RawLeafPacket call p}
variable (seed : OrdinarySeed packet)

def moving (pattern : Fin packet.block.primeCount → Bool) :
    OriginalMovingFactors (Arithmetic.data c) (probeData K c) (momentRowCharacters K c) :=
  (seed.phases.moving true).append
    (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
      packet.R.rightMultiplicity pattern)

def correction (_seed : OrdinarySeed packet) : HeckeCharacter K :=
  call.localizedSource.source.recipe.correction

def remaining (_seed : OrdinarySeed packet) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  remainingMaskIdeal (Arithmetic.data c) call.localizedSource.source.recipe.remaining *
    exteriorMomentIdeal
      (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity)

end CalibrationAtoms

namespace CalibrationConstruction

/-- One shape works for every original branch, side and rectangle. -/
def shape : ProfileShape where
  dilationLower := 1
  dilationUpper := 1
  dilationLower_pos := zero_lt_one
  dilation_interval := le_rfl
  powerBound := 1
  powerBound_nonneg := zero_le_one
  phaseBound := 1
  phaseBound_nonneg := zero_le_one

end CalibrationConstruction

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
