import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationOrigin

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual arithmetic atoms of the canonical child

The old paid moving factors are appended to the second active factors.
The original sixth-root ideal stays in the remaining mask. A constant
pattern and sector are used only after proving that every original live
row has those values. The right side changes the extracted factor to
its negative while retaining the same residual element and ideal.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAtoms

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
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

theorem one_mem : (1 : HeckeCharacter K) ∈ call.node.data.theta := by
  rw [call.source.source.theta_eq]
  exact Expansion.Project.one_mem_canonicalDetectorTheta K (targetCharacter K c)

theorem correction_mem : correction seed ∈ call.node.data.theta := by
  rcases call.localizedSource.source.recipe.correction_mem PUnit.unit with h | h
  · change call.localizedSource.source.recipe.correction ∈ call.node.data.theta
    rw [h]
    exact one_mem (call := call)
  · exact h

theorem characters_paid {k : ℕ} (index : Fin k → Fin call.node.data.geometry.slotCount) :
    seed.phases.characters true index =
      CalibrationPhases.sourceCharacters (probeData K c) (momentRowCharacters K c)
        call.node.data (seed.phases.moving true) (correction seed)
        call.localizedSource.source.recipe.remaining index := by
  change CanonicalOriginalPhaseCalibration.sourceCharacters call.localizedData
      (call.localizedSource.source.recipe.correction * (seed.phases.moving true).character)
      (exteriorMomentIdeal ((seed.phases.moving true).effectiveFullSupport
        call.localizedSource.source.recipe.remaining) * 1) index = _
  rw [mul_one]
  rfl

variable (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)
variable (pattern : Fin packet.block.primeCount → Bool)
variable (ν : SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))))

abbrev data := CalibrationConstruction.data seed input support side a rectangle
  (moving seed pattern) (correction seed) (Or.inr (correction_mem seed)) (fun _ => ν)
  (remaining seed)

variable (hpattern : ∀ h : seed.ordinary.rows.live,
  actualNonunitPattern (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
    packet.R.rightMultiplicity (packet.R.frequency h.val) = pattern)
variable (hsector : ∀ h : seed.ordinary.rows.live,
  (packet.R.extractedRow (Arithmetic.context c) (seed.ordinary.originalLiveRow h)).sector
    (probeData K c) = ν)

include hpattern hsector in
/-- No coefficient or residue identity is assumed: both dictionaries
come from the actual extracted-factor decomposition and original sector. -/
def dictionary (ξ : EngineParameter) (h : seed.ordinary.rows.live) :
    let s := seed.canonicalSource input support side a rectangle
    ((s.characters h).restrictSlots s.allocation.keep).Calibration
      (σ := Arithmetic.embedding c) (data seed input support side a rectangle pattern ν ξ)
      rfl (s.row h).momentIdeal (s.extractedFactor h) (s.row h).element := by
  have hf := packet.R.factor_sixth_active (Arithmetic.context c) h.val
  rw [hpattern h] at hf
  have hc := CalibrationPhases.calibration (probeData K c) (momentRowCharacters K c)
    call.node.data (seed.phases.moving true) (correction seed) (correction_mem seed)
    (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
    pattern ν call.localizedSource.source.recipe.remaining 0
    (CalibrationConstruction.inverseTest seed input ξ)
    (CalibrationConstruction.plainTest seed input side rectangle false ξ)
    (CalibrationConstruction.plainTest seed input side rectangle true ξ)
    (CalibrationConstruction.geometry seed input support side a ξ)
    (CalibrationConstruction.index seed input support side a)
    (one_mem (call := call)) rfl rfl
    (packet.R.extractedRow (Arithmetic.context c) (seed.ordinary.originalLiveRow h)) hf (hsector h)
  have hn := CalibrationPhases.negativeCalibration (probeData K c) (momentRowCharacters K c)
    call.node.data (seed.phases.moving true) (correction seed) (correction_mem seed)
    (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
    pattern ν call.localizedSource.source.recipe.remaining 0
    (CalibrationConstruction.inverseTest seed input ξ)
    (CalibrationConstruction.plainTest seed input side rectangle false ξ)
    (CalibrationConstruction.plainTest seed input side rectangle true ξ)
    (CalibrationConstruction.geometry seed input support side a ξ)
    (CalibrationConstruction.index seed input support side a)
    (one_mem (call := call)) rfl rfl
    (packet.R.extractedRow (Arithmetic.context c) (seed.ordinary.originalLiveRow h)) hf (hsector h)
  have hs :
      (((seed.canonicalSource input support side a rectangle).characters h).restrictSlots
        (seed.canonicalSource input support side a rectangle).allocation.keep) =
      CalibrationPhases.sourceCharacters (probeData K c) (momentRowCharacters K c)
        call.node.data (seed.phases.moving true) (correction seed)
        call.localizedSource.source.recipe.remaining
        (CalibrationConstruction.index seed input support side a) := by
    change (seed.phases.characters true (seed.slotIndex side)).restrictSlots _ = _
    rw [characters_paid seed]
    rfl
  dsimp only
  rw [hs]
  cases side
  · exact {
      fixedRay_mem_theta := hc.fixedRay_mem_theta
      plain := hc.plain
      slot := hc.slot }
  · exact {
      fixedRay_mem_theta := hn.fixedRay_mem_theta
      plain := hn.plain
      slot := hn.slot }

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAtoms

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAtoms.characters_paid
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAtoms.dictionary
