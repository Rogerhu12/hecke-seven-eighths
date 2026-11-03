import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalRecoveryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aFiniteSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact exceptional support and the actual sixth-power decomposition

These elementary parts of T3a do not assume an exceptional volume bound.
The support identity discards a row only when its actual row weight or
one of its original whole finite columns vanishes. The ideal identities
use the already selected extracted row, without choosing a new ideal.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_leaf_rows : packet.leaf.rows = packet.R.rows := rfl

theorem exceptional_leaf_rowWeight (h : Arithmetic.Orbit c) :
    packet.leaf.rowWeight h = packet.R.weight h * packet.R.correlation h := rfl

/-- The ideal decomposition is the canonical sixth-free decomposition
of the original selected extracted ideal. -/
theorem exceptional_factorization (h : packet.R.live) :
    (packet.R.extractedRow (Arithmetic.context c) h).ideal.val =
      (packet.sixthBase h).val *
        (sixthPowerAmplifierPart
          (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val ^ 6 := by
  exact congrArg (fun I : HeckeGeneral.Analysis.NonzeroIdeal K => I.val)
    (sixthPowerFreePart_mul_amplifier_sixth
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).symm

theorem exceptional_base_sixth_free (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ packet.exceptionalBases) : SixthPowerFreeIdeal I := by
  obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hI
  exact sixthPowerFreePart_isSixthPowerFree
    (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal

/-- Arithmetic valuations from the exceptional character classification
give the fourth-power divisor of the same canonical sixth-free base. -/
theorem exceptional_fourth_power (h : packet.R.live)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val),
      6 ∣ (normalizedFactors (packet.R.originalIdeal h.val).val).count
        (packet.R.primes i).val.asIdeal) :
    (packet.multiplicityOneRadical h).val ^ 4 ∣ (packet.sixthBase h).val ∧
      (Arithmetic.data c).exteriorNorm (packet.multiplicityOneRadical h) ^ 4 ≤
        (Ideal.absNorm (packet.sixthBase h).val : ℝ) := by
  exact (packet.R.exceptionalRow (Arithmetic.context c) h).base_fourth_power
    packet.R.primes_injective hclass (packet.sixthBase h).val
    (sixthPowerAmplifierPart
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val
    (packet.exceptional_factorization h)

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.pairMagnitude_eq_supported
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_factorization
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_fourth_power
