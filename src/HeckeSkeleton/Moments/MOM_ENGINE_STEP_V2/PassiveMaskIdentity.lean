module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePaidMask
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The residual identity for every original ideal and prime

The genuine paid mask enforces its physical paid support. On that
support the full first deletion equals its residual deletion. Outside
it both sides vanish. The coefficient identity therefore needs no
extra coprimality premise, including at the fixed bad primes.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

private theorem originalCoprimeMask_apply (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    originalCoprimeMask M I = (if IsCoprime I M.val then 1 else 0) := rfl

namespace OriginalPhaseData

variable (P : OriginalPhaseData packet) (hpacket : packet.Realizes)
variable {k : ℕ} (index : Fin k → Fin call.node.data.geometry.slotCount)

include hpacket in
theorem paid_plain_coefficient_zero (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hpaid : ¬IsCoprime I.val packet.second.physical.first.paidSupport.val) :
    sourcePlainCoefficient (P.characters true index).plain
      (P.characters true index).plainTwist (P.characters true index).mask I = 0 := by
  have hm : ¬IsCoprime I.val (P.mask true).val :=
    fun h => hpaid ((P.paidMask_coprime hpacket I.val).mp h)
  simp only [characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePlainCoefficient, originalCoprimeMask_apply, if_neg hm, mul_zero]

include hpacket in
theorem paid_prime_coefficient_zero (i : Fin k) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hpaid : ¬IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val) :
    sourcePrimeCoefficient ((P.characters true index).slot i)
      ((P.characters true index).slotTwist i) (P.characters true index).mask q = 0 := by
  have hm : ¬IsCoprime q.asIdeal (P.mask true).val :=
    fun h => hpaid ((P.paidMask_coprime hpacket q.asIdeal).mp h)
  simp only [characters, CanonicalOriginalPhaseCalibration.sourceCharacters,
    sourcePrimeCoefficient, originalCoprimeMask_apply, if_neg hm, mul_zero]

end OriginalPhaseData

namespace OrdinarySeed

variable (seed : OrdinarySeed packet)

theorem residualMaskIdentity (hpacket : packet.Realizes) : seed.ResidualMaskIdentity where
  plain side I := by
    have hpassive := PassivePhaseBridge.poolPassiveIdeal_dvd_deletion seed.phases hpacket
    have he := PassivePhaseBridge.plain_coefficient_global seed.phases
      (seed.slotIndex side) hpassive I
    by_cases hpaid : IsCoprime I.val packet.second.physical.first.paidSupport.val
    · have hr := seed.ordinary.residual_coprime_iff I.val hpaid
      simpa only [originalCoprimeMask_apply, OriginalPhaseData.deletionIdeal, hr] using he
    · have hz := seed.phases.paid_plain_coefficient_zero hpacket
        (seed.slotIndex side) I hpaid
      simpa only [hz, zero_mul] using he
  prime side i q := by
    have hpassive := PassivePhaseBridge.poolPassiveIdeal_dvd_deletion seed.phases hpacket
    have he := PassivePhaseBridge.prime_coefficient_global seed.phases
      (seed.slotIndex side) hpassive i q
    by_cases hpaid : IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val
    · have hr := seed.ordinary.residual_coprime_iff q.asIdeal hpaid
      simpa only [originalCoprimeMask_apply, OriginalPhaseData.deletionIdeal, hr] using he
    · have hz := seed.phases.paid_prime_coefficient_zero hpacket
        (seed.slotIndex side) i q hpaid
      simpa only [hz, zero_mul] using he
  paid_plain_zero side I hpaid :=
    seed.phases.paid_plain_coefficient_zero hpacket (seed.slotIndex side) I hpaid
  paid_prime_zero side i q hpaid :=
    seed.phases.paid_prime_coefficient_zero hpacket (seed.slotIndex side) i q hpaid

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.residualMaskIdentity
