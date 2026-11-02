import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalRefinement

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N2: the exact residual deletion and its original finite expansion

Only `fullDeletion \ paidSupport` is expanded. The paid coefficients
retain their own zeros, and the fixed bad-prime gate stays in every
carrier. The source, its scalar, its global profiles and its finite
labels are genuine definitions; the task proves their identities and
the original pointwise Cauchy bound. Paper: lines 2910--2928.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} (seed : OrdinarySeed packet)
variable (input : ProfileInput call)

structure OrdinarySeed.CanonicalSupport
    (support : seed.ordinary.PassiveSupport input) : Prop where
  slots : ∀ side, (support.side side).slotEmbedding = seed.slotIndex side
  plain : ∀ side rectangle plain,
    (support.side side).plain rectangle plain = seed.plainProfile input side rectangle plain
  prime : ∀ side i, (support.side side).prime i = seed.primeProfile input side i

/-- These identities state exactly which mask is removed. They hold
for individual factors, before summing any ideal or prime occurrence. -/
structure OrdinarySeed.ResidualMaskIdentity : Prop where
  plain : ∀ side (I : NonzeroIdeal K),
    let original := seed.phases.characters false (seed.slotIndex side)
    let paid := seed.phases.characters true (seed.slotIndex side)
    sourcePlainCoefficient original.plain original.plainTwist original.mask I =
      sourcePlainCoefficient paid.plain paid.plainTwist paid.mask I *
        (if IsCoprime I.val seed.ordinary.passiveMask then 1 else 0)
  prime : ∀ side (i : Fin (seed.ordinary.residualSlotCount side))
      (q : HeightOneSpectrum (𝓞 K)),
    let original := seed.phases.characters false (seed.slotIndex side)
    let paid := seed.phases.characters true (seed.slotIndex side)
    sourcePrimeCoefficient (original.slot i) (original.slotTwist i) original.mask q =
      sourcePrimeCoefficient (paid.slot i) (paid.slotTwist i) paid.mask q *
        (if IsCoprime q.asIdeal seed.ordinary.passiveMask then 1 else 0)
  paid_plain_zero : ∀ side (I : NonzeroIdeal K),
    ¬IsCoprime I.val packet.second.physical.first.paidSupport.val →
    let paid := seed.phases.characters true (seed.slotIndex side)
    sourcePlainCoefficient paid.plain paid.plainTwist paid.mask I = 0
  paid_prime_zero : ∀ side (i : Fin (seed.ordinary.residualSlotCount side))
      (q : HeightOneSpectrum (𝓞 K)),
    ¬IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val →
    let paid := seed.phases.characters true (seed.slotIndex side)
    sourcePrimeCoefficient (paid.slot i) (paid.slotTwist i) paid.mask q = 0

def OrdinarySeed.RefinementBound (support : seed.ordinary.PassiveSupport input) : Prop :=
  ∀ z : ℝ × ℝ,
    packet.leaf.weight * packet.leaf.ordinaryIntegrand z /
      call.base ^ (call.node.parameters.m + call.node.parameters.q) ≤
    ∑ b : support.Label,
      (seed.refinement input support).outer b *
        (seed.refinement input support).sourcePair b (WithLp.toLp 2 z)

def PassiveRefinementTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call) (packet : RawLeafPacket call p),
    packet.Realizes → ∀ seed : OrdinarySeed packet,
      ∃ support : seed.ordinary.PassiveSupport input,
        seed.CanonicalSupport input support ∧ seed.ResidualMaskIdentity ∧
          seed.RefinementBound input support

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
