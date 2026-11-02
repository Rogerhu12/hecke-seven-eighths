import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOriginalSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationMaskSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalAmplitude

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The four actual exceptional plain charts

Every quotient carrier and divisor below comes from the stored inner
allocation. The same original Schwartz profile represents both scale
rectangles. The right source retains its negative Fourier locations;
their effect is the exact opposite Fourier mode, before either norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem jointPhase_neg_left (ξ x : EngineParameter) :
    jointPhase (-ξ) x = jointPhase ξ (-x) := by
  simp only [jointPhase, inner_neg_left, inner_neg_right]

theorem allocated_plainDivisor_avoids {k : ℕ}
    (B : ActualColumnAllocation K k)
    (weight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (excluded : Finset (Ideal (𝓞 K)))
    (plain : Bool)
    (hd : PlainSupportData weight (if plain then B.plain₂ else B.plain₁) excluded) :
    Avoids (B.plainDivisor (if plain then Fin.succ 0 else 0)).val excluded := by
  cases plain with
  | false =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).1
    exact hd.divisor_avoids _ _ hw.1 hw.2
  | true =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1).2
    exact hd.divisor_avoids _ _ hw.1 hw.2

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet)

def t3bUnscaledSource : (side : Bool) →
    ActualAllocatedSource (Arithmetic.data c) EngineParameter packet.R.live
      (packet.ordinarySlots side)
  | false => (packet.t3bUnscaledLeftFrame hpacket phases).source
  | true => (packet.t3bUnscaledRightFrame hpacket phases).source

def t3bPlainDivisor (side plain : Bool) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  (packet.t3bUnscaledSource hpacket phases side).allocation.plainDivisor
    (if plain then Fin.succ 0 else 0)

def t3bChildPlain (side plain : Bool) : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  if plain then (packet.t3bUnscaledSource hpacket phases side).allocation.childPlain₂
  else (packet.t3bUnscaledSource hpacket phases side).allocation.childPlain₁

def t3bPlainScale (side rectangle plain : Bool) : ℝ :=
  if plain then (packet.t3bUnscaledTable hpacket phases side).scale₂ rectangle
  else (packet.t3bUnscaledTable hpacket phases side).scale₁ rectangle

theorem t3bPlainScale_pos (side rectangle plain : Bool) :
    0 < packet.t3bPlainScale hpacket phases side rectangle plain := by
  cases plain with
  | false => exact (packet.t3bUnscaledTable hpacket phases side).scale₁_pos rectangle
  | true => exact (packet.t3bUnscaledTable hpacket phases side).scale₂_pos rectangle

def t3bQuotientScale (side rectangle plain : Bool) : ℝ :=
  packet.t3bPlainScale hpacket phases side rectangle plain /
    idealNorm K (packet.t3bPlainDivisor hpacket phases side plain)

theorem t3bQuotientScale_pos (side rectangle plain : Bool) :
    0 < packet.t3bQuotientScale hpacket phases side rectangle plain :=
  div_pos (packet.t3bPlainScale_pos hpacket phases side rectangle plain)
    (idealNorm_pos K _)

def t3bFourierSign (side : Bool) : ℝ :=
  if side then -packet.firstSign else packet.firstSign

def t3bFourierMode (side : Bool) (ξ : EngineParameter) : EngineParameter :=
  if side then -ξ else ξ

def t3bPlainLocation (side : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : EngineParameter :=
  if side then -CanonicalLiteralLocations.plain (packet.t3bFourierSign side) I
  else CanonicalLiteralLocations.plain (packet.t3bFourierSign side) I

theorem t3bPlainLocation_phase (side : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) (ξ : EngineParameter) :
    jointPhase ξ (packet.t3bPlainLocation side I) =
      jointPhase (t3bFourierMode side ξ)
        (CanonicalLiteralLocations.plain (packet.t3bFourierSign side) I) := by
  cases side with
  | false => rfl
  | true => exact (T3b.jointPhase_neg_left ξ _).symm

def t3bPlainProfile (input : ProfileInput call) (side plain : Bool)
    (ξ : EngineParameter) : 𝓢(ℝ, ℂ) :=
  T3b.phasedProfile (packet.t3bFourierSign side) (t3bFourierMode side ξ)
    (packet.t3bPlainDivisor hpacket phases side plain)
    (packet.t3bNormProfile hpacket input plain)

theorem t3bPlainProfile_support (input : ProfileInput call) (side plain : Bool)
    (ξ : EngineParameter) :
    tsupport (packet.t3bPlainProfile hpacket phases input side plain ξ) ⊆
      T3b.profileWindow c call.frame :=
  (T3b.phasedProfile_support _ _ _ _).trans
    (packet.t3bNormProfile_support hpacket input plain)

theorem t3bPlainProfile_seminorm (input : ProfileInput call) (side plain : Bool)
    (ξ : EngineParameter) (orders : Finset (ℕ × ℕ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bPlainProfile hpacket phases input side plain ξ) =
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) :=
  T3b.phasedProfile_seminorm _ _ _ _ orders

theorem t3bPlainWeight_eq (side rectangle plain : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain rectangle I =
      packet.normProfile plain
        (idealNorm K I / packet.t3bPlainScale hpacket phases side rectangle plain) := by
  cases plain with
  | false => exact packet.t3bUnscaled_leftWeight hpacket phases side rectangle I
  | true => exact packet.t3bUnscaled_rightWeight hpacket phases side rectangle I

theorem t3bPlainProfile_identity (input : ProfileInput call)
    (side rectangle plain : Bool) (ξ : EngineParameter) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain rectangle
        (packet.t3bPlainDivisor hpacket phases side plain * I) *
      jointPhase ξ (packet.t3bPlainLocation side
        (packet.t3bPlainDivisor hpacket phases side plain * I)) =
      (Ideal.absNorm I.val : ℂ) ^
        (Complex.I * (T3b.time (packet.t3bFourierSign side)
          (t3bFourierMode side ξ) : ℂ)) *
        packet.t3bPlainProfile hpacket phases input side plain ξ
          ((Ideal.absNorm I.val : ℝ) /
            packet.t3bQuotientScale hpacket phases side rectangle plain) := by
  rw [packet.t3bPlainWeight_eq hpacket phases,
    original_norm_quotient _ I _ (packet.t3bPlainScale_pos hpacket phases side rectangle plain),
    packet.t3bPlainLocation_phase, T3b.phase_mul]
  change packet.normProfile plain _ * (_ * _) =
    _ * (_ * packet.t3bNormProfile hpacket input plain _)
  rw [packet.t3bNormProfile_apply hpacket input]
  ring

theorem t3bCompleteMask_avoids (h : packet.R.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : IsCoprime I.val (packet.t3bCompleteMask phases h)) :
    T3b.Avoids I.val packet.t3bExcluded := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQ | hQ
  · rcases Finset.mem_union.mp hQ with hQ | hQ
    · rw [Finset.mem_singleton.mp hQ]
      exact packet.t3bCompleteMask_coprime_badPlaces phases h I hcop
    · exact packet.t3bCompleteMask_coprime_firstDeletion phases h I hcop Q hQ
  · exact packet.t3bCompleteMask_coprime_secondDeletion phases h I hcop Q hQ

theorem t3bPlainDivisor_avoids (side plain : Bool) :
    T3b.Avoids (packet.t3bPlainDivisor hpacket phases side plain).val
      packet.t3bExcluded := by
  apply T3b.allocated_plainDivisor_avoids
    (packet.t3bUnscaledSource hpacket phases side).allocation
    ((packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain)
    packet.t3bExcluded plain
  cases side <;> cases plain <;>
    exact packet.t3bBeforePlainSupport hpacket phases _ _

theorem t3bPlainProfile_mem (input : ProfileInput call)
    (side rectangle plain : Bool) (ξ : EngineParameter) (h : packet.R.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : IsCoprime I.val (packet.t3bCompleteMask phases h))
    (hW : packet.t3bPlainProfile hpacket phases input side plain ξ
      ((Ideal.absNorm I.val : ℝ) /
        packet.t3bQuotientScale hpacket phases side rectangle plain) ≠ 0) :
    I ∈ packet.t3bChildPlain hpacket phases side plain := by
  let D := packet.t3bPlainDivisor hpacket phases side plain
  have hn : packet.normProfile plain
      ((Ideal.absNorm I.val : ℝ) /
        packet.t3bQuotientScale hpacket phases side rectangle plain) ≠ 0 := by
    apply right_ne_zero_of_mul (a := jointPhase (t3bFourierMode side ξ)
      (CanonicalLiteralLocations.plain (packet.t3bFourierSign side) D))
    simpa only [t3bPlainProfile, T3b.phasedProfile, SchwartzMap.smul_apply,
      smul_eq_mul, packet.t3bNormProfile_apply hpacket input] using hW
  have hw : (packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain rectangle
      (D * I) ≠ 0 := by
    rw [packet.t3bPlainWeight_eq hpacket phases,
      original_norm_quotient _ I _ (packet.t3bPlainScale_pos hpacket phases side rectangle plain)]
    exact hn
  have hm : (D * I).val ∈ packet.t3bBeforePlainCarrier side plain :=
    (packet.t3bBeforePlainSupport hpacket phases side plain).mem_of_weight rectangle (D * I) hw
      (fun Q hQ => (packet.t3bPlainDivisor_avoids hpacket phases side plain Q hQ).mul_left
        (packet.t3bCompleteMask_avoids phases h I hcop Q hQ))
  have hmem := (mem_nonzeroQuotientMomentSupport D.val (nonZeroDivisors.coe_ne_zero D)
    (packet.t3bBeforePlainCarrier side plain) I).mpr hm
  cases side <;> cases plain <;> exact hmem

/-- This chart is on the actual quotient carrier. No equality of whole
polynomials, no mask estimate and no finite-sum estimate is a premise. -/
def t3bPlainChart (input : ProfileInput call) (side rectangle plain : Bool)
    (ξ : EngineParameter) (h : packet.R.live) :
    ExceptionalPlainChart (σ := Arithmetic.embedding c)
      (packet.t3bUnscaledTable hpacket phases side).characters.plain
      (packet.t3bUnscaledTable hpacket phases side).characters.plainTwist
      (packet.t3bUnscaledTable hpacket phases side).characters.mask
      (if side then -packet.R.factor (Arithmetic.context c) h.val
        else packet.R.factor (Arithmetic.context c) h.val)
      (packet.R.extractedRow (Arithmetic.context c) h).element
      (CanonicalExceptionalVolume.coefficient
        (call.localizedData.plainBackground * packet.t3bOriginalCharacter phases h))
      (packet.t3bCompleteMask phases h)
      (packet.t3bPlainProfile hpacket phases input side plain ξ)
      (T3b.time (packet.t3bFourierSign side) (t3bFourierMode side ξ))
      (packet.t3bQuotientScale hpacket phases side rectangle plain)
      (packet.t3bChildPlain hpacket phases side plain)
      (fun I => (packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain rectangle
        (packet.t3bPlainDivisor hpacket phases side plain * I))
      (fun I => packet.t3bPlainLocation side
        (packet.t3bPlainDivisor hpacket phases side plain * I)) ξ where
  coefficient I _ := packet.t3bUnscaled_plain_coefficient hpacket phases h side I
  profile I _ := packet.t3bPlainProfile_identity hpacket phases input side rectangle plain ξ I
  support I hcop _ hW :=
    packet.t3bPlainProfile_mem hpacket phases input side rectangle plain ξ h I hcop hW

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bPlainProfile_identity
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bPlainChart
