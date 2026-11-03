import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPlainSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original plain support on the same two extracted occurrence carriers

The starting support is the original parent carrier, at its actual
paired reference row. The two later support statements follow by the
exact reconstruction of their original occurrence witnesses.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

theorem t3b_workingRows (call : Call c) :
    pairedRows call.localizedData call.workingParameters call.base =
      pairedRows call.node.data call.node.parameters call.base := by
  have hwidth : call.workingParameters.m + call.workingParameters.q =
      call.node.parameters.m + call.node.parameters.q := by
    dsimp only [workingParameters]
    ring
  have hwork : pairedRows call.node.data call.workingParameters call.base =
      pairedRows call.node.data call.node.parameters call.base := by
    unfold pairedRows
    rw [hwidth]
    rfl
  change pairedRows (restrictOriginalRows call.node.data
    (fun u => u ∈ pairedRows call.node.data call.node.parameters call.base))
      call.workingParameters call.base = _
  exact (pairedRows_restrictOriginalRows_eq call.node.data
    (fun u => u ∈ pairedRows call.node.data call.node.parameters call.base)
    call.workingParameters call.base (fun _ hu => hwork ▸ hu)).trans hwork

theorem t3b_originalPlainScale_pos (call : Call c) (rectangle plain : Bool) :
    0 < call.originalPlainScale rectangle plain := by
  unfold originalPlainScale
  split_ifs <;> exact Real.rpow_pos_of_pos call.base_pos _

end Call

namespace OrdinaryAtomTable

def t3bPlainWeight {k : ℕ} (d : OrdinaryAtomTable (K := K) k)
    (plain : Bool) : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ :=
  if plain then d.rightWeight else d.leftWeight

end OrdinaryAtomTable

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

def t3bOriginalPlainCarrier (plain : Bool) : Finset (Ideal (𝓞 K)) :=
  if plain then call.workingRaw.originalPlain₂ else call.workingRaw.originalPlain₁

def t3bOriginalPlainWeight (plain rectangle : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  packet.normProfile plain (idealNorm K I / call.originalPlainScale rectangle plain)

def t3bOriginalPlainSupport (plain : Bool) :
    T3b.PlainSupportData (packet.t3bOriginalPlainWeight plain)
      (t3bOriginalPlainCarrier (call := call) plain) {(Arithmetic.data c).cS} := by
  have href : packet.originalReference hpacket ∈
      pairedRows call.localizedData call.workingParameters call.base := by
    rw [call.t3b_workingRows]
    exact packet.originalReference_mem hpacket
  have hallowed : call.localizedData.allowedRow (packet.originalReference hpacket) :=
    ((call.localizedData.rows_spec _ _).mp (Finset.mem_filter.mp href).1).1
  cases plain with
  | false =>
    refine ⟨call.workingRaw.originalPlain₁_nonzero, ?_, ?_⟩
    · intro I hI Q hQ
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
      rw [Finset.mem_singleton.mp hQ]
      exact (Finset.mem_filter.mp hJ).2
    · intro r I hw hcop
      have hprofile : call.localizedNormProfiles.left PUnit.unit 0
          (idealNorm K I / call.originalPlainScale r false) ≠ 0 :=
        left_ne_zero_of_mul hw
      have hs : I ∈ call.localizedData.plainTest₁.support (packet.originalReference hpacket) 0
          (if r then call.base ^ call.workingComparison₁
           else call.base ^ call.workingParameters.n₁) := by
        apply (call.localizedData.plainTest₁.support_spec _ _ _ _).mpr
        rw [call.localizedNormProfiles.left_eq PUnit.unit _ hallowed]
        cases r <;> exact hprofile
      have hm := parentPlainCarrier_contains
        (pairedRows call.localizedData call.workingParameters call.base)
        call.localizedData.plainTest₁ 0 (call.base ^ call.workingParameters.n₁)
        (call.base ^ call.workingComparison₁) r (packet.originalReference hpacket) href hs
      refine Finset.mem_image.mpr ⟨I, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hm, hcop _ (Finset.mem_singleton_self _)⟩
  | true =>
    refine ⟨call.workingRaw.originalPlain₂_nonzero, ?_, ?_⟩
    · intro I hI Q hQ
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
      rw [Finset.mem_singleton.mp hQ]
      exact (Finset.mem_filter.mp hJ).2
    · intro r I hw hcop
      have hprofile : call.localizedNormProfiles.right PUnit.unit 0
          (idealNorm K I / call.originalPlainScale r true) ≠ 0 :=
        left_ne_zero_of_mul hw
      have hs : I ∈ call.localizedData.plainTest₂.support (packet.originalReference hpacket) 0
          (if r then call.base ^ call.workingComparison₂
           else call.base ^ call.workingParameters.n₂) := by
        apply (call.localizedData.plainTest₂.support_spec _ _ _ _).mpr
        rw [call.localizedNormProfiles.right_eq PUnit.unit _ hallowed]
        cases r <;> exact hprofile
      have hm := parentPlainCarrier_contains
        (pairedRows call.localizedData call.workingParameters call.base)
        call.localizedData.plainTest₂ 0 (call.base ^ call.workingParameters.n₂)
        (call.base ^ call.workingComparison₂) r (packet.originalReference hpacket) href hs
      refine Finset.mem_image.mpr ⟨I, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hm, hcop _ (Finset.mem_singleton_self _)⟩

def t3bFirstPlainCarrier (side plain : Bool) : Finset (Ideal (𝓞 K)) :=
  if plain then (packet.firstAtlas side).reindex.plain₂
  else (packet.firstAtlas side).reindex.plain₁

def t3bBeforePlainCarrier (side plain : Bool) : Finset (Ideal (𝓞 K)) :=
  if side then
    if plain then packet.rightReindex.plain₂ else packet.rightReindex.plain₁
  else if plain then packet.leftReindex.plain₂ else packet.leftReindex.plain₁

def t3bFirstExcluded : Finset (Ideal (𝓞 K)) :=
  {(Arithmetic.data c).cS} ∪ packet.second.physical.first.fullDeletion

def t3bExcluded : Finset (Ideal (𝓞 K)) :=
  packet.t3bFirstExcluded ∪ primeSupport packet.key.1.val.1

def t3bFirstPlainSupport (phases : OriginalPhaseData packet) (side plain : Bool) :
    T3b.PlainSupportData
      ((packet.firstAtomTable hpacket phases side).t3bPlainWeight plain)
      (packet.t3bFirstPlainCarrier side plain) packet.t3bFirstExcluded := by
  let b := packet.firstBranch side
  cases plain with
  | false =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1
    let D := (packet.t3bOriginalPlainSupport hpacket false).extract
      packet.second.physical.first.fullDeletion (packet.realizes_deletionPrime hpacket)
      b.plainDivisor₁ b.witness.1.1 hw.1 hw.2
    change T3b.PlainSupportData _ (packet.firstAtlas side).reindex.plain₁ _
    rw [packet.realizes_firstPlain₁ hpacket side]
    apply D.congrWeight
    intro r I
    change packet.normProfile false (idealNorm K I / packet.firstPlainScale side r false) =
      packet.normProfile false (idealNorm K (b.plainDivisor₁ * I) /
        call.originalPlainScale r false)
    rw [original_norm_quotient b.plainDivisor₁ I _
      (call.t3b_originalPlainScale_pos r false)]
    rfl
  | true =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2
    let D := (packet.t3bOriginalPlainSupport hpacket true).extract
      packet.second.physical.first.fullDeletion (packet.realizes_deletionPrime hpacket)
      b.plainDivisor₂ b.witness.1.2 hw.1 hw.2
    change T3b.PlainSupportData _ (packet.firstAtlas side).reindex.plain₂ _
    rw [packet.realizes_firstPlain₂ hpacket side]
    apply D.congrWeight
    intro r I
    change packet.normProfile true (idealNorm K I / packet.firstPlainScale side r true) =
      packet.normProfile true (idealNorm K (b.plainDivisor₂ * I) /
        call.originalPlainScale r true)
    rw [original_norm_quotient b.plainDivisor₂ I _
      (call.t3b_originalPlainScale_pos r true)]
    rfl

def t3bBeforePlainSupport (phases : OriginalPhaseData packet) (side plain : Bool) :
    T3b.PlainSupportData
      ((packet.t3bUnscaledTable hpacket phases side).t3bPlainWeight plain)
      (packet.t3bBeforePlainCarrier side plain) packet.t3bExcluded := by
  let b := packet.secondBranch side
  have hp : ∀ Q ∈ primeSupport packet.key.1.val.1, Prime Q :=
    fun _ hQ => support_prime hQ
  cases plain with
  | false =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).1
    let D := (packet.t3bFirstPlainSupport hpacket phases side false).extract
      (primeSupport packet.key.1.val.1) hp b.plainDivisor₁ b.witness.1.1 hw.1 hw.2
    have hc : packet.t3bBeforePlainCarrier side false =
        SupportCartesian.plainResidual (packet.firstAtlas side).reindex.plain₁
          (primeSupport packet.key.1.val.1) b.plainExtract₁ := by
      cases side <;> exact OrdinaryOriginalCoordinates.residualReindex_plain₁ _ _ _ _ _ _
    rw [hc]
    apply D.congrWeight
    intro r I
    cases side <;> rfl
  | true =>
    have hw := Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_product.mp b.witness_mem).1).2
    let D := (packet.t3bFirstPlainSupport hpacket phases side true).extract
      (primeSupport packet.key.1.val.1) hp b.plainDivisor₂ b.witness.1.2 hw.1 hw.2
    have hc : packet.t3bBeforePlainCarrier side true =
        SupportCartesian.plainResidual (packet.firstAtlas side).reindex.plain₂
          (primeSupport packet.key.1.val.1) b.plainExtract₂ := by
      cases side <;> exact OrdinaryOriginalCoordinates.residualReindex_plain₂ _ _ _ _ _ _
    rw [hc]
    apply D.congrWeight
    intro r I
    cases side <;> rfl

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bOriginalPlainSupport
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bBeforePlainSupport
