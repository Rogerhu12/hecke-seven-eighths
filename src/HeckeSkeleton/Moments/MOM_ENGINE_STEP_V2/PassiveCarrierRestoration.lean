module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveParentSupport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSecondCarrier
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCommonAvoidance
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveFiniteSupport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveColumnBridge

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact restoration of the original finite column energy

Nonzero atoms recover both original support extractions and the old
inner divisor. Conversely, their global profile formula forces them
into the restored smooth support with the same fixed and paid gates.
Only after these exact finite-support identities is the residual mask
separated, with no change to the row set or its complete complex weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open PassivePlainRecovery

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

include seed in
theorem first_plain_input (hpacket : packet.Realizes) (side plain : Bool) :
    branchInput (packet.secondBranch side) plain =
      SupportCartesian.plainResidual (branchInput (packet.firstBranch side) plain)
        packet.second.physical.first.fullDeletion
        (branchDivisor (packet.firstBranch side) plain).val := by
  cases plain
  · exact packet.firstAtlas_plain₁ hpacket side
  · exact packet.firstAtlas_plain₂ hpacket side

theorem second_plain_input (side plain : Bool) :
    allocationInput (seed.ordinary.originalAllocation side) plain =
      SupportCartesian.plainResidual (branchInput (packet.secondBranch side) plain)
        (primeSupport packet.key.1.val.1) (branchDivisor (packet.secondBranch side) plain).val := by
  cases plain
  · exact seed.ordinary.originalAllocation_plain₁ side
  · exact seed.ordinary.originalAllocation_plain₂ side

theorem restoredPlain_fixed (hpacket : packet.Realizes) (side plain : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : IsCoprime I.val (Arithmetic.data c).cS) :
    IsCoprime (seed.restoredPlainIdeal side plain I).val (Arithmetic.data c).cS := by
  have hd := nested_divisor_coprime (packet.firstBranch side) (packet.secondBranch side)
    (seed.ordinary.originalAllocation side) plain
    (seed.first_plain_input hpacket side plain) (seed.second_plain_input side plain)
    (Arithmetic.data c).cS (seed.first_input_fixed side plain)
  have hh := hd.mul_left hI
  change IsCoprime
    (((branchDivisor (packet.firstBranch side) plain).val *
      ((branchDivisor (packet.secondBranch side) plain).val *
        (allocationDivisor (seed.ordinary.originalAllocation side) plain).val)) * I.val)
    (Arithmetic.data c).cS at hh
  change IsCoprime
    ((branchDivisor (packet.firstBranch side) plain).val *
      ((branchDivisor (packet.secondBranch side) plain).val *
        ((allocationDivisor (seed.ordinary.originalAllocation side) plain).val * I.val)))
    (Arithmetic.data c).cS
  simpa only [mul_assoc] using hh

theorem canonicalPlainTerm_mem_originalChild (hpacket : packet.Realizes)
    (side rectangle plain : Bool) (h : seed.ordinary.rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : seed.canonicalPlainTerm input false side rectangle h plain I ≠ 0) :
    I ∈ (seed.originalChildCarrier side).plain plain := by
  have hd := seed.canonicalPlainTerm_data input side rectangle plain h I hn
  have hc : IsCoprime I.val packet.key.1.val.1 :=
    PassiveCommonAvoidance.plainTerm_common_coprime seed.ordinary side false h _ _ _ _ _ I hn
  have hmem := seed.restoredPlain_mem_parent input side rectangle plain I hd.1
    (seed.restoredPlain_fixed hpacket side plain I hd.2.1)
  have hi : I ∈ allocationChild (seed.ordinary.originalAllocation side) plain := by
    apply nested_mem (packet.firstBranch side) (packet.secondBranch side)
      (seed.ordinary.originalAllocation side) plain
      (seed.first_plain_input hpacket side plain) (seed.second_plain_input side plain)
      (packet.fullDeletion_prime hpacket) (fun _ hq => support_prime hq) I
    · intro q hq
      exact hd.2.2.of_prod_right q hq
    · exact PassiveCommonAvoidance.common_prime I.val hc
    · exact hmem
  rw [seed.originalChildCarrier_plain]
  cases plain <;> exact hi

theorem canonicalPrimeTerm_mem_originalChild (hpacket : packet.Realizes)
    (side : Bool) (h : seed.ordinary.rows.live)
    (i : Fin (seed.ordinary.residualSlotCount side)) (q : HeightOneSpectrum (𝓞 K))
    (hn : seed.canonicalPrimeTerm input false side h i q ≠ 0) :
    q ∈ (seed.originalChildCarrier side).slots i := by
  have hd := seed.canonicalPrimeTerm_data input side h i q hn
  have hc : IsCoprime q.asIdeal packet.key.1.val.1 :=
    PassiveCommonAvoidance.primeTerm_common_coprime seed.ordinary side false h _ _ _ _ _ q hn
  rw [seed.originalChildCarrier_slots hpacket]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨seed.prime_mem_parent input side i q hd.1 hd.2.1, ?_⟩, ?_⟩
  · intro hq
    exact q.prime.not_unit (isCoprime_self.mp (hd.2.2.of_prod_right q.asIdeal hq))
  · intro hq
    exact q.prime.not_unit (isCoprime_self.mp
      (PassiveCommonAvoidance.common_prime q.asIdeal hc q.asIdeal hq))

/-- A nonzero globally prescribed original atom reconstructs its actual
old finite quotient carrier, including every retained prime occurrence. -/
theorem canonicalCoefficient_mem_originalChild (hpacket : packet.Realizes)
    (side rectangle : Bool) (h : seed.ordinary.rows.live)
    (i : AllocationColumn K (seed.ordinary.residualSlotCount side))
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (hn : seed.canonicalCoefficient input false side rectangle h i ≠ 0) :
    i ∈ PassiveAllocation.carrierColumns (seed.originalChildCarrier side) := by
  have ht := seed.canonicalCoefficient_terms_nonzero input false side rectangle h i hn
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨sourceMomentIdeal i.1.1,
      seed.canonicalPlainTerm_mem_originalChild input hpacket side rectangle false h _ (ht.1 false),
      PassiveCarrierFacts.sourceMomentIdeal_val _ hleft⟩
  · exact Finset.mem_image.mpr ⟨sourceMomentIdeal i.1.2,
      seed.canonicalPlainTerm_mem_originalChild input hpacket side rectangle true h _ (ht.1 true),
      PassiveCarrierFacts.sourceMomentIdeal_val _ hright⟩
  · exact Fintype.mem_piFinset.mpr fun j =>
      seed.canonicalPrimeTerm_mem_originalChild input hpacket side h j (i.2 j) (ht.2 j)

theorem unscaledOriginal_energy_smooth (hpacket : packet.Realizes)
    (side rectangle : Bool) (ξ : EngineParameter) :
    (seed.unscaledOriginal side rectangle).energy (σ := Arithmetic.embedding c) ξ =
      jointColumnEnergy (seed.ordinary.originalSource side false).rows
        (PassiveAllocation.carrierColumns ((seed.canonicalSupport input).carrier side))
        (seed.canonicalWeight side) (seed.canonicalCoefficient input false side rectangle)
        (fun _ => seed.canonicalLocation side) ξ := by
  rw [seed.unscaledOriginal_energy_canonicalOld input]
  apply PassiveFiniteSupport.energy_replace
  · intro h hh hw i hi
    rfl
  · intro h hh hw i hi
    rfl
  · intro h hh hw i hi hnot
    by_contra hn
    have hne := PassiveCarrierFacts.carrier_nonzero _ i hi
    exact hnot (seed.canonicalCoefficient_mem_restored input hpacket
      side rectangle h i hne.1 hne.2 hn)
  · intro h hh hw i hi hnot
    by_contra hn
    have hne := PassiveCarrierFacts.carrier_nonzero _ i hi
    exact hnot (seed.canonicalCoefficient_mem_originalChild input hpacket
      side rectangle h i hne.1 hne.2 hn)

/-- Exact old energy equals the paid original formula with precisely
the residual deletion gate, on the restored canonical smooth carrier. -/
theorem unscaledOriginal_energy_restored (hpacket : packet.Realizes)
    (side rectangle : Bool) (ξ : EngineParameter) :
    (seed.unscaledOriginal side rectangle).energy (σ := Arithmetic.embedding c) ξ =
      jointColumnEnergy (seed.ordinary.originalSource side false).rows
        ((PassiveAllocation.carrierColumns ((seed.canonicalSupport input).carrier side)).filter
          (fun i => IsCoprime seed.ordinary.passiveMask (PassiveAllocation.columnIdeal i)))
        (seed.canonicalWeight side) (seed.canonicalCoefficient input true side rectangle)
        (fun _ => seed.canonicalLocation side) ξ := by
  rw [seed.unscaledOriginal_energy_smooth input hpacket]
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have he : jointFourierColumn
      (PassiveAllocation.carrierColumns ((seed.canonicalSupport input).carrier side))
      (seed.canonicalCoefficient input false side rectangle h) (seed.canonicalLocation side) ξ =
    jointFourierColumn
      ((PassiveAllocation.carrierColumns ((seed.canonicalSupport input).carrier side)).filter
        (fun i => IsCoprime seed.ordinary.passiveMask (PassiveAllocation.columnIdeal i)))
      (seed.canonicalCoefficient input true side rectangle h) (seed.canonicalLocation side) ξ := by
    exact PassiveColumnBridge.polynomial_residual seed.phases (seed.slotIndex side)
      seed.ordinary (seed.canonicalSmoothSupport input side) hpacket
      ((seed.ordinary.originalSource side false).extractedFactor h)
      ((seed.ordinary.originalSource side false).row h).element
      _ _ _ _ _ _ _ (seed.canonicalLocation side) ξ
  rw [he]

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalCoefficient_mem_originalChild
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.unscaledOriginal_energy_restored
