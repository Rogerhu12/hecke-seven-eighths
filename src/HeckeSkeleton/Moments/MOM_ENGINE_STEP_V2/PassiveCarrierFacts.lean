module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalAtoms
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSmoothSupport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveMaskIdentity

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Nonzero canonical atoms retain every original support gate -/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace PassiveCarrierFacts

theorem residue_fixed {A : SArithmeticData K} {σ : K →+* ℂ}
    (I : Ideal (𝓞 K)) (h : A.R)
    (hn : actualIdealResidue (A := A) (σ := σ) I h ≠ 0) :
    IsCoprime I A.cS := by
  by_contra hg
  have hbad : ¬(I ≠ 0 ∧ IsCoprime I A.cS) := fun hi => hg hi.2
  exact hn (by simp only [actualIdealResidue, dif_neg hbad])

theorem carrier_nonzero {k : ℕ} (B : PassiveAllocation.Carrier K k)
    (i : AllocationColumn K k) (hi : i ∈ PassiveAllocation.carrierColumns B) :
    i.1.1 ≠ 0 ∧ i.1.2 ≠ 0 := by
  obtain ⟨hp, _⟩ := Finset.mem_product.mp hi
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
  obtain ⟨I, _, hI⟩ := Finset.mem_image.mp hl
  obtain ⟨J, _, hJ⟩ := Finset.mem_image.mp hr
  exact ⟨hI ▸ nonZeroDivisors.coe_ne_zero I, hJ ▸ nonZeroDivisors.coe_ne_zero J⟩

theorem sourceMomentIdeal_val (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (sourceMomentIdeal I).val = I := by
  simp only [sourceMomentIdeal, dif_pos hI]

end PassiveCarrierFacts

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

def canonicalPlainTerm (paid side rectangle : Bool) (h : seed.ordinary.rows.live)
    (plain : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  sourcePlainTerm (σ := Arithmetic.embedding c)
    (seed.phases.characters paid (seed.slotIndex side)).plain
    (seed.phases.characters paid (seed.slotIndex side)).plainTwist
    (seed.phases.characters paid (seed.slotIndex side)).mask
    ((seed.ordinary.originalSource side false).extractedFactor h)
    ((seed.ordinary.originalSource side false).row h).element
    (fun J => (seed.plainProfile input side rectangle plain).formula.value 0
      (idealNorm K J / seed.occurrences.plainScale side rectangle plain))
    (seed.occurrences.plainScale side rectangle plain) I

def canonicalPrimeTerm (paid side : Bool) (h : seed.ordinary.rows.live)
    (i : Fin (seed.ordinary.residualSlotCount side)) (q : HeightOneSpectrum (𝓞 K)) : ℂ :=
  sourcePrimeTerm (σ := Arithmetic.embedding c)
    ((seed.phases.characters paid (seed.slotIndex side)).slot i)
    ((seed.phases.characters paid (seed.slotIndex side)).slotTwist i)
    (seed.phases.characters paid (seed.slotIndex side)).mask
    ((seed.ordinary.originalSource side false).extractedFactor h)
    ((seed.ordinary.originalSource side false).row h).element
    (fun q => (seed.primeProfile input side i).formula.value 0
      ((Ideal.absNorm q.asIdeal : ℝ) /
        call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length))
    (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) q

theorem canonicalCoefficient_terms (paid side rectangle : Bool)
    (h : seed.ordinary.rows.live)
    (i : AllocationColumn K (seed.ordinary.residualSlotCount side)) :
    seed.canonicalCoefficient input paid side rectangle h i =
      seed.canonicalPlainTerm input paid side rectangle h false (sourceMomentIdeal i.1.1) *
      seed.canonicalPlainTerm input paid side rectangle h true (sourceMomentIdeal i.1.2) *
      ∏ j, seed.canonicalPrimeTerm input paid side h j (i.2 j) := rfl

theorem canonicalCoefficient_terms_nonzero (paid side rectangle : Bool)
    (h : seed.ordinary.rows.live)
    (i : AllocationColumn K (seed.ordinary.residualSlotCount side))
    (hn : seed.canonicalCoefficient input paid side rectangle h i ≠ 0) :
    (∀ plain, seed.canonicalPlainTerm input paid side rectangle h plain
      (sourceMomentIdeal (if plain then i.1.2 else i.1.1)) ≠ 0) ∧
    (∀ j, seed.canonicalPrimeTerm input paid side h j (i.2 j) ≠ 0) := by
  rw [seed.canonicalCoefficient_terms input] at hn
  have hp := mul_ne_zero_iff.mp hn
  have hlr := mul_ne_zero_iff.mp hp.1
  refine ⟨?_, ?_⟩
  · intro plain
    cases plain
    · exact hlr.1
    · exact hlr.2
  · intro j
    exact (Finset.prod_ne_zero_iff.mp hp.2) j (Finset.mem_univ j)

theorem canonicalPlainTerm_data (side rectangle plain : Bool)
    (h : seed.ordinary.rows.live) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : seed.canonicalPlainTerm input false side rectangle h plain I ≠ 0) :
    (seed.plainProfile input side rectangle plain).formula.value 0
        (idealNorm K I / seed.occurrences.plainScale side rectangle plain) ≠ 0 ∧
      IsCoprime I.val (Arithmetic.data c).cS ∧
      IsCoprime I.val seed.phases.deletionIdeal.val := by
  have hn' := hn
  simp only [canonicalPlainTerm, sourcePlainTerm, mul_ne_zero_iff] at hn'
  have hc := hn'.2.1.1
  have hr := PassiveCarrierFacts.residue_fixed I.val _ hn'.2.1.2
  have hm : (seed.phases.characters false (seed.slotIndex side)).mask I.val ≠ 0 :=
    (mul_ne_zero_iff.mp hc).2
  have hg : IsCoprime I.val (seed.phases.mask false).val := by
    by_contra hg
    apply hm
    change (if IsCoprime I.val (seed.phases.mask false).val then (1 : ℂ) else 0) = 0
    exact if_neg hg
  have hd : IsCoprime I.val seed.phases.deletionIdeal.val := by
    change IsCoprime I.val (_ * seed.phases.deletionIdeal.val) at hg
    exact hg.of_mul_right_right
  exact ⟨hn'.2.2, hr, hd⟩

theorem canonicalPrimeTerm_data (side : Bool) (h : seed.ordinary.rows.live)
    (i : Fin (seed.ordinary.residualSlotCount side)) (q : HeightOneSpectrum (𝓞 K))
    (hn : seed.canonicalPrimeTerm input false side h i q ≠ 0) :
    (seed.primeProfile input side i).formula.value 0
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) ≠ 0 ∧
      IsCoprime q.asIdeal (Arithmetic.data c).cS ∧
      IsCoprime q.asIdeal seed.phases.deletionIdeal.val := by
  have hn' := hn
  simp only [canonicalPrimeTerm, sourcePrimeTerm, mul_ne_zero_iff] at hn'
  have hc := hn'.2.1.1
  have hr := PassiveCarrierFacts.residue_fixed q.asIdeal _ hn'.2.1.2
  have hm : (seed.phases.characters false (seed.slotIndex side)).mask q.asIdeal ≠ 0 :=
    (mul_ne_zero_iff.mp hc).2
  have hg : IsCoprime q.asIdeal (seed.phases.mask false).val := by
    by_contra hg
    apply hm
    change (if IsCoprime q.asIdeal (seed.phases.mask false).val then (1 : ℂ) else 0) = 0
    exact if_neg hg
  have hd : IsCoprime q.asIdeal seed.phases.deletionIdeal.val := by
    change IsCoprime q.asIdeal (_ * seed.phases.deletionIdeal.val) at hg
    exact hg.of_mul_right_right
  exact ⟨hn'.2.2, hr, hd⟩

theorem canonicalPlainTerm_paid (hpacket : packet.Realizes)
    (side rectangle plain : Bool) (h : seed.ordinary.rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : seed.canonicalPlainTerm input false side rectangle h plain I ≠ 0) :
    IsCoprime I.val packet.second.physical.first.paidSupport.val := by
  by_contra hp
  have hc := (seed.residualMaskIdentity hpacket).plain side I
  dsimp only at hc
  rw [(seed.residualMaskIdentity hpacket).paid_plain_zero side I hp, zero_mul] at hc
  exact hn (by simp only [canonicalPlainTerm, sourcePlainTerm, hc, zero_mul, mul_zero])

theorem canonicalPrimeTerm_paid (hpacket : packet.Realizes)
    (side : Bool) (h : seed.ordinary.rows.live)
    (i : Fin (seed.ordinary.residualSlotCount side)) (q : HeightOneSpectrum (𝓞 K))
    (hn : seed.canonicalPrimeTerm input false side h i q ≠ 0) :
    IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val := by
  by_contra hp
  have hc := (seed.residualMaskIdentity hpacket).prime side i q
  dsimp only at hc
  rw [(seed.residualMaskIdentity hpacket).paid_prime_zero side i q hp, zero_mul] at hc
  exact hn (by simp only [canonicalPrimeTerm, sourcePrimeTerm, hc, zero_mul, mul_zero])

/-- Every nonzero original complete atom lies in the restored carrier.
This uses the original profile supports, and retains both arithmetic gates. -/
theorem canonicalCoefficient_mem_restored (hpacket : packet.Realizes)
    (side rectangle : Bool) (h : seed.ordinary.rows.live)
    (i : AllocationColumn K (seed.ordinary.residualSlotCount side))
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (hn : seed.canonicalCoefficient input false side rectangle h i ≠ 0) :
    i ∈ PassiveAllocation.carrierColumns ((seed.canonicalSupport input).carrier side) := by
  have ht := seed.canonicalCoefficient_terms_nonzero input false side rectangle h i hn
  have hplain (plain : Bool) :
      sourceMomentIdeal (if plain then i.1.2 else i.1.1) ∈
        (seed.canonicalSmoothSupport input side).plainCarrier
          packet.second.physical.first.paidSupport plain := by
    have hd := seed.canonicalPlainTerm_data input side rectangle plain h _ (ht.1 plain)
    apply Finset.mem_filter.mpr
    exact ⟨(seed.canonicalSmoothSupport input side).mem_smoothPlain_of_value_ne_zero
      rectangle plain 0 _ hd.1,
      hd.2.1, seed.canonicalPlainTerm_paid input hpacket side rectangle plain h _ (ht.1 plain)⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨sourceMomentIdeal i.1.1, hplain false,
      PassiveCarrierFacts.sourceMomentIdeal_val _ hleft⟩
  · exact Finset.mem_image.mpr ⟨sourceMomentIdeal i.1.2, hplain true,
      PassiveCarrierFacts.sourceMomentIdeal_val _ hright⟩
  · apply Fintype.mem_piFinset.mpr
    intro j
    have hd := seed.canonicalPrimeTerm_data input side h j (i.2 j) (ht.2 j)
    apply Finset.mem_filter.mpr
    exact ⟨(seed.canonicalSmoothSupport input side).mem_smoothSlot_of_value_ne_zero
      j 0 (i.2 j) hd.1,
      hd.2.1, seed.canonicalPrimeTerm_paid input hpacket side h j (i.2 j) (ht.2 j)⟩

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalCoefficient_mem_restored
