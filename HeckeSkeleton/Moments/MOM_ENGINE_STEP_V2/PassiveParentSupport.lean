import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCarrierFacts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePlainRecovery
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCoverOrigin

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Recovering the actual original parent supports from canonical profiles -/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
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

theorem reference_mem_working :
    seed.reference ∈ pairedRows call.localizedData call.workingParameters call.base := by
  have he : pairedRows call.localizedData call.workingParameters call.base =
      pairedRows call.localizedData call.node.parameters call.base := by
    simp only [pairedRows, Call.workingParameters, sub_add_cancel]
  rw [he, Call.localizedData, EngineInduction.localizeOriginalParent_pairedRows]
  exact seed.reference_mem

def restoredPlainIdeal (side plain : Bool) (I : NonzeroIdeal K) : NonzeroIdeal K :=
  branchDivisor (packet.firstBranch side) plain *
    (branchDivisor (packet.secondBranch side) plain *
      (allocationDivisor (seed.ordinary.originalAllocation side) plain * I))

theorem restoredPlain_argument (side rectangle plain : Bool) (I : NonzeroIdeal K) :
    idealNorm K I / seed.occurrences.plainScale side rectangle plain =
      idealNorm K (seed.restoredPlainIdeal side plain I) /
        call.originalPlainScale rectangle plain := by
  unfold OriginalOccurrenceData.plainScale OriginalOccurrenceData.beforePlainScale
    RawLeafPacket.firstPlainScale restoredPlainIdeal branchDivisor allocationDivisor
  rw [ProfileFormula.divided_scale_argument, ProfileFormula.divided_scale_argument,
    ProfileFormula.divided_scale_argument]

include seed in
theorem first_input_fixed (side plain : Bool) (I : Ideal (𝓞 K))
    (hI : I ∈ branchInput (packet.firstBranch side) plain) :
    IsCoprime I (Arithmetic.data c).cS := by
  cases plain
  · obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hJ).2
  · obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hJ).2

/-- The smooth original argument is exactly the norm of the ideal
before both support extractions and the inner divisor quotient. -/
theorem restoredPlain_mem_parent (side rectangle plain : Bool) (I : NonzeroIdeal K)
    (hprofile : (seed.plainProfile input side rectangle plain).formula.value 0
      (idealNorm K I / seed.occurrences.plainScale side rectangle plain) ≠ 0)
    (hfixed : IsCoprime (seed.restoredPlainIdeal side plain I).val
      (Arithmetic.data c).cS) :
    (seed.restoredPlainIdeal side plain I).val ∈
      branchInput (packet.firstBranch side) plain := by
  have ho := (seed.plainProfile input side rectangle plain).formula.
    original_ne_zero_of_value_ne_zero 0 _ hprofile
  have hd : (seed.plainProfile input side rectangle plain).formula.dilation = 1 := rfl
  rw [hd, one_mul, seed.restoredPlain_argument] at ho
  cases plain
  · have hp := (seed.plainProfile input side rectangle false).left_original rfl
      (idealNorm K (seed.restoredPlainIdeal side false I) /
        call.originalPlainScale rectangle false)
    rw [hp] at ho
    apply Finset.mem_image.mpr
    refine ⟨seed.restoredPlainIdeal side false I, Finset.mem_filter.mpr ⟨?_, hfixed⟩, rfl⟩
    apply parentPlainCarrier_contains
      (pairedRows call.localizedData call.workingParameters call.base)
      call.localizedData.plainTest₁ 0 (call.base ^ call.workingParameters.n₁)
      (call.base ^ call.workingComparison₁) rectangle seed.reference seed.reference_mem_working
    apply (call.localizedData.plainTest₁.support_spec seed.reference 0 _ _).mpr
    simpa only [Call.originalPlainScale, Call.workingParameters, Bool.false_eq_true, ite_false]
      using ho
  · have hp := (seed.plainProfile input side rectangle true).right_original rfl
      (idealNorm K (seed.restoredPlainIdeal side true I) /
        call.originalPlainScale rectangle true)
    rw [hp] at ho
    apply Finset.mem_image.mpr
    refine ⟨seed.restoredPlainIdeal side true I, Finset.mem_filter.mpr ⟨?_, hfixed⟩, rfl⟩
    apply parentPlainCarrier_contains
      (pairedRows call.localizedData call.workingParameters call.base)
      call.localizedData.plainTest₂ 0 (call.base ^ call.workingParameters.n₂)
      (call.base ^ call.workingComparison₂) rectangle seed.reference seed.reference_mem_working
    apply (call.localizedData.plainTest₂.support_spec seed.reference 0 _ _).mpr
    simpa only [Call.originalPlainScale, Call.workingParameters, ite_true]
      using ho

theorem prime_mem_parent (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side))
    (q : HeightOneSpectrum (𝓞 K))
    (hprofile : (seed.primeProfile input side i).formula.value 0
      ((Ideal.absNorm q.asIdeal : ℝ) /
        call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) ≠ 0)
    (hfixed : IsCoprime q.asIdeal (Arithmetic.data c).cS) :
    q ∈ call.workingRaw.exteriorSlots (seed.slotIndex side i) := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hfixed⟩
  have ho := (seed.primeProfile input side i).formula.original_ne_zero_of_value_ne_zero
    0 _ hprofile
  have hd : (seed.primeProfile input side i).formula.dilation = 1 := rfl
  rw [hd, one_mul, (seed.primeProfile input side i).prime_original (seed.slotIndex side i) rfl]
    at ho
  exact ((call.node.data.geometry.slots (seed.slotIndex side i)).support_spec 0 _ q).mpr ho

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.restoredPlain_mem_parent
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.prime_mem_parent
