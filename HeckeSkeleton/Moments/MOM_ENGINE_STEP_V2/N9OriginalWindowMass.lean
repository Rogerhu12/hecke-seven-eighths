import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalWindowContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9ClippedRadiusData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9FullKappaMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9UniformCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9ReserveBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact N5b/N6 adapter and the original-window N9 theorem

Source activity comes from membership in the existing active family.
The N5b coefficient bound is its `active_cost`, and the radius identity
is the same N6 result's `capacity_radius`.  The pre-removal slot bound
comes from the original calibration's injective slot dictionary.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep EngineInduction.Source
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

theorem UniformProfileWindowCertificate.kernelInputCost_value
    {frame : SourceFrame} {shape : ProfileShape} {orders : Finset (ℕ × ℕ)}
    (certificate : UniformProfileWindowCertificate c frame shape orders)
    (amplitude height : ℝ) :
    certificate.kernelInputCost.value amplitude height =
      certificate.costCoefficient * amplitude * (1 + 1) := by
  simp only [UniformProfileWindowCertificate.kernelInputCost, UniformCost.value,
    pow_one, Real.rpow_zero, mul_one]
  ring

theorem OriginalCalibration.source_slots_le {H : Type} {k : ℕ}
    {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
    (D : OriginalCalibration call s) : s.allocation.keep.card ≤ c.geometry.slots := by
  have hk : k ≤ call.node.data.geometry.slotCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective D.originalSlots.index D.originalSlots.index.injective
  have hkeep : s.allocation.keep.card ≤ k := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ s.allocation.keep
  exact hkeep.trans (hk.trans call.slots_le)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep
open NumberField MeasureTheory HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {input : ProfileInput call} {trace : SourceTrace call p}
variable {geometry : GeometryFamily trace.second}
variable {frame : SourceFrame} {shape : ProfileShape} {orders : Finset (ℕ × ℕ)}
variable (choices : FullKappaChoices c p.loss)
variable (certificate : UniformProfileWindowCertificate c frame shape orders)
variable (horders : call.childOrders ⊆ orders)
variable (raw : RawFamily geometry)
variable (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
variable (R : ∀ j, RefinementData (O j) input) (C : ∀ j, (R j).Calibrations)
variable (windows : ∀ j, (C j).ProfileWindows orders
  (certificate.coefficient * input.amplitude * 1)
  (certificate.costCoefficient * input.amplitude * (1 + 1)) certificate.degree)
variable (results : ∀ j, (C j).FullKappaResults choices horders (windows j))

/-- Every field is projected from the same original upstream records;
the active bounds are not additional hypotheses. -/
def originalWindowRadiusData :
    ClippedKernelRadiusData
      (refinedNormalizedData raw O R C (fun j => (C j).fullKappaCapacities (results j)))
      orders c.geometry.slots certificate.degree certificate.degree
      certificate.degree certificate.degree
      (certificate.kernelInputCost.value input.amplitude call.request.height)
      (fullKappaKernelRadius choices call) where
  leftRawCoefficient _ := certificate.coefficient * input.amplitude * 1
  rightRawCoefficient _ := certificate.coefficient * input.amplitude * 1
  left_raw_nonneg _ := mul_nonneg
    (mul_nonneg certificate.coefficient_pos.le (zero_le_one.trans input.amplitude_one_le))
    zero_le_one
  right_raw_nonneg _ := mul_nonneg
    (mul_nonneg certificate.coefficient_pos.le (zero_le_one.trans input.amplitude_one_le))
    zero_le_one
  left_active_bound b := by
    change ((C b.val.1).side false b.val.2.1 b.val.2.2.2.1).profileRadiusCoefficient
      orders (certificate.coefficient * input.amplitude * 1) ≤ _
    rw [certificate.kernelInputCost_value]
    exact (windows b.val.1 false b.val.2.1 b.val.2.2.2.1).active_cost
      (Finset.mem_filter.mp b.property).2.1
  right_active_bound b := by
    change ((C b.val.1).side true b.val.2.2.1 b.val.2.2.2.2).profileRadiusCoefficient
      orders (certificate.coefficient * input.amplitude * 1) ≤ _
    rw [certificate.kernelInputCost_value]
    exact (windows b.val.1 true b.val.2.2.1 b.val.2.2.2.2).active_cost
      (Finset.mem_filter.mp b.property).2.2
  left_slots b := ((C b.val.1).side false b.val.2.1 b.val.2.2.2.1).source_slots_le
  right_slots b := ((C b.val.1).side true b.val.2.2.1 b.val.2.2.2.2).source_slots_le
  left_radius b z :=
    (results b.val.1 false b.val.2.1 b.val.2.2.2.1).2.capacity_radius_at_call z
  right_radius b z :=
    (results b.val.1 true b.val.2.2.1 b.val.2.2.2.2).2.capacity_radius_at_call z

end HeckeSkeleton.Moments.EngineStepV2.Assembly

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField MeasureTheory EngineStep
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

theorem originalWindowKernelMass (c : TargetContext K) (p : SourceParameters c) :
    OriginalWindowKernelMassTask c p := by
  intro frame shape orders choices certificate
  obtain ⟨coefficient, hcoefficient, bound⟩ :=
    fullKappaKernelMass c p choices certificate.degree certificate.degree
      certificate.degree certificate.degree
  refine ⟨certificate.kernelInputCost.kernelPower coefficient hcoefficient.le
    (fullKappaProfilePower c), rfl, rfl, ?_⟩
  intro call input _frame horders _ready trace htrace geometry raw O R C windows results
  let G := fun j => (C j).fullKappaCapacities (results j)
  let N := Assembly.refinedNormalizedData raw O R C G
  let D := Assembly.originalWindowRadiusData choices certificate horders raw O R C windows results
  have hB : 0 ≤ certificate.kernelInputCost.value input.amplitude call.request.height :=
    certificate.kernelInputCost.value_nonneg (zero_le_one.trans input.amplitude_one_le)
      call.request.height_nonneg
  obtain ⟨integrable, finite, mass⟩ :=
    bound call input trace htrace geometry raw O R C G
      (certificate.kernelInputCost.value input.amplitude call.request.height) hB
      D.toKernelRadiusData
  refine ⟨?_, finite, ?_⟩
  · intro b
    exact (integrable b).congr (Filter.Eventually.of_forall
      (fun z => (D.toKernelRadiusData.envelope_eq b z).symm))
  · exact kernelMass_le_uniformCost N input certificate.kernelInputCost coefficient
      hcoefficient.le (fullKappaProfilePower c)
      (certificate.kernelInputCost.value input.amplitude call.request.height)
      p.loss hB le_rfl p.loss_le_edgeLoss_half mass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.source_slots_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.originalWindowRadiusData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.originalWindowKernelMass
