import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyLeafConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyArithmeticBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyNormalizationGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyFourierBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N9OriginalWindowContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizationCertificate

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# All normalization tasks yield their internal assembly certificate

The N4 scale demand is selected separately from the arithmetic cost.
One N6 choice is used for every order set. N5 and N9 are then selected
at each fixed order set, before the moving call and its raw leaves.
The original N5 windows are retained: N8 and N9 receive two views of
the same leaf records and therefore the same normalized capacities.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction.Source Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

/-- This is a derived certificate. Its only mathematical premises are
the named normalization tasks and the same original N8a ledger. -/
theorem normalizationCertificate_of_tasks (c : TargetContext K)
    (p : SourceParameters c) (frame : SourceFrame)
    (atoms : OriginalAtomTask c p)
    (refinement : PassiveRefinementTask c p)
    (calibration : OriginalCalibrationTask c p)
    (capacity : UniformOriginalCapacityTask c p)
    (profileWindows : ProfileWindowTask c)
    (fullKappa : FullKappaTask c)
    (childArithmetic : ChildArithmeticTask c p)
    (childProfiles : ChildProfileTask c p)
    (sourceIndex : SourceIndexTask c p)
    (normalizedMass : NormalizedMassTask c p)
    (kernelMass : OriginalWindowKernelMassTask c p) :
    Nonempty (NormalizationCertificate c frame p) := by
  classical
  obtain ⟨capacityDemand, produceCapacity⟩ := capacityProducer_exists capacity frame
  obtain ⟨choices, normalize⟩ := fullKappaProducer_exists fullKappa p.loss p.loss_pos
  obtain ⟨arithmeticCost, arithmeticBound⟩ :=
    canonicalArithmeticMass_of_blueprintTasks c p sourceIndex normalizedMass frame
  let W (orders : Finset (ℕ × ℕ)) :
      UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders :=
    Classical.choice (profileWindows frame CalibrationConstruction.shape orders)
  have kernelSpecification (orders : Finset (ℕ × ℕ)) :=
    kernelMass frame CalibrationConstruction.shape orders choices (W orders)
  let profileCost (orders : Finset (ℕ × ℕ)) : UniformCost :=
    Classical.choose (kernelSpecification orders)
  let profileDemand (orders : Finset (ℕ × ℕ)) : UniformDemand :=
    { orders := (W orders).inputOrders
      threshold := 1
      threshold_one_le := le_rfl }
  refine ⟨{
    demand := fun orders => capacityDemand.join (profileDemand orders)
    degree := fun orders => (W orders).degree
    arithmeticCost := fun _ => arithmeticCost
    profileCost := profileCost
    produce := ?_ }⟩
  intro call input hframe ready arithmeticReady profileReady
    trace htrace geometry hgeometry raw hraw
  let orders := call.childOrders
  have horders : call.childOrders ⊆ orders := Finset.Subset.refl _
  have inputOrders : (W orders).inputOrders ⊆ input.orders := ready.ready_right.orders
  let leaves (j : Fin raw.count) :
      LeafNormalization (raw.packet j) input choices (W orders) horders :=
    Classical.choice (leafNormalization_of_tasks atoms refinement calibration
      frame capacityDemand produceCapacity choices normalize orders (W orders)
      call input hframe ready.ready_left inputOrders horders (raw.packet j)
      (RawFamily.packet_realizes trace htrace hgeometry raw hraw j))
  let packets := fun j => (leaves j).massPacket
  let O := fun j => (leaves j).seed.ordinary
  let R := fun j => (leaves j).seed.refinement input (leaves j).support
  let C := fun j => (leaves j).calibrations
  let G := fun j => (leaves j).capacities
  let N := canonicalMassData raw input choices packets
  have ordinary : raw.normalizedOrdinary ≤ N.sourceBudget :=
    ordinaryBudget_le_refinedSourceBudget raw O R C G
      (fun j => (leaves j).refinement_bound)
  obtain ⟨outputGeometry, admissible⟩ :=
    canonicalOutputAndRecursive childArithmetic childProfiles input trace htrace
      geometry hgeometry raw hraw choices packets
  have arithmetic : N.arithmeticMass ≤
      arithmeticCost.value input.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) :=
    arithmeticBound call input hframe arithmeticReady trace htrace
      geometry hgeometry raw hraw choices packets
  have kernel := (Classical.choose_spec (kernelSpecification orders)).2.2
    call input hframe horders profileReady trace htrace geometry raw O R C
      (fun j => (leaves j).windows) (fun j => (leaves j).fullKappaResults)
  have profile : N.kernelMass ≤
      (profileCost orders).value input.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) * N.arithmeticMass :=
    kernel.2.2
  exact ⟨{
    data := N
    geometry := outputGeometry
    atoms := leafFamilyFourierControl input raw choices (W orders) horders leaves
    admissible := admissible
    ordinary := ordinary
    arithmetic := arithmetic
    profile := profile }⟩

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.normalizationCertificate_of_tasks
