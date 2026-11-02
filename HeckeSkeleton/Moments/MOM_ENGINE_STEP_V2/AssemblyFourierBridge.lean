import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyLeafConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyMomentDataExt
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AssemblyProfilePhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fourier atom control for the same original normalized leaves

The zero-frequency original profiles already contain their fixed real
powers. Their remaining Fourier dependence is a pure logarithmic phase,
so the original-log-profile atoms have exponent zero. The exact N3 data
identity supplies every arithmetic field and every profile on the whole
real line. N6 supplies the radii of these same selected capacities.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open Blueprint EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

private noncomputable def phaseAtom (seed : OrdinarySeed packet) (side : Bool)
    (scale : ℝ) (hscale : 0 < scale) : CanonicalLogProfiles.Atom EngineParameter where
  scale := scale
  scale_pos := hscale
  exponent := 0
  offset := 0
  direction := WithLp.toLp 2 (seed.logDirection side)

private theorem phaseAtom_multiplier (seed : OrdinarySeed packet) (side : Bool)
    (scale : ℝ) (hscale : 0 < scale) (ξ : EngineParameter) (x : ℝ) :
    (phaseAtom seed side scale hscale).multiplier ξ x =
      jointPhase ξ (Real.log (scale * x) • WithLp.toLp 2 (seed.logDirection side)) := by
  simp only [phaseAtom, CanonicalLogProfiles.Atom.multiplier,
    CanonicalLogProfiles.Atom.location, Real.rpow_zero, Complex.ofReal_one,
    one_mul, zero_add]

private theorem original_profile_phase (seed : OrdinarySeed packet)
    (input : ProfileInput call) (kind : ParentProfileKind call) (side : Bool)
    (scale : ℝ) (hscale : 0 < scale) (absent : Bool)
    (ξ : EngineParameter) (x : ℝ) :
    (seed.profile input kind side scale absent).formula.value ξ x =
      (seed.profile input kind side scale absent).formula.value 0 x *
        jointPhase ξ (Real.log (scale * x) • WithLp.toLp 2 (seed.logDirection side)) := by
  change ((seed.profile input kind side scale absent).formula.atScale
    (seed.logDirection side) scale).value ξ x = _
  exact ProfileFormula.atScale_value _ _ scale hscale ξ x

private theorem original_plain_positive (seed : OrdinarySeed packet)
    (input : ProfileInput call) (side rectangle plain : Bool) (ξ : EngineParameter) :
    CanonicalLogProfiles.PositivePlainProfile
      (CalibrationConstruction.plainTest seed input side rectangle plain ξ) := by
  intro u t x hx
  cases plain <;>
    exact ProfilePhase.argument_pos_of_value_ne_zero _ ξ x hx

private theorem original_prime_positive (seed : OrdinarySeed packet)
    (input : ProfileInput call) (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) (ξ : EngineParameter) :
    CanonicalLogProfiles.PositivePrimeProfile
      (CalibrationConstruction.primeTest seed input side i ξ) := by
  intro t x hx
  exact ProfilePhase.argument_pos_of_value_ne_zero _ ξ x hx

private theorem original_plain_eq (seed : OrdinarySeed packet)
    (input : ProfileInput call) (side rectangle plain : Bool) (ξ : EngineParameter) :
    CalibrationConstruction.plainTest seed input side rectangle plain ξ =
      (phaseAtom seed side (seed.occurrences.plainScale side rectangle plain)
        (seed.occurrences.plainScale_pos side rectangle plain)).idealTest
        (CalibrationConstruction.plainTest seed input side rectangle plain 0)
        (original_plain_positive seed input side rectangle plain 0) ξ := by
  apply idealTest_ext_profile
  funext u t x
  cases plain
  · change (seed.profile input (.plain false) side
        (seed.occurrences.plainScale side rectangle false)
        (rectangle && !call.node.centered && !false)).formula.value ξ x =
      (seed.profile input (.plain false) side
        (seed.occurrences.plainScale side rectangle false)
        (rectangle && !call.node.centered && !false)).formula.value 0 x * _
    rw [phaseAtom_multiplier]
    exact original_profile_phase seed input _ side _
      (seed.occurrences.plainScale_pos side rectangle false) _ ξ x
  · change (seed.profile input (.plain true) side
        (seed.occurrences.plainScale side rectangle true)
        (rectangle && !call.node.centered && !true)).formula.value ξ x =
      (seed.profile input (.plain true) side
        (seed.occurrences.plainScale side rectangle true)
        (rectangle && !call.node.centered && !true)).formula.value 0 x * _
    rw [phaseAtom_multiplier]
    exact original_profile_phase seed input _ side _
      (seed.occurrences.plainScale_pos side rectangle true) _ ξ x

private theorem original_prime_eq (seed : OrdinarySeed packet)
    (input : ProfileInput call) (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) (ξ : EngineParameter) :
    CalibrationConstruction.primeTest seed input side i ξ =
      (phaseAtom seed side
        (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length)
        (Real.rpow_pos_of_pos call.base_pos _)).primeWindow
        (CalibrationConstruction.primeTest seed input side i 0)
        (original_prime_positive seed input side i 0) ξ := by
  apply primeWindow_ext_profile rfl
  funext t x
  change (seed.profile input (.prime (seed.slotIndex side i)) side
      (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length)
      false).formula.value ξ x =
    (seed.profile input (.prime (seed.slotIndex side i)) side
      (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length)
      false).formula.value 0 x * _
  rw [phaseAtom_multiplier]
  exact original_profile_phase seed input _ side _
    (Real.rpow_pos_of_pos call.base_pos _) false ξ x

private theorem original_inverse_eq (seed : OrdinarySeed packet)
    (input : ProfileInput call) (ξ : EngineParameter) :
    CalibrationConstruction.inverseTest seed input ξ =
      CalibrationConstruction.inverseTest seed input 0 := by
  apply idealTest_ext_profile
  funext u t x
  change (seed.inverseProfile input).formula.value ξ x =
    (seed.inverseProfile input).formula.value 0 x
  simp [OrdinarySeed.inverseProfile, ProfileFormula.value, ProfileFormula.linear]

/-- The fixed profile at zero already contains the original norm power.
Only the unit Fourier multiplier is introduced by these atoms. -/
noncomputable def originalLogProfiles (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    CanonicalLogProfiles.OriginalLogProfiles K c.family.omega
      (targetCharacter K c) EngineParameter where
  original := CalibrationAtoms.data seed input support side a rectangle
    (CalibrationClass.pattern packet) (CalibrationClass.sector packet) 0
  left := phaseAtom seed side (seed.occurrences.plainScale side rectangle false)
    (seed.occurrences.plainScale_pos side rectangle false)
  right := phaseAtom seed side (seed.occurrences.plainScale side rectangle true)
    (seed.occurrences.plainScale_pos side rectangle true)
  slot i := phaseAtom seed side
    (call.base ^ (call.node.data.geometry.slots
      (CalibrationConstruction.index seed input support side a i)).length)
    (Real.rpow_pos_of_pos call.base_pos _)
  left_positive := original_plain_positive seed input side rectangle false 0
  right_positive := original_plain_positive seed input side rectangle true 0
  slot_positive i := original_prime_positive seed input side
    (SlotRestriction.index (CalibrationConstruction.allocation seed input support side a).keep i) 0

/-- The whole moment record has exactly the original phase dependence;
its allowed rows, characters, masks and inverse profile remain fixed. -/
theorem originalLogProfiles_moving (seed : OrdinarySeed packet)
    (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool) (ξ : EngineParameter) :
    CalibrationAtoms.data seed input support side a rectangle
      (CalibrationClass.pattern packet) (CalibrationClass.sector packet) ξ =
      (originalLogProfiles seed input support side a rectangle).moving ξ := by
  have hslots :
      (fun i : Fin (CalibrationConstruction.allocation seed input support side a).keep.card =>
        CalibrationConstruction.primeTest seed input side
          (SlotRestriction.index (CalibrationConstruction.allocation seed input support side a).keep i) ξ) =
      (fun i =>
        (phaseAtom seed side
          (call.base ^ (call.node.data.geometry.slots
            (CalibrationConstruction.index seed input support side a i)).length)
          (Real.rpow_pos_of_pos call.base_pos _)).primeWindow
          (CalibrationConstruction.primeTest seed input side
            (SlotRestriction.index (CalibrationConstruction.allocation seed input support side a).keep i) 0)
          (original_prime_positive seed input side
            (SlotRestriction.index (CalibrationConstruction.allocation seed input support side a).keep i) 0) ξ) := by
    funext i
    exact original_prime_eq seed input side _ ξ
  change
    { CalibrationAtoms.data seed input support side a rectangle
        (CalibrationClass.pattern packet) (CalibrationClass.sector packet) 0 with
      inverseTest := CalibrationConstruction.inverseTest seed input ξ
      plainTest₁ := CalibrationConstruction.plainTest seed input side rectangle false ξ
      plainTest₂ := CalibrationConstruction.plainTest seed input side rectangle true ξ
      geometry := CalibrationConstruction.geometry seed input support side a ξ } = _
  rw [original_inverse_eq seed input ξ,
    original_plain_eq seed input side rectangle false ξ,
    original_plain_eq seed input side rectangle true ξ]
  exact congrArg
    (fun slots : Fin (CalibrationConstruction.allocation seed input support side a).keep.card →
        PrimeWindow K =>
      { CalibrationAtoms.data seed input support side a rectangle
          (CalibrationClass.pattern packet) (CalibrationClass.sector packet) 0 with
        plainTest₁ :=
          (phaseAtom seed side (seed.occurrences.plainScale side rectangle false)
            (seed.occurrences.plainScale_pos side rectangle false)).idealTest
            (CalibrationConstruction.plainTest seed input side rectangle false 0)
            (original_plain_positive seed input side rectangle false 0) ξ
        plainTest₂ :=
          (phaseAtom seed side (seed.occurrences.plainScale side rectangle true)
            (seed.occurrences.plainScale_pos side rectangle true)).idealTest
            (CalibrationConstruction.plainTest seed input side rectangle true 0)
            (original_plain_positive seed input side rectangle true 0) ξ
        geometry := ⟨(CalibrationConstruction.allocation seed input support side a).keep.card,
          slots⟩ }) hslots

theorem calibration_data_eq_logProfiles
    (seed : OrdinarySeed packet) (input : ProfileInput call)
    (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (D : OriginalCalibration call (seed.canonicalSource input support side a rectangle))
    (spec : OriginalCalibrationSpec seed input support side a rectangle D)
    (ξ : EngineParameter) :
    D.calibration.data ξ =
      (originalLogProfiles seed input support side a rectangle).moving ξ := by
  rw [spec.data]
  exact originalLogProfiles_moving seed input support side a rectangle ξ

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}
variable {frame : SourceFrame} {orders : Finset (ℕ × ℕ)}

/-- The same N3 data and N6 capacities supply all finite atom controls.
The Fourier degrees are exactly the common N5 degree, on both sides. -/
noncomputable def leafFamilyFourierControl
    (input : ProfileInput call) (raw : RawFamily geometry)
    (choices : FullKappaChoices c p.loss)
    (W : UniformProfileWindowCertificate c frame CalibrationConstruction.shape orders)
    (horders : call.childOrders ⊆ orders)
    (leaves : ∀ j : Fin raw.count,
      LeafNormalization (raw.packet j) input choices W horders) :
    let N := canonicalMassData raw input choices (fun j => (leaves j).massPacket)
    N.family.FourierAtomControl N.labels W.degree W.degree W.degree W.degree := by
  let N := canonicalMassData raw input choices (fun j => (leaves j).massPacket)
  change N.family.FourierAtomControl N.labels W.degree W.degree W.degree W.degree
  refine CanonicalLogProfiles.familyFourierControl N.family N.labels
    (fun b => originalLogProfiles (leaves b.1).seed input (leaves b.1).support
      false b.2.1 b.2.2.2.1)
    (fun b => originalLogProfiles (leaves b.1).seed input (leaves b.1).support
      true b.2.2.1 b.2.2.2.2)
    (fun _ => 0) (fun _ => 0) ?_ ?_ ?_ ?_
    (fun b => ((leaves b.1).normalization false b.2.1 b.2.2.2.1).profiles.coefficient)
    (fun b => ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).profiles.coefficient)
    ?_ ?_ W.degree W.degree W.degree W.degree ?_ ?_
  · intro b ξ
    exact calibration_data_eq_logProfiles (leaves b.1).seed input (leaves b.1).support
      false b.2.1 b.2.2.2.1
      ((leaves b.1).calibrations.side false b.2.1 b.2.2.2.1)
      ((leaves b.1).calibration_actual false b.2.1 b.2.2.2.1) ξ
  · intro b ξ
    exact calibration_data_eq_logProfiles (leaves b.1).seed input (leaves b.1).support
      true b.2.2.1 b.2.2.2.2
      ((leaves b.1).calibrations.side true b.2.2.1 b.2.2.2.2)
      ((leaves b.1).calibration_actual true b.2.2.1 b.2.2.2.2) ξ
  · intro b ξ
    exact ((leaves b.1).calibration_actual false b.2.1 b.2.2.2.1).height ξ
  · intro b ξ
    exact ((leaves b.1).calibration_actual true b.2.2.1 b.2.2.2.2).height ξ
  · intro b _
    exact ((leaves b.1).normalization false b.2.1 b.2.2.2.1).profiles.coefficient_nonnegative
  · intro b _
    exact ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).profiles.coefficient_nonnegative
  · intro b _ z
    simpa only [WithLp.ofLp_toLp] using
      ((leaves b.1).normalization false b.2.1 b.2.2.2.1).capacity_radius (WithLp.toLp 2 z)
  · intro b _ z
    simpa only [WithLp.ofLp_toLp] using
      ((leaves b.1).normalization true b.2.2.1 b.2.2.2.2).capacity_radius (WithLp.toLp 2 z)

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.originalLogProfiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.originalLogProfiles_moving
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.calibration_data_eq_logProfiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.leafFamilyFourierControl
