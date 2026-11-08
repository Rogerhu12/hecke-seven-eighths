module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalCalibrationData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalSupport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationRows
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationPhases
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationFourierProfiles

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Constructing the original child from the canonical residual source

Every test below is made from the source's named parent representative.
The prime geometry is its actual residual keep, and the allowed rows
are exactly the finite image of its original row map. The complete
moving recipe is constructed directly on that image; no enlarged
budget predicate or completed child calibration is supplied as data.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}
variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem profile_bounded (kind : ParentProfileKind call) (side : Bool)
    (scale : ℝ) (absent : Bool) :
    (seed.profile input kind side scale absent).Bounded shape 1 call.window where
  shape_bound := {
    dilation_lower := le_rfl
    dilation_upper := le_rfl
    power := by
      change |-1 + 2 * p.tilt| ≤ 1
      rw [abs_le]
      constructor <;> linarith [p.tilt_pos, p.tilt_half]
    phase_first := by
      change |-(if packet.second.physical.first.firstRight then (-1 : ℝ) else 1)| ≤ 1
      split <;> norm_num
    phase_second := by
      change |(if side then (1 : ℝ) else -1)| ≤ 1
      cases side <;> norm_num }
  scalar := by
    change ‖(if absent then (0 : ℂ) else 1)‖ ≤ 1
    cases absent <;> norm_num
  support := by
    change Set.Icc ((call.prepared.lower / 2) / 1) ((2 * call.prepared.upper) / 1) ⊆
      Set.Icc (call.prepared.lower / 2) (2 * call.prepared.upper)
    simp only [div_one]
    exact Set.Subset.rfl

theorem inverse_bounded : (seed.inverseProfile input).Bounded shape 1 call.window where
  shape_bound := {
    dilation_lower := le_rfl
    dilation_upper := le_rfl
    power := by change |(0 : ℝ)| ≤ 1; norm_num
    phase_first := by change |(0 : ℝ)| ≤ 1; norm_num
    phase_second := by change |(0 : ℝ)| ≤ 1; norm_num }
  scalar := by change ‖(1 : ℂ)‖ ≤ 1; norm_num
  support := by
    change Set.Icc ((call.prepared.lower / 2) / 1) ((2 * call.prepared.upper) / 1) ⊆
      Set.Icc (call.prepared.lower / 2) (2 * call.prepared.upper)
    simp only [div_one]
    exact Set.Subset.rfl

def inverseTest (ξ : EngineParameter) : IdealTest K :=
  (seed.inverseProfile input).inverseTest rfl ξ

def plainTest (side rectangle plain : Bool) (ξ : EngineParameter) : IdealTest K :=
  if plain then (seed.plainProfile input side rectangle true).rightTest rfl ξ
  else (seed.plainProfile input side rectangle false).leftTest rfl ξ

def primeTest (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side))
    (ξ : EngineParameter) : PrimeWindow K :=
  (seed.primeProfile input side i).primeTest (seed.slotIndex side i) rfl ξ

@[simp] theorem inverseTest_profile (ξ : EngineParameter)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t x : ℝ) :
    (inverseTest seed input ξ).profile u t x =
      (seed.inverseProfile input).formula.value ξ x := rfl

@[simp] theorem plainTest_profile (side rectangle plain : Bool) (ξ : EngineParameter)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t x : ℝ) :
    (plainTest seed input side rectangle plain ξ).profile u t x =
      (seed.plainProfile input side rectangle plain).formula.value ξ x := by
  cases plain <;> rfl

@[simp] theorem primeTest_profile (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) (ξ : EngineParameter) (t x : ℝ) :
    (primeTest seed input side i ξ).profile t x =
      (seed.primeProfile input side i).formula.value ξ x := rfl

@[simp] theorem primeTest_length (side : Bool)
    (i : Fin (seed.ordinary.residualSlotCount side)) (ξ : EngineParameter) :
    (primeTest seed input side i ξ).length =
      (call.node.data.geometry.slots (seed.slotIndex side i)).length := rfl

theorem location_eq (side : Bool) (norm : ℝ) :
    seed.location side norm = Real.log norm • WithLp.toLp 2 (seed.logDirection side) :=
  ProfileFormula.scale_translation _ _

variable (support : seed.ordinary.PassiveSupport input)
variable (side : Bool) (a : support.labels side)

abbrev allocation := PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a

def index (i : Fin (allocation seed input support side a).keep.card) :
    Fin call.node.data.geometry.slotCount :=
  seed.slotIndex side (SlotRestriction.index (allocation seed input support side a).keep i)

theorem index_injective : Function.Injective (index seed input support side a) :=
  (seed.slotIndex_injective side).comp
    (PassiveCanonicalSupport.slotRestriction_index_injective _)

def geometry (ξ : EngineParameter) : SlotGeometry K where
  slotCount := (allocation seed input support side a).keep.card
  slots i := primeTest seed input side
    (SlotRestriction.index (allocation seed input support side a).keep i) ξ

@[simp] theorem geometry_length (ξ : EngineParameter)
    (i : Fin (geometry seed input support side a ξ).slotCount) :
    ((geometry seed input support side a ξ).slots i).length =
      (call.node.data.geometry.slots (index seed input support side a i)).length := rfl

variable (rectangle : Bool)

def originalSlots : OriginalSlotDictionary call.node.data
    (seed.canonicalSource input support side a rectangle).length where
  index := ⟨seed.slotIndex side, seed.slotIndex_injective side⟩
  length_eq _ := rfl

/-- Single-ideal profile equality at the exact quotient scale. The
location retains the allocated divisor as part of the original ideal. -/
theorem left_profile (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let s := seed.canonicalSource input support side a rectangle
    s.leftWeight h (s.allocation.plainDivisor 0 * I) *
        jointPhase ξ (s.leftLocation h (s.allocation.plainDivisor 0 * I)) =
      (plainTest seed input side rectangle false ξ).profile (s.row h).momentIdeal 0
        (idealNorm K I / (s.scale₁ / idealNorm K (s.allocation.plainDivisor 0))) := by
  let f := (seed.plainProfile input side rectangle false).formula
  let scale := seed.occurrences.plainScale side rectangle false
  let B := (allocation seed input support side a).plainDivisor 0
  change f.value 0 (idealNorm K (B * I) / scale) *
      jointPhase ξ (seed.location side (idealNorm K (B * I))) =
    f.value ξ (idealNorm K I / (scale / idealNorm K B))
  rw [location_eq]
  symm
  exact ProfileFormula.atScale_quotient f (seed.logDirection side) scale
    (seed.occurrences.plainScale_pos side rectangle false) ξ B I

theorem right_profile (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let s := seed.canonicalSource input support side a rectangle
    s.rightWeight h (s.allocation.plainDivisor (Fin.succ 0) * I) *
        jointPhase ξ (s.rightLocation h (s.allocation.plainDivisor (Fin.succ 0) * I)) =
      (plainTest seed input side rectangle true ξ).profile (s.row h).momentIdeal 0
        (idealNorm K I / (s.scale₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))) := by
  let f := (seed.plainProfile input side rectangle true).formula
  let scale := seed.occurrences.plainScale side rectangle true
  let B := (allocation seed input support side a).plainDivisor (Fin.succ 0)
  change f.value 0 (idealNorm K (B * I) / scale) *
      jointPhase ξ (seed.location side (idealNorm K (B * I))) =
    f.value ξ (idealNorm K I / (scale / idealNorm K B))
  rw [location_eq]
  symm
  exact ProfileFormula.atScale_quotient f (seed.logDirection side) scale
    (seed.occurrences.plainScale_pos side rectangle true) ξ B I

theorem slot_profile (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (i : Fin (geometry seed input support side a ξ).slotCount)
    (q : HeightOneSpectrum (𝓞 K)) :
    let s := seed.canonicalSource input support side a rectangle
    s.slotWeight h (SlotRestriction.index s.allocation.keep i) q *
        jointPhase ξ (s.slotLocation h (SlotRestriction.index s.allocation.keep i) q) =
      ((geometry seed input support side a ξ).slots i).profile 0
        ((Ideal.absNorm q.asIdeal : ℝ) /
          s.base ^ ((geometry seed input support side a ξ).slots i).length) := by
  let j := SlotRestriction.index (allocation seed input support side a).keep i
  let f := (seed.primeProfile input side j).formula
  let scale := call.base ^ (call.node.data.geometry.slots (seed.slotIndex side j)).length
  change f.value 0 ((Ideal.absNorm q.asIdeal : ℝ) / scale) *
      jointPhase ξ (seed.location side (Ideal.absNorm q.asIdeal : ℝ)) =
    f.value ξ ((Ideal.absNorm q.asIdeal : ℝ) / scale)
  rw [location_eq]
  symm
  exact ProfileFormula.atScale_ratio f (seed.logDirection side) scale
    (Real.rpow_pos_of_pos call.base_pos _) ξ _

section Arithmetic

variable (moving : OriginalMovingFactors (Arithmetic.data c)
  (probeData K c) (momentRowCharacters K c))
variable (correction : HeckeCharacter K)
variable (hcorr : correction = 1 ∨ correction ∈ call.node.data.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
  SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The finite row image replaces the auxiliary budget predicate before
the child is exposed. All remaining fields are built from original data. -/
def data (ξ : EngineParameter) : MomentData K c.family.omega (targetCharacter K c) :=
  CalibrationRows.data (seed.canonicalSource input support side a rectangle)
    (CanonicalOriginalChildData.data call.node.data moving correction hcorr sector remaining 0
      (inverseTest seed input ξ) (plainTest seed input side rectangle false ξ)
      (plainTest seed input side rectangle true ξ) (geometry seed input support side a ξ)
      (index seed input support side a))

theorem allowed_exact (ξ : EngineParameter) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (data seed input support side a rectangle moving correction hcorr sector remaining ξ).allowedRow u ↔
      ∃ h ∈ (seed.canonicalSource input support side a rectangle).rows,
        ((seed.canonicalSource input support side a rectangle).row h).momentIdeal = u :=
  CalibrationRows.allowed_exact _ _ _

/-- The exterior certificate comes from the source's original row,
independently of any later support or width bound. -/
def recipe : CompleteMovingRowRecipe (Arithmetic.data c) (probeData K c)
    (momentRowCharacters K c)
    (data seed input support side a rectangle moving correction hcorr sector remaining) where
  moving := moving
  correction := correction
  correction_mem _ := hcorr
  sector := sector
  exterior ξ u hu := by
    obtain ⟨h, _, rfl⟩ :=
      (allowed_exact seed input support side a rectangle moving correction hcorr sector remaining ξ u).mp hu
    exact (HeckeAxiom.exteriorEquiv (Arithmetic.data c)
      ((seed.canonicalSource input support side a rectangle).row h).ideal).property
  character _ _ _ := rfl
  remaining := remaining
  mask _ _ _ := rfl

def normProfiles : NormProfileRecipe
    (data seed input support side a rectangle moving correction hcorr sector remaining) where
  left ξ _ := (seed.plainProfile input side rectangle false).formula.value ξ
  right ξ _ := (seed.plainProfile input side rectangle true).formula.value ξ
  left_eq _ _ _ _ _ := rfl
  right_eq _ _ _ _ _ := rfl

theorem timeIndependent (ξ : EngineParameter) : ProfileTimeIndependent
    (data seed input support side a rectangle moving correction hcorr sector remaining ξ) := by
  constructor <;> intros <;> rfl

theorem primeSupport (ξ : EngineParameter) : PrimeProfileSupport
    (data seed input support side a rectangle moving correction hcorr sector remaining ξ) := by
  intro i t x hx
  let j := SlotRestriction.index (allocation seed input support side a).keep i
  let f := seed.primeProfile input side j
  have hv : f.formula.value ξ x ≠ 0 := hx
  have ho := f.formula.original_ne_zero_of_value_ne_zero ξ x hv
  rw [show f.formula.dilation = 1 from rfl, one_mul,
    f.prime_original (seed.slotIndex side j) rfl] at ho
  exact call.source.primeSupport (seed.slotIndex side j) 0 ho

/-- All equalities hold globally in the profile argument. The scalar
allowance is exactly one after the original common scalar was moved
outside the source by the canonical refinement definition. -/
def dictionary : GlobalProfileDictionary input
    (data seed input support side a rectangle moving correction hcorr sector remaining)
    (allocation seed input support side a).keep.card (fun _ => rfl) shape 1 call.window where
  slotEmbedding := index seed input support side a
  slotEmbedding_injective := index_injective seed input support side a
  inverse _ _ := seed.inverseProfile input
  plain plain _ _ := seed.plainProfile input side rectangle plain
  prime i _ := seed.primeProfile input side
    (SlotRestriction.index (allocation seed input support side a).keep i)
  inverse_kind _ _ := rfl
  plain_kind _ _ _ := rfl
  prime_kind _ _ := rfl
  inverse_bounded _ _ := inverse_bounded seed input
  plain_bounded plain _ _ := profile_bounded seed input (.plain plain) side
    (seed.occurrences.plainScale side rectangle plain)
    (rectangle && !call.node.centered && !plain)
  prime_bounded i _ := profile_bounded seed input
    (.prime (index seed input support side a i)) side
    (call.base ^ (call.node.data.geometry.slots (index seed input support side a i)).length) false
  inverse_eq _ _ _ _ := rfl
  left_eq _ _ _ _ := rfl
  right_eq _ _ _ _ := rfl
  prime_eq _ _ _ _ := rfl

end Arithmetic
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.left_profile
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.slot_profile
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.recipe
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.normProfiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.timeIndependent
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.primeSupport
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationConstruction.dictionary
