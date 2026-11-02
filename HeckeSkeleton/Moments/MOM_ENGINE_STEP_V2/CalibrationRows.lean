import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationCosts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact finite image of the original source rows

The source's actual row map determines the new allowed predicate and
every norm cutoff. The arithmetic coefficients and all global profiles
stay fixed. Calibration and both recipes descend to this exact finite
image, so removing slots cannot introduce additional arithmetic rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationRows

open EngineStep EngineInduction EngineInduction.Source
open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type} {k : ℕ}
variable {ω ψ : HeckeCharacter K}

def image (s : ActualAllocatedSource A EngineParameter H k) : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  s.rows.image (fun h => (s.row h).momentIdeal)

def data (s : ActualAllocatedSource A EngineParameter H k) (d : MomentData K ω ψ) :
    MomentData K ω ψ :=
  { d with
    allowedRow := fun u => u ∈ image s
    rows := fun U => (image s).filter (fun u => idealNorm K u ≤ U)
    rows_spec := fun U u => by rw [Finset.mem_filter] }

theorem allowed_exact (s : ActualAllocatedSource A EngineParameter H k)
    (d : MomentData K ω ψ) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (data s d).allowedRow u ↔ ∃ h ∈ s.rows, (s.row h).momentIdeal = u :=
  Finset.mem_image

theorem allowed_source (s : ActualAllocatedSource A EngineParameter H k)
    (d : MomentData K ω ψ) (h : H) (hh : h ∈ s.rows) :
    (data s d).allowedRow (s.row h).momentIdeal :=
  Finset.mem_image.mpr ⟨h, hh, rfl⟩

variable {s : ActualAllocatedSource A EngineParameter H k}
variable (D : s.Calibration (σ := σ) ω ψ)

theorem allowed_subset (ξ : EngineParameter) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : (data s (D.data ξ)).allowedRow u) : (D.data ξ).allowedRow u := by
  obtain ⟨h, hh, rfl⟩ := (allowed_exact s (D.data ξ) u).mp hu
  exact D.allowed ξ h hh

/-- Every source field is unchanged; only the child's exhaustive ideal
enumeration is narrowed to the exact image of those source fields. -/
def calibration : s.Calibration (σ := σ) ω ψ where
  data ξ := data s (D.data ξ)
  parameters := D.parameters
  height := D.height
  count := D.count
  lengths := D.lengths
  left_scale := D.left_scale
  right_scale := D.right_scale
  slot_sum := D.slot_sum
  dictionary ξ h :=
    { fixedRay_mem_theta := (D.dictionary ξ h).fixedRay_mem_theta
      plain := (D.dictionary ξ h).plain
      slot := (D.dictionary ξ h).slot }
  left_support := D.left_support
  right_support := D.right_support
  slot_support := D.slot_support
  left_profile := D.left_profile
  right_profile := D.right_profile
  slot_profile := D.slot_profile
  allowed ξ h hh := allowed_source s (D.data ξ) h hh
  cutoff := D.cutoff
  nonexceptional := D.nonexceptional
  rowBound := D.rowBound
  rowBound_nonneg := D.rowBound_nonneg
  row_bound := D.row_bound
  scalarBound := D.scalarBound
  scalarBound_nonneg := D.scalarBound_nonneg
  scalar_bound := D.scalar_bound
  fiberBound := D.fiberBound
  fibers := D.fibers
  principal_in_theta := D.principal_in_theta
  slot_in_theta := D.slot_in_theta

theorem calibration_allowed (ξ : EngineParameter) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((calibration D).data ξ).allowedRow u ↔
      ∃ h ∈ s.rows, (s.row h).momentIdeal = u :=
  allowed_exact s (D.data ξ) u

@[simp] theorem calibration_parameters : (calibration D).parameters = D.parameters := rfl

@[simp] theorem calibration_height : (calibration D).height = D.height := rfl

@[simp] theorem calibration_mass : (calibration D).mass = D.mass := rfl

def recipe {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (Q : CompleteMovingRowRecipe A P R D.data) :
    CompleteMovingRowRecipe A P R (calibration D).data :=
  Q.ofAllowedSubset (allowed_subset D) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def normProfiles (W : NormProfileRecipe D.data) : NormProfileRecipe (calibration D).data where
  left := W.left
  right := W.right
  left_eq ξ u hu := W.left_eq ξ u (allowed_subset D ξ u hu)
  right_eq ξ u hu := W.right_eq ξ u (allowed_subset D ξ u hu)

theorem recipe_fullJointBudget
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (Q : CompleteMovingRowRecipe A P R D.data) (Z width : ℝ)
    (hbudget : Q.FullJointBudget Z width) :
    (recipe D Q).FullJointBudget Z width := by
  intro ξ u hu
  exact hbudget ξ u (allowed_subset D ξ u hu)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationRows

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration

open EngineStep EngineInduction EngineInduction.Source NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable (D : OriginalCalibration call s)

/-- The actual finite row image, with the original recipes and costs. -/
def exactRows : OriginalCalibration call s where
  calibration := CalibrationRows.calibration D.calibration
  recipe := CalibrationRows.recipe D.calibration D.recipe
  normProfiles := CalibrationRows.normProfiles D.calibration D.normProfiles
  base_eq := D.base_eq
  kappa_eq := D.kappa_eq
  plain_background := D.plain_background
  originalSlots := D.originalSlots
  theta_eq := D.theta_eq
  slot_characters := D.slot_characters
  row_cost := D.row_cost
  scalar_cost := D.scalar_cost
  fiber_cost := D.fiber_cost

theorem exactRows_allowed (ξ : EngineParameter) (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (D.exactRows.calibration.data ξ).allowedRow u ↔
      ∃ h ∈ s.rows, (s.row h).momentIdeal = u :=
  CalibrationRows.calibration_allowed D.calibration ξ u

@[simp] theorem exactRows_parameters :
    D.exactRows.calibration.parameters = D.calibration.parameters := rfl

@[simp] theorem exactRows_mass : D.exactRows.calibration.mass = D.calibration.mass := rfl

def exactRows_rawDictionary {input : ProfileInput call} {shape : ProfileShape}
    {scalarBound : ℝ} {window : Set ℝ} (dictionary : D.RawDictionary input shape scalarBound window) :
    D.exactRows.RawDictionary input shape scalarBound window where
  slotEmbedding := dictionary.slotEmbedding
  slotEmbedding_injective := dictionary.slotEmbedding_injective
  inverse := dictionary.inverse
  plain := dictionary.plain
  prime := dictionary.prime
  inverse_kind := dictionary.inverse_kind
  plain_kind := dictionary.plain_kind
  prime_kind := dictionary.prime_kind
  inverse_bounded := dictionary.inverse_bounded
  plain_bounded := dictionary.plain_bounded
  prime_bounded := dictionary.prime_bounded
  inverse_eq := dictionary.inverse_eq
  left_eq := dictionary.left_eq
  right_eq := dictionary.right_eq
  prime_eq := dictionary.prime_eq

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationRows.calibration
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationRows.recipe
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.exactRows
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.exactRows_allowed
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.exactRows_rawDictionary
