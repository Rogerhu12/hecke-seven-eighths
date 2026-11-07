module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalAllocatedCosts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact finite costs of the original allocated source

The three costs are computed from the finite source itself, including the
empty source. Replacing a calibration's numerical bounds by these maxima
retains its data, parameters, height and all arithmetic and profile
dictionaries. No choice of a larger cost is used by the refinement task.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {H : Type} {k : ℕ}

namespace SourceCost

variable (s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k)

theorem row_nonneg : 0 ≤ row s := NNReal.coe_nonneg _

theorem scalar_nonneg : 0 ≤ scalar s := NNReal.coe_nonneg _

theorem row_bound (h : H) (hh : h ∈ s.rows) : ‖s.weight h‖ ≤ row s := by
  change ((‖s.weight h‖₊ : NNReal) : ℝ) ≤
    ((s.rows.sup (fun j => ‖s.weight j‖₊) : NNReal) : ℝ)
  exact_mod_cast (Finset.le_sup (f := fun j => ‖s.weight j‖₊) hh)

theorem scalar_bound (h : H) (hh : h ∈ s.rows) :
    ‖s.frozenScalar (σ := Arithmetic.embedding c) h‖ ^ 2 ≤ scalar s := by
  change ((‖s.frozenScalar (σ := Arithmetic.embedding c) h‖₊ : NNReal) : ℝ) ^ 2 ≤
    ((s.rows.sup (fun j =>
      ‖s.frozenScalar (σ := Arithmetic.embedding c) j‖₊ ^ (2 : ℕ)) : NNReal) : ℝ)
  exact_mod_cast (Finset.le_sup
    (f := fun j => ‖s.frozenScalar (σ := Arithmetic.embedding c) j‖₊ ^ (2 : ℕ)) hh)

theorem fiber_bound (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fiber s := by
  by_cases hI : (s.rows.filter (fun h => (s.row h).momentIdeal = I)).Nonempty
  · obtain ⟨h, hh⟩ := hI
    obtain ⟨hrow, hideal⟩ := Finset.mem_filter.mp hh
    unfold fiber
    rw [← hideal]
    exact Finset.le_sup
      (f := fun j =>
        (s.rows.filter (fun r => (s.row r).momentIdeal = (s.row j).momentIdeal)).card)
      hrow
  · rw [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.card_empty]
    exact Nat.zero_le _

theorem row_le {bound : ℝ} (hbound : 0 ≤ bound)
    (h : ∀ j ∈ s.rows, ‖s.weight j‖ ≤ bound) : row s ≤ bound := by
  have hs : s.rows.sup (fun j => ‖s.weight j‖₊) ≤ (⟨bound, hbound⟩ : NNReal) := by
    apply Finset.sup_le
    intro j hj
    exact_mod_cast h j hj
  change ((s.rows.sup (fun j => ‖s.weight j‖₊) : NNReal) : ℝ) ≤ bound
  exact_mod_cast hs

theorem scalar_le {bound : ℝ} (hbound : 0 ≤ bound)
    (h : ∀ j ∈ s.rows, ‖s.frozenScalar (σ := Arithmetic.embedding c) j‖ ^ 2 ≤ bound) :
    scalar s ≤ bound := by
  have hs : s.rows.sup (fun j =>
      ‖s.frozenScalar (σ := Arithmetic.embedding c) j‖₊ ^ (2 : ℕ)) ≤
      (⟨bound, hbound⟩ : NNReal) := by
    apply Finset.sup_le
    intro j hj
    exact_mod_cast h j hj
  change ((s.rows.sup (fun j =>
    ‖s.frozenScalar (σ := Arithmetic.embedding c) j‖₊ ^ (2 : ℕ)) : NNReal) : ℝ) ≤ bound
  exact_mod_cast hs

theorem fiber_le {bound : ℕ}
    (h : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      (s.rows.filter (fun j => (s.row j).momentIdeal = I)).card ≤ bound) :
    fiber s ≤ bound := by
  apply Finset.sup_le
  intro j _
  exact h (s.row j).momentIdeal

end SourceCost

namespace ExactCalibrationCosts

variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable (D : s.Calibration (σ := Arithmetic.embedding c)
  c.family.omega (targetCharacter K c))

/-- Fix all numerical costs to the actual finite source maxima. -/
def calibration : s.Calibration (σ := Arithmetic.embedding c)
    c.family.omega (targetCharacter K c) :=
  D.withCosts (SourceCost.row s) (SourceCost.scalar s) (SourceCost.fiber s)
    (SourceCost.row_nonneg s) (SourceCost.scalar_nonneg s)
    (SourceCost.row_bound s) (SourceCost.scalar_bound s) (SourceCost.fiber_bound s)

@[simp] theorem data : (calibration D).data = D.data := rfl

@[simp] theorem parameters : (calibration D).parameters = D.parameters := rfl

@[simp] theorem height : (calibration D).height = D.height := rfl

@[simp] theorem row_cost : (calibration D).rowBound = SourceCost.row s := rfl

@[simp] theorem scalar_cost : (calibration D).scalarBound = SourceCost.scalar s := rfl

@[simp] theorem fiber_cost : (calibration D).fiberBound = SourceCost.fiber s := rfl

theorem mass_le : (calibration D).mass ≤ D.mass := by
  have hrow := SourceCost.row_le s D.rowBound_nonneg D.row_bound
  have hscalar := SourceCost.scalar_le s D.scalarBound_nonneg D.scalar_bound
  have hfiber : (SourceCost.fiber s : ℝ) ≤ D.fiberBound := by
    exact_mod_cast SourceCost.fiber_le s D.fibers
  exact mul_le_mul
    (mul_le_mul hrow hscalar (SourceCost.scalar_nonneg s) D.rowBound_nonneg)
    hfiber (Nat.cast_nonneg _) (mul_nonneg D.rowBound_nonneg D.scalarBound_nonneg)

end ExactCalibrationCosts

namespace OriginalCalibration

variable {call : Call c}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}

/-- Install the precise finite costs after constructing the original
single-atom calibration and both recipes. The underlying profiles and
arithmetic data are definitionally preserved. -/
def ofRaw (D : s.Calibration (σ := Arithmetic.embedding c)
    c.family.omega (targetCharacter K c))
    (recipe : CompleteMovingRowRecipe (Arithmetic.data c)
      (probeData K c) (momentRowCharacters K c) D.data)
    (normProfiles : NormProfileRecipe D.data)
    (base_eq : s.base = call.base)
    (kappa_eq : D.parameters.κ = call.node.parameters.κ)
    (plain_background : ∀ ξ, (D.data ξ).plainBackground = call.node.data.plainBackground)
    (originalSlots : OriginalSlotDictionary call.node.data s.length)
    (theta_eq : ∀ ξ, (D.data ξ).theta = call.node.data.theta)
    (slot_characters : ∀ ξ i, (D.data ξ).slotCoefficient i ∈ call.node.data.theta) :
    OriginalCalibration call s where
  calibration := ExactCalibrationCosts.calibration D
  recipe := recipe
  normProfiles := normProfiles
  base_eq := base_eq
  kappa_eq := kappa_eq
  plain_background := plain_background
  originalSlots := originalSlots
  theta_eq := theta_eq
  slot_characters := slot_characters
  row_cost := rfl
  scalar_cost := rfl
  fiber_cost := rfl

end OriginalCalibration

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.row_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.scalar_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.fiber_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ExactCalibrationCosts.calibration
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ExactCalibrationCosts.mass_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.ofRaw
