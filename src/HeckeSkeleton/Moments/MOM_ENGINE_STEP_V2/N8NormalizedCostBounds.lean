import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityScalarMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Finite source maxima retain the original arithmetic bounds

The calibration used by N3 stores the actual three finite maxima.  Each
bound below is therefore proved from the original row, scalar or fibre,
without replacing the calibration or choosing larger source data.
These lemmas are used in N8b before summing the original labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ConditionalMoments
open EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {H : Type} {k : ℕ}

namespace OriginalCalibration

variable {call : Call c}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable (D : OriginalCalibration call s)

theorem rowBound_le {bound : ℝ} (bound_nonneg : 0 ≤ bound)
    (h : ∀ r ∈ s.rows, ‖s.weight r‖ ≤ bound) : D.calibration.rowBound ≤ bound := by
  rw [D.row_cost]
  exact SourceCost.row_le s bound_nonneg h

theorem scalarBound_le {bound : ℝ} (bound_nonneg : 0 ≤ bound)
    (h : ∀ r ∈ s.rows, ‖s.frozenScalar (σ := Arithmetic.embedding c) r‖ ^ 2 ≤ bound) :
    D.calibration.scalarBound ≤ bound := by
  rw [D.scalar_cost]
  exact SourceCost.scalar_le s bound_nonneg h

theorem fiberBound_le {bound : ℕ}
    (h : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      (s.rows.filter (fun r => (s.row r).momentIdeal = I)).card ≤ bound) :
    D.calibration.fiberBound ≤ bound := by
  rw [D.fiber_cost]
  exact SourceCost.fiber_le s h

theorem mass_le {rowCost scalarCost : ℝ} {fiberCost : ℕ}
    (row_nonneg : 0 ≤ rowCost) (scalar_nonneg : 0 ≤ scalarCost)
    (row_bound : ∀ r ∈ s.rows, ‖s.weight r‖ ≤ rowCost)
    (scalar_bound : ∀ r ∈ s.rows,
      ‖s.frozenScalar (σ := Arithmetic.embedding c) r‖ ^ 2 ≤ scalarCost)
    (fiber_bound : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      (s.rows.filter (fun r => (s.row r).momentIdeal = I)).card ≤ fiberCost) :
    D.calibration.mass ≤ rowCost * scalarCost * (fiberCost : ℝ) := by
  exact mul_le_mul
    (mul_le_mul (D.rowBound_le row_nonneg row_bound)
      (D.scalarBound_le scalar_nonneg scalar_bound) D.calibration.scalarBound_nonneg row_nonneg)
    (Nat.cast_le.mpr (D.fiberBound_le fiber_bound)) (Nat.cast_nonneg _)
    (mul_nonneg row_nonneg scalar_nonneg)

end OriginalCalibration
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.row_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.scalar_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceCost.fiber_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCalibration.mass_le
