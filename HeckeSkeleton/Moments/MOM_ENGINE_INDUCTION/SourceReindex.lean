import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceData
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorReindex

/-!
# Reindexing the canonical source's actual paired polynomial

The finite-sector theorem from `MOM_UNIFORM_AMPLIFY` is applied to the
canonical source's original witness rows, both calibrated plain profiles,
and its entire selected slot product. The row map keeps both ideal and
sector, and its injectivity and membership are the original source-row
eligibility facts. No completed energy comparison is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {S : MomentSourceData K c}
variable {R : RowCharacterInput K (places K c) (probeData K c)}

local instance : Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The original pointwise calibration and row inclusion give the complete
paired energy comparison, with every finite unit sector retained. -/
theorem paired_source_reindex (M : SourceMomentModelsFor K c S)
    (hcal : SourcePolynomialCalibrationFor R M) (hrows : SourceRowEligibilityFor M)
    (Z T : ℝ) (i : SourceMomentIndexFor K c S Z T) :
    physicalPlainEnergyFor i ≤ pairedModelEnergyFor M i := by
  exact UniformAmplify.paired_finite_sector_reindex
    (momentWitnessFor i).rows
    (fun u : FrequencyRow K (places K c) => u.ideal.val) (fun u => u.sector)
    (pairedModelFor M i) (pairedParametersFor i) (momentBaseFor i) 0
    (momentWitnessFor i).plainValue
    (fun u => ∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u)
    hrows.fiber (hrows.paired_rows Z T i)
    (hcal.plain₁ Z T i) (hcal.plain₂ Z T i) (hcal.paired_slots Z T i)

end HeckeSkeleton.Moments.EngineInduction.Source
