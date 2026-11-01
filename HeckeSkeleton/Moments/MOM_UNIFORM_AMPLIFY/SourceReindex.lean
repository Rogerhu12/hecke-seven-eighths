import HeckeSkeleton.SourceData
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FiniteSectorReindex

/-!
# Finite sector reindexing for one fixed all-scale source

The source, its original witness rows, its row-enumeration exponent and all
three families of actual moment polynomials remain fixed throughout the
comparison.  In particular the inverse ball is `U ^ rowWidthFor i`; the
dyadic factor of two is not discarded by replacing that exponent with one.

Only literal polynomial calibration, exact row membership and the original
ideal/sector embedding are used.  No moment estimate is an input.  This
module imports the explicit source interface and fixes every source datum
before the comparison, giving an independently auditable theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {E : MomentSourceData K c}

local instance sourceReindexSectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The three physical energies embed in the corresponding complete sector
sums of the same source.  Both paired plain factors and the unmarked
sixth-free filter are retained, with the source's actual row exponent. -/
theorem source_moment_finite_sector_reindex
    (M : SourceMomentModelsFor K c E)
    {R : RowCharacterInput K (places K c) (probeData K c)}
    (hcal : SourcePolynomialCalibrationFor R M)
    (hrows : SourceRowEligibilityFor M) :
    ∀ Z T (i : SourceMomentIndexFor K c E Z T),
      physicalInverseEnergyFor i ≤ markedModelEnergyFor M i ∧
      physicalPlainEnergyFor i ≤ pairedModelEnergyFor M i ∧
      physicalUnmarkedEnergyFor i ≤ amplifiedModelEnergyFor M i := by
  intro Z T i
  refine ⟨?_, ?_, ?_⟩
  · exact inverse_finite_sector_reindex
      (momentWitnessFor i).rows (fun u => u.ideal.val) (fun u => u.sector)
      (inverseModelFor M i) (inverseParametersFor i) (momentBaseFor i) 0
      (momentWitnessFor i).inverseValue
      (fun u => ∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u)
      hrows.fiber (hrows.inverse_rows Z T i)
      (hcal.inverse Z T i) (hcal.inverse_slots Z T i)
  · exact paired_finite_sector_reindex
      (momentWitnessFor i).rows (fun u => u.ideal.val) (fun u => u.sector)
      (pairedModelFor M i) (pairedParametersFor i) (momentBaseFor i) 0
      (momentWitnessFor i).plainValue
      (fun u => ∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u)
      hrows.fiber (hrows.paired_rows Z T i)
      (hcal.plain₁ Z T i) (hcal.plain₂ Z T i) (hcal.paired_slots Z T i)
  · exact unmarked_finite_sector_reindex
      (momentWitnessFor i).rows (fun u => u.ideal.val) (fun u => u.sector)
      (unmarkedModelFor M i) (momentBaseFor i)
      ((momentBaseFor i) ^ (momentWitnessFor i).inverseLength) 0
      (momentWitnessFor i).inverseValue hrows.fiber
      (hrows.unmarked_rows Z T i) (hcal.unmarked Z T i)

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.source_moment_finite_sector_reindex
