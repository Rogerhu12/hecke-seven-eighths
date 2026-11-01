import HeckeSkeleton.ExpansionModels.ActualRowEligibility
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceReindex

/-!
# The actual recipe satisfies the finite sector comparison

The all-label row eligibility theorem and the literal polynomial identities
are produced by the same actual recipe.  Substitution into the explicit
source theorem leaves no calibration or row-eligibility assumption at this
entry point.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)

/-- The same actual source, with all its original rows, is bounded by its
three corresponding complete finite sector sums. -/
theorem actual_source_moment_finite_sector_reindex :
    ∀ Z T (i : SourceMomentIndexFor K c Source Z T),
      physicalInverseEnergyFor i ≤ markedModelEnergyFor Models i ∧
      physicalPlainEnergyFor i ≤ pairedModelEnergyFor Models i ∧
      physicalUnmarkedEnergyFor i ≤ amplifiedModelEnergyFor Models i :=
  source_moment_finite_sector_reindex Models
    (recipeMoment_polynomial_calibration K c (expansionRecipeRaw K c))
    (actualRecipeRowEligibility K c)

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_source_moment_finite_sector_reindex
