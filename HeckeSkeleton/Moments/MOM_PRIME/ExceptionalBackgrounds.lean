import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalNormReduction
import HeckeSkeleton.ExpansionModels.SourceData

/-!
# Norm reduction of the actual plain-row backgrounds

The actual target lies on the radial-zero slice constructed by the source
owner. The selected paired model therefore inherits the generic norm-reduction
certificate. This module also re-exports the fixed-background and plain-row
results from `ExceptionalNormReduction` for compatibility with existing imports.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The original selected paired model supplies its own norm-reduction
certificate; no profile or energy estimate is an input. -/
theorem actual_paired_row_normReduced (c : TargetContext K)
    {Z T : ℝ}
    (i : SourceMomentIndexFor K c
      (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) :
    ExceptionalNormReduced K
      ((pairedModelFor (recipeMomentModels K c (expansionRecipeRaw K c)) i s).plainBackground *
        (pairedModelFor (recipeMomentModels K c (expansionRecipeRaw K c)) i s).rowCharacter u) :=
  exceptionalNormReduced_plain_row K _ (normNormalizationPlace K)
    (targetCharacter_radial_zero K c) u

end HeckeSkeleton.Moments.MOM_PRIME
