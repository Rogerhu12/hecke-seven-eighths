import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedClosure

/-!
# Canonical inverse bounds for the original expansion recipe

The marked source and the complete-row, all-smaller-scale unmarked seed
are proved for the same literal recipe models. Both use the original
quadratic and cubic sieve inputs through the actual Poisson providers,
the reflected short source and finite canonical induction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceModelClosure

open NumberField
open HeckeGeneral.Analysis
open HeckeSkeleton.LowEnergy.ActualSieveDictionary

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- Both original canonical obligations, with no extra source-energy
or endpoint-bound premise. The recipe and its complete row domain are
the same ones used by the original skeleton declaration. -/
theorem actual_canonical_inverse_models
    (hquadratic : ExteriorQuadraticBound K (places K c) (probeData K c).arithmetic)
    (hcubic : ExteriorCubicBound K (places K c) (probeData K c).arithmetic) :
    CanonicalInverseModelBoundsFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) := by
  exact {
    marked := SourceMarkedClosure.actual_marked_bound K c hquadratic hcubic
    unmarked_strict :=
      SourceCanonicalClosure.actual_complete_unmarked_scale_sup K c hquadratic hcubic }

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceModelClosure

end
