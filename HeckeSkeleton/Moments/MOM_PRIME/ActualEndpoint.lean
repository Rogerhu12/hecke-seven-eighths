import HeckeSkeleton.Moments.MOM_PRIME.RecipeEndpoint
import Expansion.PhysicalRecipeSchedule

/-!
# The actual detector supplies the endpoint prime-window hypothesis

On the physical line Re z = 17/50 the genuine forward prime-window power
is conjugate(z) - 1.  Its real part is -33/50 at every physical height.
This closes the shared-source absolute endpoint for the actual recipe.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The actual physical line has a fixed nonpositive prime-window power,
independently of all three physical height coordinates. -/
theorem physicalRecipeSlotPower_re (g : PrimeWindowGeometry)
    (j : Fin g.slots) (p : Fin 3 → ℝ) :
    (Expansion.Project.physicalRecipeSlotPower g j p).re = -(33 / 50 : ℝ) := by
  norm_num [Expansion.Project.physicalRecipeSlotPower, Complex.mul_re]


/-- This is a proved property of the concrete detector recipe, not a new
profile-control field or a hypothesis on the final moment bound. -/
theorem actualRecipeSlotPower_nonpos
    (j : Fin c.geometry.slots) (p : Fin 3 → ℝ) :
    ((expansionRecipeRaw K c).family.slotPower j p).re ≤ 0 := by
  change (Expansion.Project.physicalRecipeSlotPower c.geometry j p).re ≤ 0
  rw [physicalRecipeSlotPower_re]
  norm_num

/-- The original source's endpoint with its actual selected models.  The
legacy endpoint's calibration, row-eligibility and profile hypotheses can
remain in its signature; the absolute endpoint already follows here. -/
theorem actual_recipe_paired_primes_endpoint :
    PairedPrimeProductBoundFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) 1 :=
  recipe_paired_primes_endpoint K c (expansionRecipeRaw K c) 0
    (actualRecipeSlotPower_nonpos K c)

end HeckeSkeleton.Moments.MOM_PRIME

#print axioms HeckeSkeleton.Moments.MOM_PRIME.physicalRecipeSlotPower_re
#print axioms HeckeSkeleton.Moments.MOM_PRIME.actualRecipeSlotPower_nonpos
#print axioms HeckeSkeleton.Moments.MOM_PRIME.actual_recipe_paired_primes_endpoint
