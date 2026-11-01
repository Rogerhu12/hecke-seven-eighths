import HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.Conductor
import HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.Windows
import HeckeSkeleton.Moments.MOM_PRIME.RecipeEndpoint
import HeckeSkeleton.PrimeCancellationWiring

/-!
# Prime cancellation below one for the actual expansion recipe

Every field of `PrimeSlotModelControl` is proved for the original selected
models. The fixed prime weights, their physical twists, and the complete
paired-row conductor bound supply the existing finite-character Mellin
estimate. The full row sum, original common mask, and uniform quantifier
order are retained.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.PrimeCancellationMoment HeckeSkeleton.PrimeCancellationWiring
open scoped Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)

/-- The linear arithmetic conductor bound has height degree zero, uniformly
over the original complete paired-row family. -/
theorem actual_prime_conductor_control :
    ∃ D q : ℝ, 1 ≤ D ∧ 0 ≤ q ∧
      ∀ Z T (i : SourceMomentIndexFor K c Source Z T) s u,
        1 ≤ Z → 1 ≤ T → 1 ≤ momentBaseFor i →
        u ∈ pairedRows (pairedModelFor Models i s)
          (pairedParametersFor i) (momentBaseFor i) →
        ∀ j, Real.log (heckeConductorScale K
          ((pairedModelFor Models i s).rowCharacter u *
            (pairedModelFor Models i s).slotCoefficient j)) ≤
          D * (1 + Real.log (momentBaseFor i)) * (1 + T) ^ q := by
  obtain ⟨C₀, hC₀, hbound⟩ := actual_prime_conductor_norm_bound K c
  apply source_conductor_control_of_polynomial Models C₀ 1 hC₀ zero_le_one
  · intro Z T i s u _hZ _hT _hU _hu j
    exact HeckeConductorNorm.conductorScale_pos K _
  · intro Z T i s u _hZ _hT _hU hu j
    simpa only [Real.rpow_one] using hbound Z T i s u hu j

/-- The actual structural/profile/conductor contract has no additional
moment or prime-sum estimate as a premise. -/
def actualPrimeSlotModelControl : PrimeSlotModelControl Models where
  slot_count := fun _ _ i s =>
    MOM_PRIME.recipePairedModel_slotCount_le K c (expansionRecipeRaw K c) i s
  inverse_mem := fun _ _ i s j => actual_prime_slot_inverse_mem K c i s j
  window := actualPrimeWindow K c
  window_eq := actualPrimeWindow_eq K c
  window_support := actualPrimeWindow_support K c
  window_control := actualPrimeWindow_uniform_seminorm K c
  conductor_control := actual_prime_conductor_control K c

/-- The exact below-one exponent for the actual selected source models. -/
theorem actual_paired_primes_below_one (hB : c.family.B < 1) :
    PairedPrimeProductBoundFor Models (2 * c.family.B - 1) :=
  paired_primes_below_one_of_models Models hB
    (recipeMoment_polynomial_calibration K c (expansionRecipeRaw K c))
    (actualRecipeRowEligibility K c) (actualPrimeSlotModelControl K c)

end HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actualPrimeSlotModelControl
#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.actual_paired_primes_below_one
