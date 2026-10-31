import HeckeSkeleton.ExpansionModels.RecipeDetectorNormalization
import HeckeSkeleton.Moments

/-!
# Named source witness projections

The data-level detector identities live in RecipeDetectorNormalization.
This compatibility module applies them to the named moment source, using
the same actual physical expansion recipe constructed in Base.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {Z T : ℝ}

theorem momentWitness_inverse_eq_detector (i : SourceMomentIndex K c Z T)
    (u : FrequencyRow K (places K c)) :
    (momentWitness i).inverseValue u =
      (sourceRecipeWitness i).inverseDetectorPolynomial
        (R := momentRowCharacters K c) i.t (momentBase i) u :=
  (sourceRecipeWitness i).inversePolynomial_eq_normalized
    (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
    (sourceRecipeAmplitude i).physical i.t T (momentBase i) u
    ((by norm_num : (0 : ℝ) < 2).trans_le (momentBase_ge_two i))

theorem momentWitness_plain_eq_detector (i : SourceMomentIndex K c Z T)
    (u : FrequencyRow K (places K c)) :
    (momentWitness i).plainValue u =
      (sourceRecipeWitness i).plainDetectorPolynomial
        (R := momentRowCharacters K c) (momentBase i) u :=
  (sourceRecipeWitness i).plainPolynomial_eq_normalized
    (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
    (sourceRecipeAmplitude i).physical i.t T (momentBase i) u
    ((by norm_num : (0 : ℝ) < 2).trans_le (momentBase_ge_two i))

end HeckeSkeleton
