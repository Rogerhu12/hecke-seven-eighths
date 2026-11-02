import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepHypothesis

/-!
# The three actual paired moment targets from the explicit single step

These are the original zero-slot, below-one, and endpoint projections,
with the single-step hypothesis made explicit.  They use the actual raw
recipe, its complete finite sector family, and physical exponent one.
The original calibration, row, whole-profile, quadratic-sieve, and
prime-product premises are retained.  The unrestricted zero-slot target
has no added plain-length capacity premise.

The `For` spellings below are the definitions underlying the compatibility
abbreviations in `HeckeSkeleton.Moments`.  Keeping these statements here
lets their native compilation and axiom audit avoid the STEP producer
implementation and the later unconditional source integration.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable (c : TargetContext K)

/-- The exact defining proposition of the original
`HeckeSkeleton.QuadraticSieveBound`, before the downstream compatibility
name is imported.  Its independent coefficients and common-prime zeros
are unchanged. -/
abbrev PairedInductionQuadraticSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J *
          idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ 3‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

variable {Ωengine : Type} [MeasurableSpace Ωengine]

/-- The original unrestricted zero-slot bound, conditional only on the
explicit complete single-step producer in addition to its old premises. -/
theorem paired_zero_slot_models_of_step
    (step : PairedStepHypothesis Ωengine c)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c)
      (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hrows : SourceRowEligibilityFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hquadratic : PairedInductionQuadraticSieveBound c) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor
        (recipeMomentModels K c (expansionRecipeRaw K c)) i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True) := by
  apply uniformMomentBound_recipe_physical (expansionRecipeRaw K c)
    (fun _ _ i => pairedModelEnergyFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) i.noSlots)
    (fun _ _ _ => True)
  exact paired_zero_slot_recipe_mellin (expansionRecipeRaw K c)
    (Classical.choice (actualRecipeScalarInputs_of_step c step).1)

/-- The original positive-slot bound below one, with the same capacity
and selected-set conditions and the same kappa `2 * B - 1` prime premise. -/
theorem paired_positive_below_one_of_step
    (step : PairedStepHypothesis Ωengine c)
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c)
      (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hrows : SourceRowEligibilityFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hquadratic : PairedInductionQuadraticSieveBound c)
    (hprime : PairedPrimeProductBoundFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) (2 * c.family.B - 1)) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor
        (recipeMomentModels K c (expansionRecipeRaw K c)) i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  apply uniformMomentBound_recipe_physical (expansionRecipeRaw K c)
    (fun _ _ i => pairedModelEnergyFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) i)
    (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)
  exact paired_positive_recipe_mellin_below_one (expansionRecipeRaw K c) hB hprime
    (fun _ _ => (actualRecipeScalarInputs_of_step c step).2)

/-- The original positive-slot endpoint uses the absolute kappa-one
prime-product premise and the same actual source and physical exponent. -/
theorem paired_positive_endpoint_of_step
    (step : PairedStepHypothesis Ωengine c)
    (hB : c.family.B = 1)
    (hcal : SourcePolynomialCalibrationFor (momentRowCharacters K c)
      (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hrows : SourceRowEligibilityFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c (expansionRecipeRaw K c)))
    (hquadratic : PairedInductionQuadraticSieveBound c)
    (hprime : PairedPrimeProductBoundFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) 1) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor
        (recipeMomentModels K c (expansionRecipeRaw K c)) i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  apply uniformMomentBound_recipe_physical (expansionRecipeRaw K c)
    (fun _ _ i => pairedModelEnergyFor
      (recipeMomentModels K c (expansionRecipeRaw K c)) i)
    (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)
  exact paired_positive_recipe_mellin_endpoint (expansionRecipeRaw K c) hB hprime
    (fun _ _ => (actualRecipeScalarInputs_of_step c step).2)

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.paired_zero_slot_models_of_step
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_below_one_of_step
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_endpoint_of_step
