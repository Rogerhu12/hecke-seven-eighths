import ThetaGlobal.FiniteSkeletonSource
import ThetaGlobal.LocalDigitInput

/-!
# The digit table on the skeleton's one fixed source

The actual recipe retains the allowed-generator section of the same
arithmetic choice. Consequently the local table constructed from that
recipe has exactly the arithmetic data used by the skeleton entry point.
The source is unchanged and is selected before the high K-type input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

theorem thetaRecipe_arithmeticData :
    HeckeAxiom.thetaArithmeticData (thetaRecipe K c).A
      (thetaRecipe K c).probe.allowed (thetaRecipe K c).σ
      (axiomChoice K c).different = arithmeticData K c := by
  change HeckeAxiom.thetaArithmeticData (axiomChoice K c).A
    (ThetaGlobal.GlobalSameChoice.recipe (axiomChoice K c)
      (axiomChoice_modulus_top K c)).probe.allowed
    (complexEmbedding K c) (axiomChoice K c).different = (axiomChoice K c).thetaData
  rw [ThetaGlobal.GlobalSameChoice.recipe_allowed]
  rfl

/-- The actual fixed source supplies its exterior digit table without an
additional local-table hypothesis. -/
theorem localExteriorDigitInput :
    ThetaGlobal.GlobalProjectLocalDigitTables.Input (thetaRecipe K c)
      (thetaFiniteSource K c).projected.base.factorization (arithmeticData K c) := by
  have h := ThetaGlobal.LocalDigitInput.input (thetaRecipe K c)
    (thetaFiniteSource K c).projected.base (axiomChoice K c).different
  rw [thetaRecipe_arithmeticData K c] at h
  exact h

end HeckeSkeleton

#print axioms HeckeSkeleton.thetaRecipe_arithmeticData
#print axioms HeckeSkeleton.localExteriorDigitInput
