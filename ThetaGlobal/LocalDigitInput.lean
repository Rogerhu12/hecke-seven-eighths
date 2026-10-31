import ThetaGlobal.LocalDigitAverage
import ThetaGlobal.GlobalProjectLocalDigitTables

/-!
# The literal global digit table input from the actual exterior source

The local calculation is made in the canonical representation with the
same reference and functional. This module identifies its matrix word
with the global digit coefficient, then fills all four fields of the
existing interface from proved local arithmetic and representation
theorems.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ThetaGlobal.LocalDigitInput

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectDigitProduct
open ThetaGlobal.GlobalProjectLocalDigitTables
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointExteriorCoefficientSources R N)

/-- Both definitions evaluate the same actual reference vector at the
same canonical local representation of `A(x) W N(-s/g_p)`. -/
theorem localDigit_eq (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F) :
    localDigit R C.factorization p x s =
      LocalDigitEvaluation.localDigitValue R C p x s := by
  simp only [GlobalProjectDigitProduct.localDigit, OrbitExpansion.exteriorSlotValue,
    LocalDigitEvaluation.localDigitValue, map_mul] <;> rfl

variable (hdiff : ∀ p : HeightOneSpectrum (𝓞 F),
  p ∉ (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) → HeckeGeneral.Characters.localDifferentExponent F p = 0)

local notation "Adata" => HeckeAxiom.thetaArithmeticData R.A R.probe.allowed R.σ hdiff

/-- The local digit package of the same actual exterior source, with no
remaining local-table hypothesis. -/
theorem input : GlobalProjectLocalDigitTables.Input R C.factorization Adata where
  diagonal p x := by
    rw [C.exterior.rational_exact]
    exact LocalDigitArithmetic.sphericalFactor_eq R hdiff p x
  nonzero_digits p j x L hL := by
    simp_rw [localDigit_eq R C]
    exact LocalDigitAverage.nonzero_digits R C hdiff p j x L hL
  zeroth_weyl p := LocalDigitArithmetic.zeroth_weyl R hdiff p
  forward_mask p j t := LocalDigitArithmetic.forward_mask R hdiff p j t

end ThetaGlobal.LocalDigitInput

#print axioms ThetaGlobal.LocalDigitInput.localDigit_eq
#print axioms ThetaGlobal.LocalDigitInput.input
