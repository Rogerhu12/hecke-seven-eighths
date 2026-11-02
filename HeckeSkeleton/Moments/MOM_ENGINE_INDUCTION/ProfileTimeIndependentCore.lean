import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl

/-!
# Literal time-independent profile identity

This data-only condition records the unused final time argument of each
actual profile. Its source, power-child and freeze inheritance proofs are
in `ProfileTimeIndependent`; the analytic finite-order bridge needs only
this condition and does not depend on a particular source dictionary.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Every final evaluation-time argument is unused. This is a primitive
identity of the actual tests, with no analytic estimate among its fields. -/
structure ProfileTimeIndependent (d : MomentData K ω ψ) : Prop where
  inverse : ∀ u t, d.inverseTest.profile u t = d.inverseTest.profile u 0
  plain₁ : ∀ u t, d.plainTest₁.profile u t = d.plainTest₁.profile u 0
  plain₂ : ∀ u t, d.plainTest₂.profile u t = d.plainTest₂.profile u 0
  prime : ∀ j t, (d.geometry.slots j).profile t = (d.geometry.slots j).profile 0

end HeckeSkeleton.Moments.EngineInduction
