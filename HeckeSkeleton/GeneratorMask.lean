import HeckeSkeleton.Theta
import AxiomGeneratorMaskWitness

/-!
GR-12-MASK, skeleton layer: the abstract generator-mask witness of the Axiom
arithmetic choice `axiomChoice K c`, with the places and the arithmetic data of
the skeleton. The witness is built in `AxiomGeneratorMaskWitness` from Axiom's
`AllowedRecipe` (complement `B` of the unit image in the S-local sixth-power
classes) and the skeleton's `allowedGenerators`; it adds no new assumption.
`IsTotallyComplex K` is derived from the primitive twelfth root of the family.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft

variable (K : Type) [Field K] [NumberField K]

/-- `K` is totally complex: it contains a primitive twelfth root of unity. -/
theorem targetContext_totallyComplex (c : TargetContext K) : IsTotallyComplex K :=
  DedekindZetaZeroFree.primitive12_totallyComplex K c.family.root12 c.family.primitive12

/-- The generator mask witness of the target's Axiom arithmetic choice. -/
def generatorMaskWitness (c : TargetContext K) : GeneratorMaskWitness K :=
  haveI : IsTotallyComplex K := targetContext_totallyComplex K c
  HeckeAxiom.GeneratorMask.witness (axiomChoice K c) (allowedGenerators K c)

@[simp] theorem generatorMaskWitness_S (c : TargetContext K) :
    (generatorMaskWitness K c).S = excludedPlaces K c := rfl

@[simp] theorem generatorMaskWitness_D (c : TargetContext K) :
    (generatorMaskWitness K c).D = arithmeticData K c := rfl

end HeckeSkeleton
