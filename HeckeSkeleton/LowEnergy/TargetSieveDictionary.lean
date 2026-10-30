import HeckeSkeleton.LowEnergy.ActualSieveDictionary
import HeckeSkeleton.Moments

/-!
# The task's two sieve hypotheses match the generic actual-kernel inputs

Only the definitions of the two bounds are used from Moments.  Its unrelated
unfinished declarations are not invoked by any proof below.  This file is a
project adapter and needs checking in the complete project environment.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.TargetSieveDictionary

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.ActualSieveDictionary

variable (K : Type) [Field K] [NumberField K]
variable (c : HeckeSkeleton.TargetContext K)

local notation "S" => HeckeSkeleton.places K c
local notation "P" => HeckeSkeleton.probeData K c
local notation "ψ" => HeckeSkeleton.targetCharacter K c

/-- No strengthening of the permitted quadratic hypothesis is hidden here. -/
theorem quadratic_bound_iff :
    HeckeSkeleton.QuadraticSieveBound K c ↔ ExteriorQuadraticBound K S P.arithmetic := Iff.rfl

/-- No strengthening of the permitted cubic hypothesis is hidden here. -/
theorem cubic_bound_iff :
    HeckeSkeleton.CubicSieveBound K c ↔ ExteriorCubicBound K S P.arithmetic := Iff.rfl

/-- The actual ordinary-ideal kernels inherit exactly the two supplied sieves. -/
theorem ordinary_sieves_of_target
    {F : FiniteMellinData K S}
    (hreflection : MarkedCoefficientReflectionInput K S P.arithmetic
      F (thetaPeriod K S P ψ))
    (hquadratic : HeckeSkeleton.QuadraticSieveBound K c)
    (hcubic : HeckeSkeleton.CubicSieveBound K c) :
    OrdinaryQuadraticBound K S P.arithmetic ∧ OrdinaryCubicBound K S P.arithmetic :=
  ⟨ordinaryQuadratic_of_exterior K S P.arithmetic hreflection.allowed_generators hquadratic,
    ordinaryCubic_of_exterior K S P.arithmetic hcubic⟩

#print axioms quadratic_bound_iff
#print axioms cubic_bound_iff
#print axioms ordinary_sieves_of_target

end HeckeSkeleton.LowEnergy.TargetSieveDictionary
