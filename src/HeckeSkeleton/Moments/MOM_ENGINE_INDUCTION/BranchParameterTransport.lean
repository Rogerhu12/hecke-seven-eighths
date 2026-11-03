import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ParameterTransport
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreRecursion

/-!
# The actual local branches on one common parameter space

The strict producer and ordinary reflection use different continuous
parameters. Their original measures are embedded into the two summands
of a fixed sum space. Each child is extended using an actual parameter
of its own producer. All pointwise strict invariants therefore survive,
and the reflection geometry and numerical integrability are transported
almost everywhere with exactly the same complete mass.

These definitions only change the parameter space of already produced
local outputs; they do not ask for a child moment bound or a completed
parent reduction. The original coefficients and budgets are unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {σ W : ℝ} {S : PolynomialSystem.{u} K ω ψ σ W}
variable {parent : S.Label} {U δ β C originalControl boundary padding : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Preserve the literal canonical output children and their labels. -/
def EngineBranchAt.mapParameter
    (out : EngineBranchAt (Ω := Ω) S parent U δ β C originalControl admissible)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    EngineBranchAt (Ω := Ω') S parent U δ β C originalControl admissible where
  output := out.output.mapParameter f hf g hgf
  left b η := out.left b (g η)
  right b η := out.right b (g η)
  left_eq b η := out.left_eq b (g η)
  right_eq b η := out.right_eq b (g η)

/-- A short-factor reflection retains its actual terminal and complete
kernel-mass estimates under the same numerical transport. -/
def ShortReflectionBranchAt.mapParameter
    (out : ShortReflectionBranchAt (Ω := Ω) S parent U boundary δ β C originalControl)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    ShortReflectionBranchAt (Ω := Ω') S parent U boundary δ β C originalControl where
  output := out.output.mapParameter f hf g hgf
  terminal := out.terminal
  mass := by
    change (out.output.kernel.map f).real Set.univ ≤ C * originalControl * U ^ δ
    rw [parameterMap_mass out.output.kernel hf]
    exact out.mass

/-- This includes the actual outer reflection and the literal
whole-series terminal with its zero measure. -/
def OuterReflectionBranchAt.mapParameter
    (out : OuterReflectionBranchAt (Ω := Ω) S parent U padding δ β C originalControl)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    OuterReflectionBranchAt (Ω := Ω') S parent U padding δ β C originalControl where
  output := out.output.mapParameter f hf g hgf
  terminal := out.terminal
  mass := by
    change (out.output.kernel.map f).real Set.univ ≤ C * originalControl * U ^ δ
    rw [parameterMap_mass out.output.kernel hf]
    exact out.mass

/-- The engine occupies the left summand. The unused summand evaluates
its real original children at one fixed original engine parameter. -/
def EngineBranchAt.inlParameter
    (out : EngineBranchAt (Ω := Ω) S parent U δ β C originalControl admissible)
    (original : Ω) :
    EngineBranchAt (Ω := Ω ⊕ Ω') S parent U δ β C originalControl admissible :=
  out.mapParameter Sum.inl measurableEmbedding_parameterInl
    (parameterInlRetraction original) (parameterInlRetraction_leftInverse original)

/-- Ordinary short-factor reflection occupies the right summand. -/
def ShortReflectionBranchAt.inrParameter
    (out : ShortReflectionBranchAt (Ω := Ω) S parent U boundary δ β C originalControl)
    (original : Ω) :
    ShortReflectionBranchAt (Ω := Ω' ⊕ Ω) S parent U boundary δ β C originalControl :=
  out.mapParameter Sum.inr measurableEmbedding_parameterInr
    (parameterInrRetraction original) (parameterInrRetraction_leftInverse original)

/-- Ordinary outer reflection uses the same right summand and fixed
default as the short-factor branch, even for a zero-kernel terminal. -/
def OuterReflectionBranchAt.inrParameter
    (out : OuterReflectionBranchAt (Ω := Ω) S parent U padding δ β C originalControl)
    (original : Ω) :
    OuterReflectionBranchAt (Ω := Ω' ⊕ Ω) S parent U padding δ β C originalControl :=
  out.mapParameter Sum.inr measurableEmbedding_parameterInr
    (parameterInrRetraction original) (parameterInrRetraction_leftInverse original)

end HeckeSkeleton.Moments.EngineInduction
