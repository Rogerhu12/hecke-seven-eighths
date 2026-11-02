import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteKernelFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ScalarLedger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteEngineOutput

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A single adapter from the compact family to the unchanged public conclusion

The arithmetic producer constructs this record from its raw source.  In
particular, the source inequality, terminal estimate and mass estimate
are fields of the resulting construction, never new hypotheses of the
public paired-step theorem.  Both sides use the same finite carrier and
the same positive measure.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

structure Output (I Ω : Type*) [Fintype I] [MeasurableSpace Ω]
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop) where
  children : ChildFamily I Ω d a σ admissible
  kernels : FiniteKernelFamily children Z
  terminals : ScalarLedger
  terminal_bound : terminals.total ≤ C * control * Z ^ terminalExponent
  parent_bound : pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
    terminals.total + kernels.pairIntegral
  mass_bound : kernels.mass ≤ C * control * Z ^ ε

namespace Output

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Reindex the entire actual carrier once, preserving every original
child, its shared measure, all four terminals, and both numerical bounds. -/
def toConclusion (out : Output I Ω centered d a
    Z t Y₁ Y₂ σ ε terminalExponent C control admissible) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible := by
  sorry

theorem linearized (out : Output I Ω centered d a
    Z t Y₁ Y₂ σ ε terminalExponent C control admissible) (hZ : 0 < Z) :
    pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      C * control * Z ^ terminalExponent + ∑ b : I,
        ((∫ ξ, out.children.energy false b Z ξ ∂out.kernels.kernel b) +
          ∫ ξ, out.children.energy true b Z ξ ∂out.kernels.kernel b) / 2 := by
  sorry

end Output
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Output.toConclusion
#print axioms HeckeSkeleton.Moments.EngineStepV2.Output.linearized
