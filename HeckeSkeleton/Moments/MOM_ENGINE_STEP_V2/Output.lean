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
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible :=
  PairedEngineConclusion.ofFintype
    (out.children.data false) (out.children.data true)
    (out.children.parameters false) (out.children.parameters true)
    (fun _ _ => 0) (fun _ _ => 0) out.kernels.kernel
    (fun _ _ => rfl) (fun _ _ => rfl) out.kernels.finite_kernel
    (out.children.width false) (out.children.width true)
    (out.children.width_nonneg false) (out.children.width_nonneg true)
    (out.children.plain_left_nonneg false) (out.children.plain_right_nonneg false)
    (out.children.plain_left_nonneg true) (out.children.plain_right_nonneg true)
    (out.children.length false) (out.children.length true)
    (out.children.kappa false) (out.children.kappa true)
    (out.children.slots false) (out.children.slots true)
    (out.children.theta false) (out.children.theta true)
    (out.children.slot_characters false) (out.children.slot_characters true)
    (out.children.admissible_data false) (out.children.admissible_data true)
    (out.children.capacity false) (out.children.capacity true)
    out.terminals.firstZero out.terminals.secondZero out.terminals.exceptional out.terminals.tail
    out.terminals.firstZero_nonneg out.terminals.secondZero_nonneg
    out.terminals.exceptional_nonneg out.terminals.tail_nonneg out.terminal_bound
    (out.kernels.integrable false) (out.kernels.integrable true) out.kernels.cauchy_integrable
    out.parent_bound out.mass_bound

/-- Arbitrary extra invariants follow the exact same selected children.
This transports support, inverse-character and profile predicates without
selecting another output or changing its kernels. -/
theorem toConclusion_property (out : Output I Ω centered d a
    Z t Y₁ Y₂ σ ε terminalExponent C control admissible)
    (property : Bool → MomentData K ω ψ → RealParameters → Prop)
    (h : ∀ side b ξ, property side (out.children.data side b ξ)
      (out.children.parameters side b)) :
    (∀ b ξ, property false (out.toConclusion.leftData b ξ)
      (out.toConclusion.leftParameters b)) ∧
    (∀ b ξ, property true (out.toConclusion.rightData b ξ)
      (out.toConclusion.rightParameters b)) := by
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
