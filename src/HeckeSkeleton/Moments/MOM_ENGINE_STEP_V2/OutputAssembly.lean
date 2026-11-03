import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedEngineOutput

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same actual normalized family enters the original conclusion

Geometry, recursive admissibility and the numerical bounds all refer to
the displayed family and its original two Fourier kernels. This adapter
uses the merged finite-family construction, with no new child selection.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {Λ : Type*}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

/-- This is an assembly lemma, not a production task: its three numerical
premises and both exact recursive invariants are supplied by the separate
paper tasks on this very family. -/
def engineOutput (call : Blueprint.Call c)
    (family : ActualNormalizedPairFamily
      (Blueprint.Arithmetic.data c) (Blueprint.Arithmetic.embedding c)
      EngineParameter Λ c.family.omega (targetCharacter K c) call.base)
    (labels : Finset Λ)
    (geometry : family.OutputGeometry labels call.node.data call.node.parameters
      (recipeInductionSigma c) rowDomain window seminorms)
    (atoms : family.FourierAtomControl labels J₁₁ J₁₂ J₂₁ J₂₂)
    (F₁ F₂ : Λ → 𝓢(ℝ, ℂ)) (outer : Λ → ℝ)
    (left_admissible : ∀ (b : family.active labels) ξ,
      admissibleOfInvariant call.primitive
        (family.leftData labels b ξ) (family.leftParameters labels b))
    (right_admissible : ∀ (b : family.active labels) ξ,
      admissibleOfInvariant call.primitive
        (family.rightData labels b ξ) (family.rightParameters labels b))
    (firstZero secondZero exceptional tail : ℝ)
    (hfirstZero : 0 ≤ firstZero) (hsecondZero : 0 ≤ secondZero)
    (hexceptional : 0 ≤ exceptional) (htail : 0 ≤ tail)
    (hterminals : firstZero + secondZero + exceptional + tail ≤
      call.prepared.engineCoefficient * call.prepared.engineControl *
        call.base ^ recipeInductionTerminalLoss c)
    (hparent : call.node.normalizedEnergy call.base 0 ≤
      firstZero + secondZero + exceptional + tail +
        ∑ b : family.active labels, ∫ ξ,
          Real.sqrt (normalizedPairedEnergy (family.leftData labels b ξ)
            (family.leftParameters labels b) call.base 0) *
          Real.sqrt (normalizedPairedEnergy (family.rightData labels b ξ)
            (family.rightParameters labels b) call.base 0)
              ∂family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
                (call.node.parameters.m + call.node.parameters.q) b)
    (hmass : (∑ b : family.active labels,
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
        (call.node.parameters.m + call.node.parameters.q) b).real Set.univ) ≤
      call.prepared.engineCoefficient * call.prepared.engineControl *
        call.base ^ recipeInductionEdgeLoss c) :
    call.node.EngineOutput (Ω := EngineParameter) call.base
      (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) call.prepared.engineCoefficient
      call.prepared.engineControl (admissibleOfInvariant call.primitive) := by
  let convergence := atoms.outputIntegrability F₁ F₂ outer
    (call.node.parameters.m + call.node.parameters.q) call.base_pos
  exact PairedEngineConclusion.ofFintype
    (family.leftData labels) (family.rightData labels)
    (family.leftParameters labels) (family.rightParameters labels)
    (fun _ _ => 0) (fun _ _ => 0)
    (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer)
      (call.node.parameters.m + call.node.parameters.q))
    (fun _ _ => rfl) (fun _ _ => rfl)
    convergence.finite_kernel
    geometry.left_width geometry.right_width
    geometry.left_width_nonneg geometry.right_width_nonneg
    geometry.left_plain_left_nonneg geometry.left_plain_right_nonneg
    geometry.right_plain_left_nonneg geometry.right_plain_right_nonneg
    geometry.left_length geometry.right_length
    geometry.left_kappa geometry.right_kappa
    geometry.left_slots geometry.right_slots
    geometry.left_theta geometry.right_theta
    geometry.left_slot_characters geometry.right_slot_characters
    left_admissible right_admissible
    geometry.left_capacity geometry.right_capacity
    firstZero secondZero exceptional tail
    hfirstZero hsecondZero hexceptional htail hterminals
    convergence.left_integrable convergence.right_integrable convergence.cauchy_integrable
    hparent hmass

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.engineOutput
