import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOutputConditions

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual finite normalized family used by the blueprint

This is a small package of the existing base family and its two original
Fourier kernels. It contains no source, terminal, mass, admissibility or
integrability estimate. The normalization assembly constructs it from the
individual source calibrations; no task is allowed to supply an arbitrary
finished engine output in its place.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

structure NormalizedData (call : Call c) where
  Label : Type
  finite : Fintype Label
  family : ActualNormalizedPairFamily (Arithmetic.data c) (Arithmetic.embedding c)
    EngineParameter Label c.family.omega (targetCharacter K c) call.base
  firstKernel : Label → 𝓢(ℝ, ℂ)
  secondKernel : Label → 𝓢(ℝ, ℂ)
  outer : Label → ℝ
  outer_nonneg : ∀ b, 0 ≤ outer b

namespace NormalizedData

variable {call : Call c} (N : NormalizedData call)

def labels : Finset N.Label := @Finset.univ N.Label N.finite

abbrev Active := N.family.active N.labels

def parentWidth (_N : NormalizedData call) : ℝ :=
  call.node.parameters.m + call.node.parameters.q

/-- The original outer scalar and both original Fourier measures occur
once. The base family supplies the complete normalization envelope. -/
def kernel (b : N.Active) : Measure EngineParameter :=
  N.family.kernel N.labels
    (actualNestedLabelMeasure N.firstKernel N.secondKernel N.outer)
    N.parentWidth b

/-- The input of the final positive-kernel comparison, before applying
the already proved capacity and whole-slot removal inequalities. -/
def sourceBudget : ℝ :=
  ∑ b ∈ N.labels, N.outer b *
    ∫ z : ℝ × ℝ, N.family.sourcePair N.parentWidth b (WithLp.toLp 2 z)
      ∂nestedFourierMeasure (N.firstKernel b) (N.secondKernel b)

def childBudget : ℝ :=
  ∑ b : N.Active, ∫ ξ,
    Real.sqrt (normalizedPairedEnergy (N.family.leftData N.labels b ξ)
      (N.family.leftParameters N.labels b) call.base 0) *
    Real.sqrt (normalizedPairedEnergy (N.family.rightData N.labels b ξ)
      (N.family.rightParameters N.labels b) call.base 0) ∂N.kernel b

def arithmeticMass : ℝ :=
  ∑ b : N.Active, N.outer b.val * N.family.weight N.labels N.parentWidth b

def kernelMass : ℝ := ∑ b : N.Active, (N.kernel b).real Set.univ

/-- Every recursive certificate refers to the exact children already
selected by the base family, after normalization, restriction and freezing. -/
def RecursiveAdmissible : Prop :=
  (∀ (b : N.Active) ξ, admissibleOfInvariant call.primitive
    (N.family.leftData N.labels b ξ) (N.family.leftParameters N.labels b)) ∧
  (∀ (b : N.Active) ξ, admissibleOfInvariant call.primitive
    (N.family.rightData N.labels b ξ) (N.family.rightParameters N.labels b))

def ParentSourceBound (firstZero secondZero exceptional tail : ℝ) : Prop :=
  call.node.normalizedEnergy call.base 0 ≤
    firstZero + secondZero + exceptional + tail + N.sourceBudget

def ParentBound (firstZero secondZero exceptional tail : ℝ) : Prop :=
  call.node.normalizedEnergy call.base 0 ≤
    firstZero + secondZero + exceptional + tail + N.childBudget

def MassBound (coefficient control loss : ℝ) : Prop :=
  N.kernelMass ≤ coefficient * control * call.base ^ loss

end NormalizedData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
