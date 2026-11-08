module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalAssembly
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizationAssembly
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizedOutputAssembly

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same raw source, terminals and normalized family give one step

This is the local algebraic assembly. It uses no task theorem and
selects no source, profile, descendant or estimate. The original source
inequality and the ordinary source comparison meet at the same raw
family; both mass estimates concern the same normalized family.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {p : SourceParameters c}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}

def output_of_source_normalization
    (certificates : TerminalCertificates c frame p)
    (arithmeticMass profileMass : Finset (ℕ × ℕ) → UniformCost)
    (demand : Finset (ℕ × ℕ) → UniformDemand)
    (call : Call c)
    (input : PreparedEstimates
      ((certificates.costs arithmeticMass profileMass).withDemand demand) call)
    (hframe : call.frame = frame)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes)
    (hsource : call.node.normalizedEnergy call.base 0 ≤
      trace.first.normalizedZero + trace.second.normalizedZero + raw.normalizedExceptional +
        (trace.first.normalizedTail + trace.second.normalizedTail) + raw.normalizedOrdinary)
    (N : NormalizedData call)
    (childGeometry : N.family.OutputGeometry N.labels call.node.data call.node.parameters
      (recipeInductionSigma c) rowDomain window orders)
    (atoms : N.family.FourierAtomControl N.labels J₁₁ J₁₂ J₂₁ J₂₂)
    (admissible : N.RecursiveAdmissible)
    (hordinary : raw.normalizedOrdinary ≤ N.sourceBudget)
    (harithmetic : N.arithmeticMass ≤
      (arithmeticMass call.childOrders).value input.profile.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2))
    (hprofile : N.kernelMass ≤
      (profileMass call.childOrders).value input.profile.amplitude call.request.height *
        call.base ^ (recipeInductionEdgeLoss c / 2) * N.arithmeticMass) :
    call.node.EngineOutput (Ω := EngineParameter) call.base
      (recipeInductionSigma c) (recipeInductionEdgeLoss c)
      (recipeInductionTerminalLoss c) call.prepared.engineCoefficient
      call.prepared.engineControl (admissibleOfInvariant call.primitive) := by
  have hparentSource : N.ParentSourceBound trace.first.normalizedZero
      trace.second.normalizedZero raw.normalizedExceptional
      (trace.first.normalizedTail + trace.second.normalizedTail) :=
    hsource.trans (add_le_add (le_refl _) hordinary)
  exact normalizedOutput N childGeometry atoms admissible
    trace.first.normalizedZero trace.second.normalizedZero raw.normalizedExceptional
    (trace.first.normalizedTail + trace.second.normalizedTail)
    trace.first.normalizedZero_nonneg trace.second.normalizedZero_nonneg
    raw.normalizedExceptional_nonneg
    (add_nonneg trace.first.normalizedTail_nonneg trace.second.normalizedTail_nonneg)
    (source_terminal_budget certificates arithmeticMass profileMass demand call input
      hframe trace htrace geometry hgeometry raw hraw)
    (parentBound_of_sourceBound N atoms _ _ _ _ hparentSource)
    (mass_budget input N harithmetic hprofile)

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.output_of_source_normalization
