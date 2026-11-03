import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bCommonBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bNormalizer
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUniformAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed witness for the actual exceptional normalizer

The common scalar budgets depend polynomially on the original profile
amplitude. Their remaining coefficient is fixed by the context, source
parameters and source frame before any call or raw leaf is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def normalizerConstant (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) : ℝ :=
  commonBudgetBound c frame ^ (2 * c.geometry.slots) *
    profileAnnulus c frame ^ (4 * c.geometry.slots) *
    (orbitalFieldFactor K) ^ 2 / 2 * physicalOrbitFibreConstant c p

theorem normalizerConstant_nonneg (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) : 0 ≤ normalizerConstant c p frame := by
  have hB := commonBudgetBound_nonneg c frame
  have hA := zero_le_one.trans (profileAnnulus_one_le c frame)
  have hF := physicalOrbitFibreConstant_nonneg (c := c) (p := p)
  unfold normalizerConstant
  positivity

theorem commonNormalizerCoefficient_eq (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) (amplitude : ℝ) :
    commonNormalizerCoefficient c p frame
        ((commonBudgetBound c frame * (1 + amplitude) ^ 2) ^ c.geometry.slots) =
      normalizerConstant c p frame * (1 + amplitude) ^ (4 * c.geometry.slots) := by
  have hp : ((commonBudgetBound c frame * (1 + amplitude) ^ 2) ^ c.geometry.slots) ^ 2 =
      commonBudgetBound c frame ^ (2 * c.geometry.slots) *
        (1 + amplitude) ^ (4 * c.geometry.slots) := by
    simp only [mul_pow, ← pow_mul]
    congr 1 <;> congr 1 <;> omega
  unfold commonNormalizerCoefficient normalizerConstant
  rw [hp]
  ring

/-- The internal normalization interface is proved from both actual
frozen products and the original source chain, with no ordinary seed. -/
theorem normalizer_bound (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) :
    NormalizerBound c p frame (normalizerConstant c p frame) := by
  intro call input hframe horders hannulus trace htrace geometry hgeometry raw hraw j side
  let C := (commonBudgetBound c call.frame * (1 + input.amplitude) ^ 2) ^ c.geometry.slots
  have hC : 0 ≤ C := pow_nonneg
    (mul_nonneg (commonBudgetBound_nonneg c call.frame) (sq_nonneg _)) _
  have h := raw.t3b_normalizer_from_common_bounds trace htrace hgeometry hraw j input
    (OrdinaryPhaseFacts.ofRaw trace htrace raw j) side hannulus C hC
    (fun s => (raw.packet j).t3bFirstCommonScalar_sq_le input horders s)
    (fun s => (raw.packet j).t3bSecondCommonScalar_sq_le
      (raw.packet_realizes trace htrace hgeometry hraw j) input horders
      (OrdinaryPhaseFacts.ofRaw trace htrace raw j) s)
  have hcoeff : commonNormalizerCoefficient c p call.frame C =
      normalizerConstant c p frame * (1 + input.amplitude) ^ (4 * c.geometry.slots) := by
    rw [commonNormalizerCoefficient_eq, hframe]
  have hloss : normalizerLoss c p = p.loss * (18 + recipeInductionSigma c / 2) := by
    unfold normalizerLoss
    ring
  simpa only [hcoeff, hloss] using h

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.normalizer_bound
