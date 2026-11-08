module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bProfileBudget
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUniformBudget

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed exceptional costs and the original N8a index sum

The actual source bound is integrated against the two original fixed
kernels.  The source and normalization profile factors are paid by
one explicit polynomial.  N8a then sums precisely the original raw
indices, retaining both actual divisors and the single original pool.

`NormalizerBound` below is an internal assembly interface for the
original scalar-normalization theorem; the final task supplies its
proved witness and has only the two frozen public dependencies.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def NormalizerBound (c : TargetContext K) (p : SourceParameters c) (frame : SourceFrame)
    (coefficient : ℝ) : Prop :=
  ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
    (0, 0) ∈ input.orders →
    firstColumnAnnulus c call.frame ≤ call.base →
    ∀ (trace : SourceTrace call p) (htrace : trace.Realizes),
    ∀ (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes),
    ∀ (raw : RawFamily geometry) (hraw : raw.Realizes) (j : Fin raw.count) (side : Bool),
      (raw.packet j).leaf.weight *
        (raw.packet j).t3bPointScalar (raw.packet_realizes trace htrace hgeometry hraw j)
          (OrdinaryPhaseFacts.ofRaw trace htrace raw j) side *
        call.base ^ (raw.packet j).t3bNominalNorm side / call.parentNormalizer ≤
      (coefficient * (1 + input.amplitude) ^ (4 * c.geometry.slots)) *
        trace.expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ (p.loss * (18 + recipeInductionSigma c / 2))

variable {c : TargetContext K} {p : SourceParameters c} {frame : SourceFrame}

def analyticCost (bounds : SourceBounds c p frame) (budget : ProfileBudget bounds)
    (D : ℝ) (hD : 0 ≤ D) : UniformCost where
  orders := profileOrders bounds
  coefficient := D * (2 : ℝ) ^ (4 * c.geometry.slots) *
    pointCoefficient bounds budget.coefficient * kernelMoment c p bounds.degree bounds.degree
  coefficient_nonneg := mul_nonneg
    (mul_nonneg (mul_nonneg hD (pow_nonneg (by norm_num) _))
      (pointCoefficient_nonneg bounds budget.coefficient budget.coefficient_one_le))
    (kernelMoment_nonneg c p bounds.degree bounds.degree)
  profileDegree := 4 + 16 * c.geometry.slots
  heightDegree := 0
  heightDegree_nonneg := le_refl _
  threshold := max (max 1 (completeMaskCoefficient c frame)) (firstColumnAnnulus c frame)
  threshold_one_le := (le_max_left _ _).trans (le_max_left _ _)

theorem analyticCost_coefficient_le (bounds : SourceBounds c p frame)
    (budget : ProfileBudget bounds) (D : ℝ) (hD : 0 ≤ D)
    {call : Call c} (input : ProfileInput call) (height : ℝ) :
    (D * (1 + input.amplitude) ^ (4 * c.geometry.slots)) *
        pointCoefficient bounds (budget.coefficient * input.amplitude) *
        kernelMoment c p bounds.degree bounds.degree ≤
      (analyticCost bounds budget D hD).value input.amplitude height := by
  have hA : 0 ≤ input.amplitude := zero_le_one.trans input.amplitude_one_le
  have hpow : (1 + input.amplitude) ^ (4 * c.geometry.slots) ≤
      (2 * input.amplitude) ^ (4 * c.geometry.slots) :=
    pow_le_pow_left₀ (by linarith) (by linarith [input.amplitude_one_le]) _
  have hpoint := pointCoefficient_nonneg bounds (budget.coefficient * input.amplitude)
    (profile_amplitude_one bounds budget input)
  calc
    _ ≤ (D * (2 * input.amplitude) ^ (4 * c.geometry.slots)) *
        pointCoefficient bounds (budget.coefficient * input.amplitude) *
        kernelMoment c p bounds.degree bounds.degree :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD) hpoint)
        (kernelMoment_nonneg c p bounds.degree bounds.degree)
    _ = _ := by
      rw [pointCoefficient_mul, mul_pow]
      simp only [analyticCost, UniformCost.value, Real.rpow_zero, mul_one]
      rw [show 4 + 16 * c.geometry.slots =
        4 * c.geometry.slots + (4 + 12 * c.geometry.slots) by omega, pow_add]
      ring

theorem pointExponent_add_normalizer_le (call : Call c) (p : SourceParameters c) :
    pointExponent call p + p.loss * (18 + recipeInductionSigma c / 2) ≤
      recipeInductionTerminalLoss c - p.loss - p.loss := by
  have h := exceptional_uniform_terminal_exponent call p
  convert h using 1 <;> unfold pointExponent exceptionalErrorBound <;> ring

/-- Every premise here is a proved component on the same actual raw
leaf: T3a, the fixed contour witnesses, and the original scalar bound. -/
theorem analytic_leaf_bound (recovery : ExceptionalRecoveryTask c p)
    (bounds : SourceBounds c p frame) (budget : ProfileBudget bounds)
    (D : ℝ) (hD : 0 ≤ D) (hnormalizer : NormalizerBound c p frame D)
    (call : Call c) (input : ProfileInput call) (hframe : call.frame = frame)
    (ready : (analyticCost bounds budget D hD).Ready call input)
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    (geometry : GeometryFamily trace.second) (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) (j : Fin raw.count) :
    call.normalizedScalar (raw.packet j).leaf.exceptionalCost ≤
      (analyticCost bounds budget D hD).value input.amplitude call.request.height *
        raw.indexWeight j * call.base ^ (recipeInductionTerminalLoss c - p.loss - p.loss) := by
  let hpacket := raw.packet_realizes trace htrace hgeometry hraw j
  let phases := OrdinaryPhaseFacts.ofRaw trace htrace raw j
  let P := budget.coefficient * input.amplitude
  have hP : 1 ≤ P := profile_amplitude_one bounds budget input
  have horders : profileOrders bounds ⊆ input.orders := ready.orders
  have hthreshold : completeMaskCoefficient c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_right 1 (completeMaskCoefficient c frame)).trans
      ((le_max_left _ _).trans ready.large)
  have hannulus : firstColumnAnnulus c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_right _ _).trans ready.large
  have hplain (plain : Bool) : bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((raw.packet j).t3bNormProfile hpacket input plain) ≤ P :=
    budget.plain call input hframe horders (raw.packet j) hpacket plain
  have hprime (i : Fin call.localizedData.geometry.slotCount) (x : ℝ) :
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P :=
    budget.prime call input hframe horders i x
  obtain ⟨side, hpoint⟩ := raw.t3b_exceptional_pointwise trace htrace hgeometry hraw
    recovery bounds j input hframe hthreshold P hP hplain hprime
  have hzero : (0, 0) ∈ input.orders := horders (zero_mem_profileOrders bounds)
  have hnorm := hnormalizer call input hframe hzero hannulus
    trace htrace geometry hgeometry raw hraw j side
  have hDinput : 0 ≤ D * (1 + input.amplitude) ^ (4 * c.geometry.slots) :=
    mul_nonneg hD (pow_nonneg (by linarith [input.amplitude_one_le]) _)
  have hleaf := normalized_leaf_le_index raw j hpacket
    ((raw.packet j).t3bNominalNorm side)
    ((raw.packet j).t3bPointScalar hpacket phases side)
    (pointCoefficient bounds P) (pointExponent call p)
    (p.loss * (18 + recipeInductionSigma c / 2)) p.loss
    (D * (1 + input.amplitude) ^ (4 * c.geometry.slots)) bounds.degree bounds.degree
    (pointCoefficient_nonneg bounds P hP) hDinput hpoint hnorm
    (pointExponent_add_normalizer_le call p)
  have hcoefficient := analyticCost_coefficient_le bounds budget D hD input call.request.height
  exact hleaf.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoefficient (raw.t3b_indexWeight_nonneg j))
    (Real.rpow_nonneg call.base_pos.le _))

def exceptionalCertificate (recovery : ExceptionalRecoveryTask c p)
    (bounds : SourceBounds c p frame) (budget : ProfileBudget bounds)
    (D : ℝ) (hD : 0 ≤ D) (hnormalizer : NormalizerBound c p frame D)
    (index : SourceIndexCertificate c frame p p.loss) : ExceptionalCertificate c frame p :=
  exceptionalCertificate_of_original_leaves (analyticCost bounds budget D hD) index
    (analytic_leaf_bound recovery bounds budget D hD hnormalizer)

theorem exceptionalSummation_of_normalizer
    (normalizer : ∀ frame : SourceFrame,
      ∃ D : ℝ, 0 ≤ D ∧ NormalizerBound c p frame D) :
    ExceptionalSummationTask c p := by
  intro recovery indexTask frame
  obtain ⟨bounds⟩ := sourceBounds_nonempty c p frame
  obtain ⟨budget⟩ := profileBudget_nonempty bounds
  obtain ⟨D, hD, hnormalizer⟩ := normalizer frame
  obtain ⟨index⟩ := indexTask frame p.loss p.loss_pos
  exact ⟨exceptionalCertificate recovery bounds budget D hD hnormalizer index⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.analytic_leaf_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exceptionalSummation_of_normalizer
