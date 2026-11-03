import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSources
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRowBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original exceptional integrand is the same two source values

The complete original columns retain their common row translations,
their two common scalars, the right star and their centered subtraction.
Only after the exact polynomial identities are proved are the phases
removed from the norms. T3a's exact support then gives the original
finite exceptional sum on which the arithmetic class count operates.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem phase_scalar_term (a b u v : ℂ) :
    (a * b) * (u * v) = u * (a * (b * v)) := by
  ring

private theorem translated_column_norm {z u a v n : ℂ} {w : ℝ}
    (he : z = u * (a * v)) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = ‖n‖ * w) (hn : n = 1) : ‖z‖ = ‖a‖ * w := by
  rw [he, norm_mul, hu, one_mul, norm_mul, hv, hn, norm_one, one_mul]

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet)

def t3bColumnValue (side : Bool) (ξ : EngineParameter) (h : packet.R.live) : ℂ :=
  (packet.t3bUnscaledSource hpacket phases side).centeredColumn
    (σ := Arithmetic.embedding c)
    ((packet.t3bUnscaledTable hpacket phases side).scale₁ true)
    ((packet.t3bUnscaledTable hpacket phases side).scale₂ true)
    (fun _ => (packet.t3bUnscaledTable hpacket phases side).comparisonWeight true)
    (fun _ => (packet.t3bUnscaledTable hpacket phases side).rightWeight true) ξ h

theorem t3bColumnValue_centered (input : ProfileInput call) (hc : call.node.centered = true)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    packet.t3bColumnValue hpacket phases side ξ h =
      (packet.t3bExceptionalAt hpacket phases input hc side ξ h).source.value := rfl

theorem t3bColumnValue_uncentered (input : ProfileInput call) (hc : call.node.centered = false)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    packet.t3bColumnValue hpacket phases side ξ h =
      (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source.ordinaryValue := by
  exact packet.t3b_centeredColumn_uncentered hpacket phases hc side ξ h

theorem t3b_left_column_norm (ξ : EngineParameter) (h : packet.R.live) :
    ‖jointFourierColumn packet.leaf.left (packet.leaf.leftCoefficient h.val)
        (packet.ordinaryLeftPoint h.val) ξ‖ =
      ‖packet.secondAtomScalar hpacket phases false‖ *
        ‖packet.t3bColumnValue hpacket phases false ξ h‖ := by
  let f := packet.t3bUnscaledLeftFrame hpacket phases
  let E := packet.t3bUnscaledLeftComparison hpacket phases
  have he : jointFourierColumn packet.leaf.left (packet.leaf.leftCoefficient h.val)
      (packet.ordinaryLeftPoint h.val) ξ =
      jointPhase ξ (packet.leftRowTranslation h.val) *
        (packet.secondAtomScalar hpacket phases false *
          jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val)
            (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
              (f.slotLocation h.val)) ξ) := by
    unfold jointFourierColumn
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [packet.t3b_left_coefficient hpacket phases h.val i hi,
      packet.t3b_left_scalar hpacket phases h.val i,
      packet.ordinaryLeftPoint_eq_translation hpacket h.val i
        (packet.t3b_left_cartesian i hi), jointPhase_add]
    exact phase_scalar_term (packet.secondAtomScalar hpacket phases false)
      (f.centeredCoefficient E h.val i) (jointPhase ξ (packet.leftRowTranslation h.val))
      (jointPhase ξ (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
        (f.slotLocation h.val) i))
  exact translated_column_norm he (norm_jointPhase ξ (packet.leftRowTranslation h.val))
    (f.centered_column_norm_eq_source E h ξ)
    (packet.t3bUnscaledLeftFrame_normalizer hpacket phases)

theorem t3b_right_column_norm (ξ : EngineParameter) (h : packet.R.live) :
    ‖jointFourierColumn packet.leaf.right (fun i => star (packet.leaf.rightCoefficient h.val i))
        (packet.ordinaryRightPoint h.val) ξ‖ =
      ‖packet.secondAtomScalar hpacket phases true‖ *
        ‖packet.t3bColumnValue hpacket phases true ξ h‖ := by
  let f := packet.t3bUnscaledRightFrame hpacket phases
  let E := packet.t3bUnscaledRightComparison hpacket phases
  have he : jointFourierColumn packet.leaf.right
      (fun i => star (packet.leaf.rightCoefficient h.val i))
      (packet.ordinaryRightPoint h.val) ξ =
      jointPhase ξ (packet.rightRowTranslation h.val) *
        (star (packet.secondAtomScalar hpacket phases true) *
          jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val)
            (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
              (f.slotLocation h.val)) ξ) := by
    unfold jointFourierColumn
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [packet.t3b_right_coefficient hpacket phases h.val i hi,
      packet.t3b_right_scalar hpacket phases h.val i,
      packet.ordinaryRightPoint_eq_translation hpacket h.val i
        (packet.t3b_right_cartesian i hi), jointPhase_add]
    exact phase_scalar_term (star (packet.secondAtomScalar hpacket phases true))
      (f.centeredCoefficient E h.val i) (jointPhase ξ (packet.rightRowTranslation h.val))
      (jointPhase ξ (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
        (f.slotLocation h.val) i))
  have hnorm := translated_column_norm he (norm_jointPhase ξ (packet.rightRowTranslation h.val))
    (f.centered_column_norm_eq_source E h ξ)
    (packet.t3bUnscaledRightFrame_normalizer hpacket phases)
  exact hnorm.trans (congrArg (fun r : ℝ => r *
    ‖packet.t3bColumnValue hpacket phases true ξ h‖)
    (norm_star (packet.secondAtomScalar hpacket phases true)))

/-- Both complete source values occur under the same original row
weight. T3a removes only rows that are identically zero. -/
theorem t3b_exceptional_integrand_sources (recovery : packet.ExceptionalRecovery)
    (z : ℝ × ℝ) :
    packet.leaf.exceptionalIntegrand z =
      (‖packet.secondAtomScalar hpacket phases false‖ *
        ‖packet.secondAtomScalar hpacket phases true‖) *
      ∑ h ∈ packet.exceptionalRows, ‖packet.leaf.rowWeight h.val‖ *
        ‖packet.t3bColumnValue hpacket phases false (WithLp.toLp 2 z) h‖ *
        ‖packet.t3bColumnValue hpacket phases true (WithLp.toLp 2 z) h‖ := by
  rw [recovery.exact_support]
  unfold supportedExceptionalIntegrand jointColumnPairMagnitude
  change (∑ h ∈ packet.exceptionalRows, ‖packet.leaf.rowWeight h.val‖ *
      ‖jointFourierColumn packet.leaf.left (packet.leaf.leftCoefficient h.val)
        (packet.ordinaryLeftPoint h.val) (WithLp.toLp 2 z)‖ *
      ‖jointFourierColumn packet.leaf.right (fun i => star (packet.leaf.rightCoefficient h.val i))
        (packet.ordinaryRightPoint h.val) (WithLp.toLp 2 z)‖) = _
  simp_rw [packet.t3b_left_column_norm hpacket phases, packet.t3b_right_column_norm hpacket phases]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem t3b_exceptional_integrand_le_source_sum (recovery : packet.ExceptionalRecovery)
    (side : Bool) (z : ℝ × ℝ) :
    packet.leaf.exceptionalIntegrand z ≤
      (‖packet.secondAtomScalar hpacket phases false‖ *
        ‖packet.secondAtomScalar hpacket phases true‖ * packet.t3bRowAmplitude *
        call.base ^ ((packet.nominal side).skeleton.g₂ -
          (packet.nominal side).skeleton.t₂)) *
      ∑ h ∈ packet.exceptionalRows,
        ‖packet.t3bColumnValue hpacket phases false (WithLp.toLp 2 z) h‖ *
        ‖packet.t3bColumnValue hpacket phases true (WithLp.toLp 2 z) h‖ := by
  rw [packet.t3b_exceptional_integrand_sources hpacket phases recovery]
  calc
    _ ≤ (‖packet.secondAtomScalar hpacket phases false‖ *
          ‖packet.secondAtomScalar hpacket phases true‖) *
        ∑ h ∈ packet.exceptionalRows,
          (packet.t3bRowAmplitude * call.base ^
            ((packet.nominal side).skeleton.g₂ -
              (packet.nominal side).skeleton.t₂)) *
            ‖packet.t3bColumnValue hpacket phases false (WithLp.toLp 2 z) h‖ *
            ‖packet.t3bColumnValue hpacket phases true (WithLp.toLp 2 z) h‖ := by
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (packet.t3b_leafRowWeight_le hpacket side h)
          (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_integrand_sources
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_integrand_le_source_sum
