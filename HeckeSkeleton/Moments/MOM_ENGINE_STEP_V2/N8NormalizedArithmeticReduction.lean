import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedFixedEnvelope
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedPassiveWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedLeafWeights

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform reduction to the original first outer scalar

Every actual canonical normalized label has already supplied its own
whole-slot cost, both frozen scalars and its original row correlation.
This file collects those proved estimates with the true passive-label
cardinality. All polynomial constants and thresholds are selected from
the fixed frame before the moving call or its original raw labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open CommonSupportMass

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- The first Cauchy and single-pool allowance, with the same original
leaf coefficient and the already extracted second harmonic density. -/
def outerArithmeticWeight : ℝ :=
  packet.leaf.weight * call.base ^ packet.firstOuterExponent /
    (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
    (Ideal.absNorm packet.allocation.1.val : ℝ)

theorem outerArithmeticWeight_nonneg : 0 ≤ packet.outerArithmeticWeight :=
  div_nonneg
    (div_nonneg (mul_nonneg packet.leaf.weight_nonneg (Real.rpow_nonneg call.base_pos.le _))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end RawLeafPacket

namespace CanonicalMassPacket

variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}
variable (P : CanonicalMassPacket packet input choices)

theorem arithmeticMass_le_firstOuter (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (frame : SourceFrame) (hframe : call.frame = frame)
    (ready : (N4.annulusDemand p frame).Ready call input) :
    (P.seed.refinement input P.support).arithmeticMass P.calibrations P.capacities ≤
      (4 * ((P.support.labels false).card : ℝ) * (P.support.labels true).card) *
        (input.frozenAtomBudget ^ (4 * c.geometry.slots) *
          N8ScalarWindow.reciprocal c call.frame ^ (2 * c.geometry.slots) *
          (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K) *
        call.base ^ (29 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val) *
        call.base ^ (packet.annulusLog / 6) * packet.outerArithmeticWeight := by
  have hB : 0 ≤ input.frozenAtomBudget ^ c.geometry.slots :=
    pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _
  have htail : 0 ≤ (4 * packet.leaf.weight * (P.support.labels false).card *
      (P.support.labels true).card) *
      ((input.frozenAtomBudget ^ c.geometry.slots) ^ 3 *
        (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K /
        (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
        (Ideal.absNorm packet.allocation.1.val : ℝ)) := by
    have hw := packet.leaf.weight_nonneg
    have hF := orbitalFieldFactor_nonneg K
    positivity
  have h := mul_le_mul_of_nonneg_left
    (packet.firstExternalPair_mul_secondLedger_le input hpacket horders P.seed.phases) htail
  apply (P.arithmeticMass_le_secondHarmonic hpacket horders frame hframe ready).trans
  convert h using 1
  · unfold secondHarmonicBound
    ring
  · rw [show packet.firstOuterExponent + 29 * p.loss + packet.annulusLog / 6 +
          call.node.parameters.κ * (momentMesh K c.family).val =
        packet.firstOuterExponent +
          (29 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val) +
          packet.annulusLog / 6 by ring,
      Real.rpow_add call.base_pos, Real.rpow_add call.base_pos]
    rw [show 4 * c.geometry.slots = c.geometry.slots * 4 by omega, pow_mul]
    unfold RawLeafPacket.outerArithmeticWeight
    ring

end CanonicalMassPacket

namespace N8Normalized

/-- A genuine uniform estimate for the complete normalized label
family, still retaining the original first outer arithmetic factor.
Its hypotheses contain only earlier tasks' actual constructors. -/
theorem arithmeticReduction (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) :
    ∃ cost : UniformCost,
      ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
        cost.Ready call input → ∀ (packet : RawLeafPacket call p), packet.Realizes →
        ∀ (choices : FullKappaChoices c p.loss)
          (P : CanonicalMassPacket packet input choices),
          (P.seed.refinement input P.support).arithmeticMass P.calibrations P.capacities ≤
            cost.value input.amplitude call.request.height *
              call.base ^ (31 * p.loss +
                call.node.parameters.κ * (momentMesh K c.family).val) *
              packet.outerArithmeticWeight := by
  obtain ⟨C, hC, hcards⟩ := passive_label_pair_bound c p.loss p.loss_pos
  let coefficient : ℝ :=
    4 * C * N8ScalarWindow.atomCoefficient c frame ^ (4 * c.geometry.slots) *
      N8ScalarWindow.reciprocal c frame ^ (2 * c.geometry.slots) *
      (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K * N4.uniformAnnulus c frame
  have hcoefficient : 0 ≤ coefficient := by
    have ha := (zero_le_one.trans (N8ScalarWindow.atomCoefficient_one c frame))
    have hr := (zero_le_one.trans (N8ScalarWindow.reciprocal_one c frame))
    have hF := orbitalFieldFactor_nonneg K
    have hA := (zero_le_one.trans (N4.uniformAnnulus_one_le c frame))
    dsimp only [coefficient]
    positivity
  let cost : UniformCost := {
    orders := {(0, 0)}
    coefficient := coefficient
    coefficient_nonneg := hcoefficient
    profileDegree := 8 * c.geometry.slots
    heightDegree := 0
    heightDegree_nonneg := le_rfl
    threshold := max (N8Source.normThreshold c frame) (N4.annulusDemand p frame).threshold
    threshold_one_le := (N8Source.normThreshold_one_le c frame).trans (le_max_left _ _) }
  refine ⟨cost, ?_⟩
  intro call input hframe ready packet hpacket choices P
  have hz : 0 < call.base := call.base_pos
  have horders : (0, 0) ∈ input.orders := ready.orders (by simp [cost])
  have hlarge : N8Source.normThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact (le_max_left _ _).trans ready.large
  have hready : (N4.annulusDemand p frame).Ready call input := {
    orders := by simp [N4.annulusDemand]
    large := (le_max_right _ _).trans ready.large }
  have hcard := hcards call input hlarge p packet hpacket P.seed P.support
  have hatom := input.frozenAtomBudget_pow_le frame hframe (4 * c.geometry.slots)
  rw [show 2 * (4 * c.geometry.slots) = 8 * c.geometry.slots by omega] at hatom
  have hannulus := packet.annulus_factor_le input frame hframe
  have hB : 0 ≤ input.frozenAtomBudget := zero_le_one.trans input.frozenAtomBudget_one
  have hF := orbitalFieldFactor_nonneg K
  have hR : 0 ≤ N8ScalarWindow.reciprocal c frame :=
    zero_le_one.trans (N8ScalarWindow.reciprocal_one c frame)
  have hA : 0 ≤ N8ScalarWindow.atomCoefficient c frame :=
    zero_le_one.trans (N8ScalarWindow.atomCoefficient_one c frame)
  have hamp : 0 ≤ input.amplitude := zero_le_one.trans input.amplitude_one_le
  have hcard4 :
      4 * ((P.support.labels false).card : ℝ) * (P.support.labels true).card ≤
        4 * (C * call.base ^ (2 * p.loss)) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 4)
  have hatomFactor :
      input.frozenAtomBudget ^ (4 * c.geometry.slots) *
          N8ScalarWindow.reciprocal c frame ^ (2 * c.geometry.slots) *
          (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K ≤
        (N8ScalarWindow.atomCoefficient c frame ^ (4 * c.geometry.slots) *
          input.amplitude ^ (8 * c.geometry.slots)) *
          N8ScalarWindow.reciprocal c frame ^ (2 * c.geometry.slots) *
          (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hatom (pow_nonneg hR _)) (Nat.cast_nonneg _)) hF
  have hpre := mul_le_mul hcard4 hatomFactor
    (show 0 ≤ input.frozenAtomBudget ^ (4 * c.geometry.slots) *
        N8ScalarWindow.reciprocal c frame ^ (2 * c.geometry.slots) *
        (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K by positivity)
    (show 0 ≤ 4 * (C * call.base ^ (2 * p.loss)) by positivity)
  have hscale := mul_le_mul_of_nonneg_right hpre
    (Real.rpow_nonneg call.base_pos.le
      (29 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val))
  have hboth := mul_le_mul hscale hannulus
    (Real.rpow_nonneg call.base_pos.le (packet.annulusLog / 6))
    (show 0 ≤ (4 * (C * call.base ^ (2 * p.loss))) *
      ((N8ScalarWindow.atomCoefficient c frame ^ (4 * c.geometry.slots) *
        input.amplitude ^ (8 * c.geometry.slots)) *
        N8ScalarWindow.reciprocal c frame ^ (2 * c.geometry.slots) *
        (Arithmetic.unitSubgroup c).index * orbitalFieldFactor K) *
      call.base ^ (29 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val)
      by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hboth packet.outerArithmeticWeight_nonneg
  have hlocal := P.arithmeticMass_le_firstOuter hpacket horders frame hframe hready
  rw [hframe] at hlocal
  apply hlocal.trans (hfinal.trans_eq ?_)
  change _ = coefficient * input.amplitude ^ (8 * c.geometry.slots) *
    (1 + call.request.height) ^ (0 : ℝ) *
    call.base ^ (31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val) *
    packet.outerArithmeticWeight
  rw [Real.rpow_zero, mul_one,
    show 31 * p.loss + call.node.parameters.κ * (momentMesh K c.family).val =
      2 * p.loss + (29 * p.loss +
        call.node.parameters.κ * (momentMesh K c.family).val) by ring,
    Real.rpow_add call.base_pos]
  dsimp only [coefficient]
  ring

end N8Normalized
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.arithmeticMass_le_firstOuter
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized.arithmeticReduction
