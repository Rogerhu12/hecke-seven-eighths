import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleCompensation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScalarArithmetic

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Apply the two-stage scalar cancellation to the original atom tables

The norm estimates consumed here are for the two actual bare common
scalars, separately. The original pool residue, both original norm
tilts, both complete frozen ideals and both remaining scale products
are then assembled without replacing any of them by a chosen scalar.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

theorem t3b_poolScalar_norm_le :
    ‖packet.poolScalar‖ ≤
      (Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ^ p.tilt := by
  unfold poolScalar
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg
      ((Arithmetic.data c).exteriorNorm_pos packet.second.physical.first.poolPower).le _)]
  exact (mul_le_mul_of_nonneg_left
    (actualIdealResidue_norm_le_one (Arithmetic.context c) _ _)
    (Real.rpow_nonneg
      ((Arithmetic.data c).exteriorNorm_pos packet.second.physical.first.poolPower).le _)).trans_eq
      (mul_one _)

theorem t3b_secondAtomScalar_norm (phases : OriginalPhaseData packet) (side : Bool) :
    ‖packet.secondAtomScalar hpacket phases side‖ =
      ‖packet.firstCommonScalar side‖ * ‖packet.poolScalar‖ *
        packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) *
        ‖(packet.firstAtomTable hpacket phases side).commonScalar (packet.secondBranch side)‖ := by
  simp only [secondAtomScalar, firstExternalScalar, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (packet.firstScaleProduct_pos side).le _)]

theorem t3b_commonScalar_scale_le
    (input : ProfileInput call) (phases : OriginalPhaseData packet) (side : Bool)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfirst : ‖packet.firstCommonScalar side‖ ^ 2 ≤
      C₁ / (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ))
    (hsecond : ‖(packet.firstAtomTable hpacket phases side).commonScalar
        (packet.secondBranch side)‖ ^ 2 ≤
      C₂ / (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ)) :
    ‖packet.secondAtomScalar hpacket phases side‖ *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket side) ≤
      Real.sqrt (C₁ * C₂) * (T3b.profileAnnulus c call.frame) ^ (2 * c.geometry.slots) *
        call.base ^ (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) / 2 +
          2 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)) /
        (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) := by
  have hN₁ : 0 < (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (N4.firstFrozenIdeal_ne_zero packet side))
  have hN₂ : 0 < (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (N4.secondFrozenIdeal_ne_zero packet side))
  have hQ : 1 ≤ (Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower := by
    change (1 : ℝ) ≤ (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr packet.second.physical.first.poolPower.property.1)
  have hB : 1 ≤ (T3b.profileAnnulus c call.frame) ^ c.geometry.slots :=
    one_le_pow₀ (T3b.profileAnnulus_one_le c call.frame)
  have h := T3b.twoStage_scalar_sqrt_le call.base
    (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)
    ((T3b.profileAnnulus c call.frame) ^ c.geometry.slots)
    (packet.firstScaleProduct side) (packet.t3bBeforeScaleProduct hpacket side)
    (Ideal.absNorm (N4.firstFrozenIdeal packet side))
    (Ideal.absNorm (N4.secondFrozenIdeal packet side))
    ((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower) p.tilt
    ‖packet.firstCommonScalar side‖
    ‖(packet.firstAtomTable hpacket phases side).commonScalar (packet.secondBranch side)‖
    ‖packet.poolScalar‖ C₁ C₂
    call.base_pos hB (packet.firstScaleProduct_pos side)
    (packet.t3bBeforeScaleProduct_pos hpacket side) hN₁ hN₂ hQ
    (packet.t3b_poolNorm_le_firstFrozenNorm hpacket side) p.tilt_pos.le p.tilt_half
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC₁ hC₂ hfirst hsecond
    packet.t3b_poolScalar_norm_le (packet.t3b_firstScale_compensated input side)
    (packet.t3b_firstScale_upper input side) (packet.t3b_secondScale_upper hpacket input side)
  rw [← packet.t3b_secondAtomScalar_norm hpacket phases side] at h
  simpa only [← pow_mul, Nat.mul_comm c.geometry.slots 2] using h

theorem t3b_paired_commonScalar_scale_le
    (input : ProfileInput call) (phases : OriginalPhaseData packet)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfirst : ∀ side, ‖packet.firstCommonScalar side‖ ^ 2 ≤
      C₁ / (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ))
    (hsecond : ∀ side, ‖(packet.firstAtomTable hpacket phases side).commonScalar
        (packet.secondBranch side)‖ ^ 2 ≤
      C₂ / (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ)) :
    (‖packet.secondAtomScalar hpacket phases false‖ *
        ‖packet.secondAtomScalar hpacket phases true‖) *
      (Real.sqrt (packet.t3bBeforeScaleProduct hpacket false) *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket true)) ≤
      (C₁ * C₂ * (T3b.profileAnnulus c call.frame) ^ (4 * c.geometry.slots)) *
        call.base ^ (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) +
          4 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)) /
        ((Ideal.absNorm (packet.secondIdeal false) : ℝ) *
          (Ideal.absNorm (packet.secondIdeal true) : ℝ)) := by
  have hL := packet.t3b_commonScalar_scale_le hpacket input phases false C₁ C₂ hC₁ hC₂
    (hfirst false) (hsecond false)
  have hR := packet.t3b_commonScalar_scale_le hpacket input phases true C₁ C₂ hC₁ hC₂
    (hfirst true) (hsecond true)
  have h := mul_le_mul hL hR
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    ((mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)).trans hL)
  calc
    _ = (‖packet.secondAtomScalar hpacket phases false‖ *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket false)) *
        (‖packet.secondAtomScalar hpacket phases true‖ *
          Real.sqrt (packet.t3bBeforeScaleProduct hpacket true)) := by ring
    _ ≤ _ := h
    _ = _ := by
      rw [div_mul_div_comm, ← N4.secondFrozenIdeal_eq packet false,
        ← N4.secondFrozenIdeal_eq packet true]
      congr 1
      have hz := Real.rpow_pos_of_pos call.base_pos
        (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) / 2 +
          2 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z))
      have he : 2 * (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) / 2 +
          2 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)) =
          -(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) +
            4 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) := by ring
      calc
        _ = (Real.sqrt (C₁ * C₂)) ^ 2 *
            ((T3b.profileAnnulus c call.frame) ^ (2 * c.geometry.slots)) ^ 2 *
            (call.base ^ (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) / 2 +
              2 * p.tilt * (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z))) ^ 2 := by ring
        _ = _ := by
          rw [Real.sq_sqrt (mul_nonneg hC₁ hC₂), ← pow_mul,
            ← Real.rpow_mul_natCast call.base_pos.le]
          norm_num only [Nat.cast_ofNat]
          simp only [show 2 * c.geometry.slots * 2 = 4 * c.geometry.slots by omega,
            mul_comm _ (2 : ℝ), he]
    

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_paired_commonScalar_scale_le
