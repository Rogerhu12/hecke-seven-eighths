import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRawMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPrimeProfiles

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Original prime profiles supply both actual exceptional raw masses -/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

namespace T3b

def atomRadius (K : Type) [Field K] [NumberField K] (annulus profile : ℝ) : ℝ :=
  idealCountConstant K * annulus * profile ^ 2

theorem atomRadius_one {annulus profile : ℝ} (ha : 1 ≤ annulus) (hP : 1 ≤ profile) :
    1 ≤ atomRadius K annulus profile :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_idealCountConstant K) ha) (one_le_pow₀ hP)

theorem atomRadius_annulus {annulus profile : ℝ} (ha : 0 ≤ annulus) (hP : 1 ≤ profile) :
    annulus ≤ atomRadius K annulus profile := by
  calc
    _ ≤ idealCountConstant K * annulus := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_idealCountConstant K) ha
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hP : 1 ≤ profile ^ 2)
        (mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) ha)

theorem atomRadius_profile {annulus profile : ℝ} (ha : 0 ≤ annulus) :
    annulus * profile ^ 2 ≤ atomRadius K annulus profile := by
  have hm := mul_le_mul_of_nonneg_right (one_le_idealCountConstant K)
    (mul_nonneg ha (sq_nonneg profile))
  simpa only [one_mul, atomRadius, mul_assoc] using hm

theorem atomRadius_prime {annulus profile : ℝ} (ha : 0 ≤ annulus) (hP : 1 ≤ profile) :
    idealCountConstant K * annulus * profile ≤ atomRadius K annulus profile := by
  have hp : profile ≤ profile ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hp
    (mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K)) ha)

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet) (input : ProfileInput call)

/-- The ordinary and centered records have the same computed raw
mass; only their complete value reads the comparison rectangle. -/
theorem t3b_rawMass_centered_eq_ordinary (hc : call.node.centered = true)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bExceptionalAt hpacket phases input hc side ξ h).source.rawMass =
      (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source.rawMass := rfl

theorem t3b_ordinary_rawMass_le (P : ℝ) (hP : 1 ≤ P)
    (hprofiles : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source.rawMass ≤
      (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (3 * c.geometry.slots) *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket side) /
          (Ideal.absNorm (packet.t3bUnscaledSource hpacket phases side).allocation.frozenIdeal : ℝ) := by
  let s := (packet.t3bOrdinaryExceptionalAt hpacket phases input side ξ h).source
  have hbase : s.Zslot = call.base := by cases side <;> rfl
  have hlength : s.length = (packet.t3bUnscaledTable hpacket phases side).length := by
    cases side <;> rfl
  have hcharacters : s.characters = (packet.t3bUnscaledTable hpacket phases side).characters := by
    cases side <;> rfl
  have hweight : s.w = (packet.t3bUnscaledTable hpacket phases side).slotWeight := by
    cases side <;> rfl
  have hwindow (i) (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ s.allocation.slots i) :
      (Ideal.absNorm q.asIdeal : ℝ) ≤ T3b.profileAnnulus c call.frame * s.Zslot ^ s.length i := by
    rw [hbase, hlength]
    exact packet.t3bUnscaled_prime_norm hpacket phases input side i q hq
  have hp (i) (q : HeightOneSpectrum (𝓞 K)) (_hq : q ∈ s.allocation.slots i) : ‖s.w i q‖ ≤ P := by
    rw [hweight, packet.t3bUnscaled_slotWeight hpacket phases input]
    exact hprofiles _ _
  have hb := T3b.rawMass_le_scale_quotient s (Arithmetic.context c)
    c.geometry.slots (packet.t3bUnscaled_slots_le hpacket side)
    (T3b.profileAnnulus c call.frame) P
    (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P)
    (by rw [hbase]; exact call.domain.scale)
    (by rw [hlength]; exact fun i => ((packet.t3bUnscaledTable hpacket phases side).length_pos i).le)
    (T3b.profileAnnulus_one_le c call.frame) (zero_le_one.trans hP)
    (T3b.atomRadius_one (T3b.profileAnnulus_one_le c call.frame) hP)
    (T3b.atomRadius_annulus (T3b.profileAnnulus_pos c call.frame).le hP)
    (T3b.atomRadius_profile (T3b.profileAnnulus_pos c call.frame).le)
    (T3b.atomRadius_prime (T3b.profileAnnulus_pos c call.frame).le hP)
    (by rw [hcharacters]; exact packet.t3bUnscaled_mask_two hpacket phases side)
    hwindow hp
  have htotal : s.X₁ * s.X₂ * (∏ i, s.Zslot ^ s.length i) =
      packet.t3bBeforeScaleProduct hpacket side := by
    rw [hbase, hlength]
    have hx₁ : s.X₁ = (packet.t3bUnscaledTable hpacket phases side).scale₁ false := by
      cases side <;> rfl
    have hx₂ : s.X₂ = (packet.t3bUnscaledTable hpacket phases side).scale₂ false := by
      cases side <;> rfl
    rw [hx₁, hx₂]
    exact packet.t3bUnscaled_scale_total hpacket phases side
  rw [htotal] at hb
  exact hb

theorem t3b_centered_rawMass_le (hc : call.node.centered = true) (P : ℝ) (hP : 1 ≤ P)
    (hprofiles : ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ P)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bExceptionalAt hpacket phases input hc side ξ h).source.rawMass ≤
      (T3b.atomRadius K (T3b.profileAnnulus c call.frame) P) ^ (3 * c.geometry.slots) *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket side) /
          (Ideal.absNorm (packet.t3bUnscaledSource hpacket phases side).allocation.frozenIdeal : ℝ) := by
  rw [packet.t3b_rawMass_centered_eq_ordinary hpacket phases input hc side ξ h]
  exact packet.t3b_ordinary_rawMass_le hpacket phases input P hP hprofiles side ξ h

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_ordinary_rawMass_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_centered_rawMass_le
