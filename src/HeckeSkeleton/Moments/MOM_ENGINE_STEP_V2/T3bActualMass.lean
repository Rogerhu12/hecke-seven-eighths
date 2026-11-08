module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRawMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPrimeProfiles

@[expose] public section

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
      simpa only [mul_one, atomRadius] using mul_le_mul_of_nonneg_left (one_le_pow₀ hP : 1 ≤ profile ^ 2)
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

private theorem rawMass_le_of_table
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h : A.R} {k : ℕ}
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h k)
    (C : A.GeneralArithmeticContext σ η hS) (d : OrdinaryAtomTable (K := K) k)
    (cap : ℕ) (hcap : k ≤ cap) (annulus profile Z total : ℝ)
    (hannulus : 1 ≤ annulus) (hprofile : 1 ≤ profile) (hZ : 1 < Z)
    (hdata : s.Zslot = Z ∧ s.length = d.length ∧ s.characters = d.characters ∧
      s.w = d.slotWeight ∧ s.X₁ = d.scale₁ false ∧ s.X₂ = d.scale₂ false)
    (hmask : ∀ I, d.characters.mask I = 0 ∨ d.characters.mask I = 1)
    (hwindow : ∀ i, ∀ q ∈ s.allocation.slots i,
      (Ideal.absNorm q.asIdeal : ℝ) ≤ annulus * Z ^ d.length i)
    (hweight : ∀ i q, ‖d.slotWeight i q‖ ≤ profile)
    (htotal : d.scale₁ false * d.scale₂ false * (∏ i, Z ^ d.length i) = total) :
    s.rawMass ≤ (atomRadius K annulus profile) ^ (3 * cap) * Real.sqrt total /
      (Ideal.absNorm s.allocation.frozenIdeal : ℝ) := by
  rcases hdata with ⟨hbase, hlength, hcharacters, hw, hx₁, hx₂⟩
  have hb := rawMass_le_scale_quotient s C cap hcap annulus profile
    (atomRadius K annulus profile)
    (by rw [hbase]; exact hZ)
    (by rw [hlength]; exact fun i => (d.length_pos i).le)
    hannulus (zero_le_one.trans hprofile)
    (atomRadius_one hannulus hprofile)
    (atomRadius_annulus (zero_le_one.trans hannulus) hprofile)
    (atomRadius_profile (zero_le_one.trans hannulus))
    (atomRadius_prime (zero_le_one.trans hannulus) hprofile)
    (by rw [hcharacters]; exact hmask)
    (by intro i q hq; rw [hbase, hlength]; exact hwindow i q hq)
    (by intro i q _; rw [hw]; exact hweight i q)
  have htotal' : s.X₁ * s.X₂ * (∏ i, s.Zslot ^ s.length i) = total := by
    rw [hbase, hlength, hx₁, hx₂]
    exact htotal
  exact hb.trans_eq (congrArg (fun t : ℝ =>
    (atomRadius K annulus profile) ^ (3 * cap) * Real.sqrt t /
      (Ideal.absNorm s.allocation.frozenIdeal : ℝ)) htotal')

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
  let d := packet.t3bUnscaledTable hpacket phases side
  refine T3b.rawMass_le_of_table s (Arithmetic.context c) d
    c.geometry.slots (packet.t3bUnscaled_slots_le hpacket side)
    (T3b.profileAnnulus c call.frame) P call.base
    (packet.t3bBeforeScaleProduct hpacket side)
    (T3b.profileAnnulus_one_le c call.frame) hP call.domain.scale ?_
    (packet.t3bUnscaled_mask_two hpacket phases side)
    (fun i q hq => packet.t3bUnscaled_prime_norm hpacket phases input side i q hq) ?_
    (packet.t3bUnscaled_scale_total hpacket phases side)
  · cases side <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i q
    exact (congrArg (fun z : ℂ => ‖z‖)
      (packet.t3bUnscaled_slotWeight hpacket phases input side i q)).trans_le (hprofiles _ _)

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
