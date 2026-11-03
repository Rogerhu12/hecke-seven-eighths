import HeckeGeneral.Analysis.HeckeNormPole
import HeckeGeneral.Analysis.MellinZeroDetector

/-!
# The actual Hecke endpoint and the remaining physical-probe consumer

The target uses the existing globally meromorphic `heckeContinuation` of
an actual continuous unitary Hecke character.  The conditional theorem
below closes *derived detector estimates*.  It does not identify those
estimates with T, I, or P, and does not prove their transfer from moments.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Characters Filter
open scoped Topology BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The intended conclusion over one field, with genuine zeros measured
by positive meromorphic order.  Pure norm poles remain permitted. -/
def HeckeSevenEighths : Prop :=
  ∀ χ : HeckeCharacter K,
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (7 / 8))

/-- The full goal.  The universe matches the imported global Tate theorem. -/
def GeneralHeckeSevenEighths : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], HeckeSevenEighths F

abbrev HeckePacketIndex (ω : HeckeCharacter K) := ↥(HeckePacket K ω)

def heckePacketZeros (ω : HeckeCharacter K) (χ : HeckePacketIndex K ω) : Set ℝ :=
  zeroRealParts (heckeContinuation K χ.val)

/-- The analytic output of single-row amplification and smooth dyadic
continuation.  This remains an obligation, not a definition of MI. -/
def PacketSeedReciprocal (ω : HeckeCharacter K) : Prop :=
  ∀ β : ℝ, 11 / 12 < β → ∀ χ : HeckePacketIndex K ω,
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (rightHalfPlane β) ∧
      ∃ s₀ ∈ rightHalfPlane β,
        (fun w => heckeContinuation K χ.val w * G w) =ᶠ[𝓝[≠] s₀] (fun _ => 1)

/-- The downstream physical estimate with the manuscript's common saving.
The slot count and saving are chosen before the target character; the
probe, numerator and implicit constants may depend on that target.
Constructing these objects from T/I/P is still a separate obligation. -/
def PacketImprovedDetector (ω : HeckeCharacter K) : Prop :=
  ∀ B : ℝ, 7 / 8 < B → B ≤ 11 / 12 →
    (∀ χ r, r ∈ heckePacketZeros K ω χ → 1 / 2 ≤ r → r ≤ 1 → r ≤ B) →
    ∃ J : ℕ, 0 < J ∧ ∀ χ : HeckePacketIndex K ω,
      ∃ (f : ℝ → ℂ) (H : ℂ → ℂ),
        PhysicalProbeBound f (B - closureSaving (B - 7 / 8) J) ∧
        InitialMellinDetectorIdentity (heckeContinuation K χ.val) f H
          (B - closureSaving (B - 7 / 8) J)

theorem PacketSeedReciprocal.seedBound {ω : HeckeCharacter K}
    (h : PacketSeedReciprocal K ω) : SeedBound (heckePacketZeros K ω) := by
  intro χ r hr
  obtain ⟨s, hsr, hzero⟩ := hr
  by_contra hn
  have hgt : 11 / 12 < r := lt_of_not_ge hn
  let β : ℝ := (r + 11 / 12) / 2
  have hβ : 11 / 12 < β := by dsimp [β]; linarith
  obtain ⟨G, hG, s₀, hs₀, hid₀⟩ := h β hβ χ
  have hid := meromorphic_germ_identity_of_preconnected
    (fun z hz => (meromorphicOn_heckeContinuation K χ.val z (Set.mem_univ _)).mul
      (hG z hz).meromorphicAt)
    (fun _ _ => (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) _).meromorphicAt)
    (isPreconnected_rightHalfPlane β) hs₀ hid₀
  have hs : s ∈ rightHalfPlane β := by
    change β < s.re
    dsimp [β]
    linarith
  have horder := order_nonpos_of_analytic_multiplier
    (meromorphicOn_heckeContinuation K χ.val s (Set.mem_univ _))
    (hG s hs) analyticAt_const (by norm_num : (1 : ℂ) ≠ 0) (hid s hs)
  exact (not_lt_of_ge horder) hzero

theorem PacketImprovedDetector.commonStrictImprovement {ω : HeckeCharacter K}
    (h : PacketImprovedDetector K ω) : CommonStrictImprovement (heckePacketZeros K ω) := by
  intro B hlo hhi hbound
  obtain ⟨J, hJ, hdet⟩ := h B hlo hhi hbound
  have hgap : 0 < B - 7 / 8 := by linarith
  refine ⟨closureSaving (B - 7 / 8) J, closureSaving_pos hgap hJ,
    closureSaving_lt_half_gap hgap, ?_⟩
  intro χ r hr _hrlo _hrhi
  obtain ⟨s, hsr, hzero⟩ := hr
  obtain ⟨f, H, hf, hid⟩ := hdet χ
  have hfree := meromorphicZeroFreeOn_of_initial_physicalMellin
    (fun z _ => meromorphicOn_heckeContinuation K χ.val z (Set.mem_univ _)) hf hid
  apply le_of_not_gt
  intro hn
  have hs : s ∈ rightHalfPlane (B - closureSaving (B - 7 / 8) J) := by
    change B - closureSaving (B - 7 / 8) J < s.re
    rwa [hsr]
  exact (not_lt_of_ge (hfree.2 s hs)) hzero

theorem heckePacket_sevenEighths_of_detectors (ω : HeckeCharacter K)
    (hseed : PacketSeedReciprocal K ω) (himp : PacketImprovedDetector K ω)
    (χ : HeckePacketIndex K ω) :
    MeromorphicZeroFreeOn (heckeContinuation K χ.val) (rightHalfPlane (7 / 8)) := by
  exact meromorphic_family_sevenEighths_of_seed_improvement
    (fun ψ : HeckePacketIndex K ω => heckeContinuation K ψ.val)
    (fun ψ z _ => meromorphicOn_heckeContinuation K ψ.val z (Set.mem_univ _))
    (hseed.seedBound K)
    (CommonStrictImprovement.at_supremum _ (himp.commonStrictImprovement K)) χ

theorem heckeSevenEighths_of_detectors
    (hseed : ∀ ω : HeckeCharacter K, PacketSeedReciprocal K ω)
    (himp : ∀ ω : HeckeCharacter K, PacketImprovedDetector K ω) : HeckeSevenEighths K := by
  intro χ
  exact heckePacket_sevenEighths_of_detectors K χ (hseed χ) (himp χ)
    ⟨χ, base_mem_heckePacket K χ⟩

theorem generalHeckeSevenEighths_of_detectors
    (hseed : ∀ (F : Type) [Field F] [NumberField F],
      ∀ ω : HeckeCharacter F, PacketSeedReciprocal F ω)
    (himp : ∀ (F : Type) [Field F] [NumberField F],
      ∀ ω : HeckeCharacter F, PacketImprovedDetector F ω) : GeneralHeckeSevenEighths := by
  intro F _ _
  exact heckeSevenEighths_of_detectors F (hseed F) (himp F)

variable (F : Type) [Field F] [NumberField F]

/-- Actual-continuation data required for abelian descent.  Construction
from `K = F(ζ₁₂)` and norm pullback is not supplied by this structure.
The unique possible pole must match the product's order: meromorphic
factorization alone would allow cancellation of a zero against a pole. -/
structure HeckeFactorizationDescentData (χ : HeckeCharacter F) (η : HeckeCharacter K) where
  factors : Finset (HeckeCharacter F)
  target_mem : χ ∈ factors
  factorization : ∀ s ∈ rightHalfPlane (7 / 8),
    heckeContinuation K η =ᶠ[𝓝[≠] s]
      (fun w => ∏ ψ ∈ factors, heckeContinuation F ψ w)
  pole_matching : ∀ s ∈ rightHalfPlane (7 / 8),
    (∀ ψ ∈ factors, AnalyticAt ℂ (heckeContinuation F ψ) s) ∨
    ∃ p ∈ factors, meromorphicOrderAt (heckeContinuation F p) s = (-1 : ℤ) ∧
      meromorphicOrderAt (heckeContinuation K η) s = (-1 : ℤ) ∧
      ∀ ψ ∈ factors, ψ ≠ p → AnalyticAt ℂ (heckeContinuation F ψ) s

theorem hecke_sevenEighths_of_factorization {χ : HeckeCharacter F} {η : HeckeCharacter K}
    (D : HeckeFactorizationDescentData K F χ η)
    (hη : MeromorphicZeroFreeOn (heckeContinuation K η) (rightHalfPlane (7 / 8))) :
    MeromorphicZeroFreeOn (heckeContinuation F χ) (rightHalfPlane (7 / 8)) := by
  classical
  exact meromorphicZeroFreeOn_of_factorization D.factors (heckeContinuation F)
    (heckeContinuation K η) (rightHalfPlane (7 / 8))
    (fun ψ _ z _ => meromorphicOn_heckeContinuation F ψ z (Set.mem_univ _))
    hη D.factorization D.pole_matching D.target_mem

end HeckeGeneral.Analysis
