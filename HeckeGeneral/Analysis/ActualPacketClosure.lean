import HeckeGeneral.Analysis.PrincipalProbeClosure
import HeckeGeneral.Analysis.HeckeEndpointTarget

/-! Section 7 closure for the actual principal probes, with the common
slot count and saving chosen before the target. A different finite S and
probe may be chosen for each target. The finite-height comparison is an
explicit downstream premise; this theorem does not rename it as T/I/P. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

theorem heckePacket_sevenEighths_of_principalComparisons
    (ω : HeckeCharacter K) (hseed : PacketSeedReciprocal K ω)
    (hcompare : ∀ B : ℝ, 7 / 8 < B → B ≤ 11 / 12 →
      (∀ χ r, r ∈ heckePacketZeros K ω χ → 1 / 2 ≤ r → r ≤ 1 → r ≤ B) →
      ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ χ : HeckePacketIndex K ω,
        ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
          (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (J : ℝ → ℂ),
          AnalyticOnNhd ℂ (principalCorrection K S P χ.val) (rightHalfPlane (7 / 8)) ∧
          (∀ s : ℂ, 7 / 8 < s.re → ‖principalCorrection K S P χ.val s - 1‖ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε))) ∧
          PhysicalHeightComparison J (principalLineProbe K S P χ.val)
            (B - 11 / 16) (closureSaving (B - 7 / 8) J₀))
    (χ : HeckePacketIndex K ω) :
    MeromorphicZeroFreeOn (heckeContinuation K χ.val) (rightHalfPlane (7 / 8)) := by
  have himp : CommonStrictImprovement (heckePacketZeros K ω) := by
    intro B hlo hhi hbound
    obtain ⟨J₀, hJ₀, htarget⟩ := hcompare B hlo hhi hbound
    have hgap : 0 < B - 7 / 8 := by linarith
    have hσ := closureSaving_pos hgap hJ₀
    have hσsmall := closureSaving_lt_half_gap hgap (J := J₀)
    refine ⟨closureSaving (B - 7 / 8) J₀, hσ, hσsmall, ?_⟩
    intro ψ r hr _hrlo _hrhi
    obtain ⟨S, P, J, hH, hHbound, hlow, hhigh⟩ := htarget ψ
    have hfree := principal_zeroFree_of_heightComparison K S P ψ.val J
      hhi hσ hσsmall hlow hhigh hH hHbound
    obtain ⟨s, hsr, hzero⟩ := hr
    apply le_of_not_gt
    intro hn
    exact (not_lt_of_ge (hfree.2 s (by change _ < s.re; rwa [hsr]))) hzero
  exact meromorphic_family_sevenEighths_of_seed_improvement
    (fun ψ : HeckePacketIndex K ω => heckeContinuation K ψ.val)
    (fun ψ z _ => meromorphicOn_heckeContinuation K ψ.val z (Set.mem_univ _))
    (hseed.seedBound K) (CommonStrictImprovement.at_supremum _ himp) χ

end HeckeGeneral.ThetaSkeleton.Physical
