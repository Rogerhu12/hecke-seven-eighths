import HeckeGeneral.Analysis.IdealDyadicContinuation
import HeckeGeneral.Analysis.HeckeEndpointTarget

/-!
The actual compact-uniform dyadic shell estimate implies the analytic seed.
The reciprocal germ is constructed from the proved Re(s)>1 series identity;
it is not an input. The number-theoretic shell estimate remains an input.
-/

noncomputable section
namespace HeckeGeneral.Analysis.IdealDyadicMobius

open NumberField IsDedekindDomain HeckeGeneral.Characters Filter
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

theorem deletedContinuation_ne_zero_above_one (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ S s ≠ 0 := by
  apply mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K χ S
    (lt_trans zero_lt_one hs))
  rw [heckeContinuation_eq_series K χ hs]
  exact heckeLSeries_ne_zero K χ hs

/-- The initial germ follows from the actual dyadic series identity and
actual Euler-product nonvanishing, both already proved on Re(s)>1. -/
theorem deleted_dyadic_initial_reciprocal (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    (fun w => heckeDeletedContinuation K χ S w * dyadicTotal K χ S w)
      =ᶠ[𝓝[≠] s₀] (fun _ => 1) := by
  have hnear : ∀ᶠ w in 𝓝[≠] s₀, 1 < w.re :=
    nhdsWithin_le_nhds ((isOpen_rightHalfPlane 1).mem_nhds hs₀)
  filter_upwards [hnear] with w hw
  rw [dyadicTotal_eq_reciprocal K χ S hw]
  exact mul_inv_cancel₀ (deletedContinuation_ne_zero_above_one K χ S hw)

/-- The actual finite-shell estimate supplies holomorphy; the initial
identity is proved above, and the existing meromorphic consumer propagates it. -/
theorem heckeContinuation_zeroFreeOn_of_compact_growth (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {b : ℝ}
    (hG : CompactShellGrowth K χ S b) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  let c : ℝ := max b 1 + 1
  have hc : 1 < (c : ℂ).re := by
    change 1 < c
    dsimp [c]
    linarith [le_max_right b 1]
  have hbc : (c : ℂ) ∈ rightHalfPlane b := by
    change b < c
    dsimp [c]
    linarith [le_max_left b 1]
  exact heckeContinuation_zeroFreeOn_of_deleted_initial_reciprocal K χ S
    (analyticOnNhd_dyadicTotal_of_compact_growth K χ S hG) hbc
    (deleted_dyadic_initial_reciprocal K χ S hc)

theorem heckeContinuation_seed_of_compact_growth (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hG : CompactShellGrowth K χ S (11 / 12)) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (11 / 12)) :=
  heckeContinuation_zeroFreeOn_of_compact_growth K χ S hG

/-- Target-dependent finite deletions are permitted. This analytic consumer
does not claim the moment constants are uniform over target characters. -/
theorem packetSeedReciprocal_of_compact_growth (ω : HeckeCharacter K)
    (hG : ∀ χ : HeckePacketIndex K ω,
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), CompactShellGrowth K χ.val S (11 / 12)) :
    PacketSeedReciprocal K ω := by
  intro β hβ χ
  obtain ⟨S, hχ⟩ := hG χ
  let c : ℝ := max β 1 + 1
  have hc : 1 < (c : ℂ).re := by
    change 1 < c
    dsimp [c]
    linarith [le_max_right β 1]
  have hβc : (c : ℂ) ∈ rightHalfPlane β := by
    change β < c
    dsimp [c]
    linarith [le_max_left β 1]
  have han : AnalyticOnNhd ℂ (dyadicTotal K χ.val S) (rightHalfPlane β) :=
    (analyticOnNhd_dyadicTotal_of_compact_growth K χ.val S hχ).mono
      (fun w hw => lt_trans hβ hw)
  obtain ⟨hfull, hid⟩ := heckeDeletedContinuation_reciprocal_to_full K χ.val S han
    (deleted_dyadic_initial_reciprocal K χ.val S hc)
  exact ⟨fun w => heckeEulerDeletionPolynomial K χ.val S w * dyadicTotal K χ.val S w,
    hfull, (c : ℂ), hβc, hid⟩

theorem packetSeedBound_of_compact_growth (ω : HeckeCharacter K)
    (hG : ∀ χ : HeckePacketIndex K ω,
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), CompactShellGrowth K χ.val S (11 / 12)) :
    SeedBound (heckePacketZeros K ω) :=
  PacketSeedReciprocal.seedBound K (packetSeedReciprocal_of_compact_growth K ω hG)

end HeckeGeneral.Analysis.IdealDyadicMobius
