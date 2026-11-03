import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Analysis.HeckeEndpointTarget

/-!
# Actual finite-order premise of the paired fourth moment

Finite-order Hecke characters are members of the same actual packet.
Consequently its common boundary B supplies P's finite-order boundary at
(1+κ)/2=B when κ=2B-1. No separate finite-order 7/8 theorem is assumed.

This file only supplies that premise. It does not prove canonical moment
estimates or the bridge from a zero boundary to quantitative prime bounds.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Characters ConditionalMoments

variable (K : Type) [Field K] [NumberField K]
variable {ω : HeckeCharacter K} {B : ℝ}

/-- Every finite-order zero to the right of B would also be a packet zero.
The seed provides its upper clipping bound; B>7/8 supplies the lower one. -/
theorem finiteOrderBoundary_of_packet_common_bound
    (hseed : SeedBound (heckePacketZeros K ω))
    (hB : 7 / 8 < B)
    (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ConditionalMoments.FiniteOrderBoundary (K := K) B := by
  intro χ hχ s hs
  apply le_of_not_gt
  intro hzero
  let i : HeckePacketIndex K ω :=
    ⟨χ, finiteOrder_mem_heckePacket K ω χ hχ⟩
  have hr : s.re ∈ heckePacketZeros K ω i := by
    exact ⟨s, rfl, hzero⟩
  have hrseed : s.re ≤ 11 / 12 := hseed i s.re hr
  have hrlo : 1 / 2 ≤ s.re := by linarith
  have hrhi : s.re ≤ 1 := by linarith
  have hrB : s.re ≤ B := hbound i s.re hr hrlo hrhi
  exact (not_lt_of_ge hrB) hs

/-- The actual dynamic parameter is in P's admissible interval, and P's
boundary argument is exactly the packet boundary B. This is the premise
to pass to `PInput`; it does not wrap or strengthen that moment input. -/
theorem dynamic_P_premise_of_packet_common_bound
    (hseed : SeedBound (heckePacketZeros K ω))
    (hB : 7 / 8 < B) (hBhi : B ≤ 11 / 12)
    (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    (3 / 4 ≤ 2 * B - 1 ∧ 2 * B - 1 ≤ 5 / 6) ∧
      ConditionalMoments.FiniteOrderBoundary (K := K)
        ((1 + (2 * B - 1)) / 2) := by
  obtain ⟨hκlo, hκhi, hκB⟩ := ConditionalMoments.dynamic_kappa hB hBhi
  refine ⟨⟨hκlo, hκhi⟩, ?_⟩
  rw [hκB]
  exact finiteOrderBoundary_of_packet_common_bound K hseed hB hbound

end HeckeGeneral.Analysis
