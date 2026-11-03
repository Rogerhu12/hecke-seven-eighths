import HeckeGeneral.Analysis.TInputRanges
import HeckeGeneral.Analysis.MomentEndpointBridge

/-! Every actual companion presentation used in a physical row belongs to
the same Hecke packet. Its common boundary therefore controls every row
family at every height before any strict improvement is attempted. Only
the existing finite-order row-character calibration and finite-order ray
characters are used; no independent finite-order endpoint is assumed. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

private theorem packet_mul_actual_finite {ω χ θ : HeckeCharacter K}
    (hχ : χ ∈ HeckePacket K ω) (hθ : FiniteOrder θ) :
    χ * θ ∈ HeckePacket K ω :=
  packet_mul_finiteOrder (heckeLogNorm K) ω hχ hθ

theorem physicalRowFamily_subset_packet {ω ψ : HeckeCharacter K}
    (hψ : ψ ∈ HeckePacket K ω) (Θ : Finset (HeckeCharacter K))
    (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
    (P : ProbeData K S) (E : RowEulerData K S P) (u : FrequencyRow K S) :
    (↑(physicalRowFamily K S ψ Θ P E u) : Set (HeckeCharacter K)) ⊆
      HeckePacket K ω := by
  intro χ hχ
  obtain ⟨θ, hθ, hχ⟩ := Finset.mem_biUnion.mp hχ
  have hθf := hΘ θ hθ
  have huf := E.rows.finite_order u
  have hθu := finiteOrder_mem_heckePacket K ω (θ * E.rows.character u) (hθf.mul huf)
  have hθui := finiteOrder_mem_heckePacket K ω (θ * conjugate (E.rows.character u))
    (hθf.mul huf.inv)
  have hψθ := packet_mul_actual_finite K hψ hθf
  have hψiθ := packet_mul_actual_finite K (heckePacket_inv K ω hψ) hθf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
  rcases hχ with rfl | rfl | rfl | rfl
  · exact hθu
  · exact hθui
  · exact packet_mul_actual_finite K hψθ huf.inv
  · exact packet_mul_actual_finite K hψiθ huf

/-- The same B controls every height, not just a chosen finite box. -/
theorem physicalRowFamily_zeroBelow_of_common_bound {ω ψ : HeckeCharacter K} {B : ℝ}
    (hψ : ψ ∈ HeckePacket K ω) (Θ : Finset (HeckeCharacter K))
    (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B) (u : FrequencyRow K S) (height : ℝ) :
    rowZeroBelow K S ψ Θ P E u height B := by
  intro χ hχ ρ hzero hlo hhi _hheight
  let i : HeckePacketIndex K ω :=
    ⟨χ, physicalRowFamily_subset_packet K S hψ Θ hΘ P E u hχ⟩
  exact hbound i ρ.re ⟨ρ, rfl, hzero⟩ hlo hhi

/-- A positive seed plus the common bound also controls unclipped zeros,
so the actual companion continuation has no zeros right of B. -/
theorem physicalRowFamily_zeroFree_of_common_bound {ω ψ : HeckeCharacter K} {B : ℝ}
    (hψ : ψ ∈ HeckePacket K ω) (Θ : Finset (HeckeCharacter K))
    (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hseed : SeedBound (heckePacketZeros K ω)) (hB : 7 / 8 < B)
    (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (u : FrequencyRow K S) (χ : HeckeCharacter K)
    (hχ : χ ∈ physicalRowFamily K S ψ Θ P E u) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane B) := by
  refine ⟨fun s _ => meromorphicOn_heckeContinuation K χ s (mem_univ _), ?_⟩
  intro s hs
  apply le_of_not_gt
  intro hzero
  let i : HeckePacketIndex K ω :=
    ⟨χ, physicalRowFamily_subset_packet K S hψ Θ hΘ P E u hχ⟩
  have hz : s.re ∈ heckePacketZeros K ω i := ⟨s, rfl, hzero⟩
  have hseed' := hseed i s.re hz
  have hb := hbound i s.re hz (by change B < s.re at hs; linarith) (by linarith)
  exact (not_lt_of_ge hb) hs

end HeckeGeneral.ThetaSkeleton.Physical
