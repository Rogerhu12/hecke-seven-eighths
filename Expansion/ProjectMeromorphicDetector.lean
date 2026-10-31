import Expansion.BufferedSelection
import HeckeGeneral.Analysis.PhysicalRowPacketBoundary

/-!
Project adapter for the self-contained meromorphic-order detector.  The only
analytic facts used here are the already proved ordinary Hecke continuation
and its nonzero germ at two.  No improved zero-free boundary is an input to
finite zero detection.  This file must be compiled in the supplied project;
the standalone cache does not contain its vendored dependencies.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable {ι : Type*}

def heckeFamily (χ : ι → HeckeCharacter K) : Expansion.MeromorphicFamily ι where
  function i := heckeContinuation K (χ i)
  meromorphic i := meromorphicOn_heckeContinuation K (χ i)
  finite_at_two i := meromorphicOrderAt_heckeContinuation_ne_top K (χ i) 2

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
variable (P : ProbeData K S) (E : RowEulerData K S P)

def rowFamily (u : FrequencyRow K S) :
    Expansion.MeromorphicFamily {χ // χ ∈ physicalRowFamily K S ψ Θ P E u} :=
  heckeFamily K (fun χ => χ.val)

def rowMaximum (u : FrequencyRow K S) (height : ℝ) : ℝ :=
  (rowFamily K S ψ Θ P E u).maximum (51 / 100) 1 height

theorem rowMaximum_bounds (u : FrequencyRow K S) (height : ℝ) :
    (51 / 100 : ℝ) ≤ rowMaximum K S ψ Θ P E u height ∧
      rowMaximum K S ψ Θ P E u height ≤ 1 :=
  (rowFamily K S ψ Θ P E u).maximum_bounds (by norm_num) height

/-- The maximum captures every genuine zero in the source's original strip.
Zeros between one half and the floor are paid for by the floor itself. -/
theorem rowZeroBelow_iff (u : FrequencyRow K S) {height upper : ℝ}
    (hu : (51 / 100 : ℝ) ≤ upper) :
    rowZeroBelow K S ψ Θ P E u height upper ↔
      rowMaximum K S ψ Θ P E u height ≤ upper := by
  constructor
  · intro hb
    exact (rowFamily K S ψ Θ P E u).maximum_le_boundary hu
      (fun χ s hlo hhi ht hz => hb χ.val χ.property s hz (by linarith) hhi ht)
  · intro hm χ hχ s hz hlo hhi ht
    by_cases hf : (51 / 100 : ℝ) ≤ s.re
    · exact ((rowFamily K S ψ Θ P E u).zero_re_le_maximum
        (i := ⟨χ, hχ⟩) hf hhi ht hz).trans hm
    · exact (le_of_lt (lt_of_not_ge hf)).trans hu

theorem rowZeroAbove_iff (u : FrequencyRow K S) {height lower : ℝ}
    (hl : (51 / 100 : ℝ) < lower) :
    rowZeroAbove K S ψ Θ P E u height lower ↔
      lower ≤ rowMaximum K S ψ Θ P E u height := by
  constructor
  · rintro ⟨χ, hχ, s, hz, hlo, hhi, ht⟩
    exact hlo.trans ((rowFamily K S ψ Θ P E u).zero_re_le_maximum
      (i := ⟨χ, hχ⟩) (hl.le.trans hlo) hhi ht hz)
  · intro hm
    obtain ⟨χ, s, hz, ht, hs, _, hhi⟩ :=
      (rowFamily K S ψ Θ P E u).maximum_attained (hl.trans_le hm)
    exact ⟨χ.val, χ.property, s, hz, by simpa only [rowMaximum, hs] using hm, hhi, ht⟩

/-- Both zero heights arise from one finite buffered choice.  The finite
family boundary is the pre-existing family boundary, not a stronger one. -/
theorem exists_actual_row_buffer (u : FrequencyRow K S)
    {B e T : ℝ} (hB0 : (51 / 100 : ℝ) ≤ B) (hB : B ≤ 1) (he : 0 < e)
    (hboundary : ∀ χ ∈ physicalRowFamily K S ψ Θ P E u, ∀ s : ℂ,
      0 < meromorphicOrderAt (heckeContinuation K χ) s →
      1 / 2 ≤ s.re → s.re ≤ 1 → s.re ≤ B) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ ⌈(B - 51 / 100) / e⌉₊ + 1 ∧
      k ≤ ⌊(B - 51 / 100) / e⌋₊ ∧
      let a := 51 / 100 + e * k
      51 / 100 ≤ a ∧ a ≤ B ∧
      (51 / 100 < a → rowZeroAbove K S ψ Θ P E u (3 * i * T) a) ∧
      rowZeroBelow K S ψ Θ P E u (3 * (i + 1 : ℕ) * T) (a + 2 * e) := by
  obtain ⟨i, k, hi, hi', hk, ha, haB, hselected, hupper⟩ :=
    (rowFamily K S ψ Θ P E u).exists_buffered_zero_bin hB0 hB he
      ⌈(B - 51 / 100) / e⌉₊ (explicit_buffered_width he)
      (fun χ s hs hs' hz => hboundary χ.val χ.property s hz (by linarith) hs')
  refine ⟨i, k, hi, hi', hk, ha, haB, ?_, ?_⟩
  · intro hlive
    obtain ⟨χ, s, hz, hs, hs', ht⟩ := hselected hlive
    have hhi : s.re ≤ 1 := by
      by_contra hgt
      have ho := meromorphicOrderAt_heckeContinuation K χ.val (lt_of_not_ge hgt)
      change 0 < meromorphicOrderAt (heckeContinuation K χ.val) s at hz
      rw [ho] at hz
      exact (lt_irrefl 0) hz
    exact ⟨χ.val, χ.property, s, hz, hs, hhi, ht⟩
  · intro χ hχ s hz hs hs' ht
    by_cases hfloor : (51 / 100 : ℝ) ≤ s.re
    · exact (hupper ⟨χ, hχ⟩ s hfloor hs' ht hz).le
    · linarith [lt_of_not_ge hfloor]

/-- The boundary needed above is already supplied by the original packet
boundary.  This version introduces no separate bound on the detector family. -/
theorem exists_actual_row_buffer_of_packet {ω : HeckeCharacter K}
    (hψ : ψ ∈ HeckePacket K ω)
    (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
    {B e T : ℝ} (hB0 : (51 / 100 : ℝ) ≤ B) (hB : B ≤ 1) (he : 0 < e)
    (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B) (u : FrequencyRow K S) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ ⌈(B - 51 / 100) / e⌉₊ + 1 ∧
      k ≤ ⌊(B - 51 / 100) / e⌋₊ ∧
      let a := 51 / 100 + e * k
      51 / 100 ≤ a ∧ a ≤ B ∧
      (51 / 100 < a → rowZeroAbove K S ψ Θ P E u (3 * i * T) a) ∧
      rowZeroBelow K S ψ Θ P E u (3 * (i + 1 : ℕ) * T) (a + 2 * e) := by
  apply exists_actual_row_buffer K S ψ Θ P E u hB0 hB he
  intro χ hχ s hz hs hs'
  let i : HeckePacketIndex K ω :=
    ⟨χ, physicalRowFamily_subset_packet K S hψ Θ hΘ P E u hχ⟩
  exact hbound i s.re ⟨s, rfl, hz⟩ hs hs'

end Expansion.Project
