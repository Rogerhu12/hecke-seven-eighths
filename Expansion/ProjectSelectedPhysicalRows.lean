import Expansion.ProjectMeromorphicDetector
import Expansion.SelectedBufferedRows
import HeckeGeneral.Analysis.BufferedPhysicalRowBin

/-!
Actual arithmetic rows are assigned one buffered index before contour
integration.  This adapter uses the original packet boundary and constructs
the choice; a preselected bin, detector spike, or row-count bound is not an
input.  It requires the complete project dependency environment to compile.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ω ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))
variable (P : ProbeData K S) (E : RowEulerData K S P)

abbrev RowBufferIndex (B e : ℝ) :=
  BufferedIndex (51 / 100) B e ⌈(B - 51 / 100) / e⌉₊

def RowBufferGood (B e T : ℝ) (u : FrequencyRow K S)
    (b : RowBufferIndex B e) : Prop :=
  51 / 100 ≤ b.center ∧ b.center ≤ B ∧
  (51 / 100 < b.center → rowZeroAbove K S ψ Θ P E u
    (3 * (b.1.val + 1 : ℕ) * T) b.center) ∧
  rowZeroBelow K S ψ Θ P E u
    (3 * (b.1.val + 2 : ℕ) * T) (b.center + 2 * e)

variable (hψ : ψ ∈ HeckePacket K ω)
variable (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
variable {B e : ℝ} (hB0 : (51 / 100 : ℝ) ≤ B) (hB : B ≤ 1) (he : 0 < e)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)

theorem exists_rowBufferIndex (T : ℝ) (u : FrequencyRow K S) :
    ∃ b : RowBufferIndex B e, RowBufferGood K S ψ Θ P E B e T u b := by
  obtain ⟨i, k, hi, hi', hk, ha, ha', hz, hb⟩ :=
    exists_actual_row_buffer_of_packet K S ψ Θ P E hψ hΘ hB0 hB he hbound u
      (T := T)
  refine ⟨(⟨i - 1, by omega⟩, ⟨k, by omega⟩), ?_⟩
  have hi1 : i - 1 + 1 = i := by omega
  have hi2 : i - 1 + 2 = i + 1 := by omega
  simpa only [RowBufferGood, BufferedIndex.center, hi1, hi2] using
    (show 51 / 100 ≤ 51 / 100 + e * k ∧
      51 / 100 + e * k ≤ B ∧
      (51 / 100 < 51 / 100 + e * k →
        rowZeroAbove K S ψ Θ P E u (3 * i * T) (51 / 100 + e * k)) ∧
      rowZeroBelow K S ψ Θ P E u (3 * (i + 1 : ℕ) * T)
        (51 / 100 + e * k + 2 * e) from ⟨ha, ha', hz, hb⟩)

def rowBufferIndex (T : ℝ) (u : FrequencyRow K S) : RowBufferIndex B e :=
  Classical.choose (exists_rowBufferIndex K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T u)

theorem rowBufferIndex_good (T : ℝ) (u : FrequencyRow K S) :
    RowBufferGood K S ψ Θ P E B e T u
      (rowBufferIndex K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T u) :=
  Classical.choose_spec
    (exists_rowBufferIndex K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T u)

def retainedShellRows (U : ℝ) : Finset (FrequencyRow K S) :=
  (frequencyRows K S (2 * U)).filter fun u =>
    U < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u

def selectedPhysicalRows (U T : ℝ) (b : RowBufferIndex B e) :
    Finset (FrequencyRow K S) :=
  selectedRows (retainedShellRows K S U)
    (rowBufferIndex K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T) b

/-- D-SUPPORT for every label, including empty labels. -/
theorem selectedPhysicalRows_norm_envelope (U T : ℝ) (b : RowBufferIndex B e) :
    selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b ⊆
      frequencyRows K S (2 * U) :=
  (selectedRows_subset _ _ _).trans (Finset.filter_subset _ _)

/-- A selected live bin is a subset of the old wide buffered bin.  The
old analytic upper bounds are therefore still available on its rows. -/
theorem selectedPhysicalRows_subset_buffered (U T : ℝ) (b : RowBufferIndex B e)
    (hlive : (51 / 100 : ℝ) < b.center) :
    selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b ⊆
      bufferedPhysicalRowBin K S ψ Θ P E
        (3 * (b.1.val + 1 : ℕ) * T) (3 * (b.1.val + 2 : ℕ) * T)
        U (2 * U) b.center e := by
  intro u hu
  have hmem := (mem_selectedRows _ _ b u).mp hu
  have hshell := Finset.mem_filter.mp hmem.1
  have hgood := rowBufferIndex_good K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T u
  rw [hmem.2] at hgood
  exact (mem_bufferedPhysicalRowBin_iff K S ψ Θ P E _ _ _ _ _ _ u).mpr
    ⟨hshell.1, hshell.2.1, hshell.2.2, hgood.2.2.1 hlive, hgood.2.2.2⟩

/-- The floor keeps its upper-zero condition without demanding a selected
zero.  It uses the same chosen fixed rows as the live bins. -/
theorem selectedPhysicalRows_floor (U T : ℝ) (b : RowBufferIndex B e)
    (hfloor : b.center = 51 / 100) :
    ∀ u ∈ selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b,
      rowZeroBelow K S ψ Θ P E u
        (3 * (b.1.val + 2 : ℕ) * T) (51 / 100 + 2 * e) := by
  intro u hu
  have hmem := (mem_selectedRows _ _ b u).mp hu
  have hgood := rowBufferIndex_good K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T u
  rw [hmem.2] at hgood
  simpa only [hfloor] using hgood.2.2.2

/-- The original fixed-row sum is counted exactly once. -/
theorem sum_selectedPhysicalRows (U T : ℝ) (value : FrequencyRow K S → ℂ) :
    (∑ b : RowBufferIndex B e,
      ∑ u ∈ selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b,
        value u) = ∑ u ∈ retainedShellRows K S U, value u :=
  sum_selectedRows _ _ _

theorem selectedPhysicalRows_disjoint (U T : ℝ) {b b' : RowBufferIndex B e}
    (h : b ≠ b') :
    Disjoint (selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b)
      (selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b') :=
  selectedRows_disjoint _ _ h

/-- The last dyadic shell is clipped at the same global retained endpoint
used by the large-row decomposition.  Its natural 2U envelope is kept. -/
def clippedSelectedPhysicalRows (U globalUpper T : ℝ) (b : RowBufferIndex B e) :
    Finset (FrequencyRow K S) :=
  selectedRows ((retainedShellRows K S U).filter
    fun u => frequencyRowNorm K S u ≤ globalUpper)
    (rowBufferIndex K S ω ψ Θ P E hψ hΘ hB0 hB he hbound T) b

theorem clippedSelectedPhysicalRows_subset (U globalUpper T : ℝ)
    (b : RowBufferIndex B e) :
    clippedSelectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U globalUpper T b ⊆
      selectedPhysicalRows K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b := by
  intro u hu
  obtain ⟨hu, hs⟩ := (mem_selectedRows _ _ b u).mp hu
  exact (mem_selectedRows _ _ b u).mpr ⟨(Finset.mem_filter.mp hu).1, hs⟩

theorem clippedSelectedPhysicalRows_bounds (U globalUpper T : ℝ)
    (b : RowBufferIndex B e) (u : FrequencyRow K S)
    (hu : u ∈ clippedSelectedPhysicalRows K S ω ψ Θ P E
      hψ hΘ hB0 hB he hbound U globalUpper T b) :
    u ∈ frequencyRows K S (2 * U) ∧ frequencyRowNorm K S u ≤ globalUpper := by
  constructor
  · exact selectedPhysicalRows_norm_envelope K S ω ψ Θ P E hψ hΘ hB0 hB he hbound U T b
      (clippedSelectedPhysicalRows_subset K S ω ψ Θ P E hψ hΘ hB0 hB he hbound
        U globalUpper T b hu)
  · exact (Finset.mem_filter.mp ((mem_selectedRows _ _ b u).mp hu).1).2

theorem sum_clippedSelectedPhysicalRows (U globalUpper T : ℝ)
    (value : FrequencyRow K S → ℂ) :
    (∑ b : RowBufferIndex B e,
      ∑ u ∈ clippedSelectedPhysicalRows K S ω ψ Θ P E
        hψ hΘ hB0 hB he hbound U globalUpper T b, value u) =
      ∑ u ∈ (retainedShellRows K S U).filter
        (fun u => frequencyRowNorm K S u ≤ globalUpper), value u :=
  sum_selectedRows _ _ _

end Expansion.Project
