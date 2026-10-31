import HeckeSkeleton.HighBinSupport.BufferedDetectorGeometry
import HeckeGeneral.Analysis.BufferedPhysicalRowBin
import HeckeGeneral.Analysis.PhysicalRowPacketBoundary
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Buffered choices and a finite partition of the actual rows

For every physical row, a finite pigeonhole argument selects a grid center
and two successive detector heights. The upper detector condition is
proved from maximality of an observed grid level. The old common packet
boundary puts the selected center below the given B, including B = 1.

The resulting choices partition any finite family of actual frequency
rows. Each part is contained in the original fixed buffered bin, and the
number of parts is at most `(ceil (1/e) + 1)^2` per shell. These are actual
row sets, with genuine zero witnesses in every live bin.

The assigned subsets are not identified with their enclosing raw bins.
Several raw buffered bins can contain the same row. The named HIGHBIN
presentation must retain these selector subsets (or an equivalent fixed
row mask) when its block identity is constructed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualBoundaryGeometry

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinDetectorGeometry
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (ψ : HeckeCharacter K)
variable (Θ : Finset (HeckeCharacter K)) (E : RowEulerData K S P)

/-- Adjoin the trivial companion before constructing the detector. This
retains every supplied companion and covers the actual L denominator. -/
def augmentedCompanions : Finset (HeckeCharacter K) := insert 1 Θ

theorem one_mem_augmentedCompanions : 1 ∈ augmentedCompanions K Θ := by
  simp [augmentedCompanions]

theorem augmentedCompanions_finiteOrder (hΘ : ∀ θ ∈ Θ, FiniteOrder θ) :
    ∀ θ ∈ augmentedCompanions K Θ, FiniteOrder θ := by
  intro θ hθ
  rcases Finset.mem_insert.mp hθ with rfl | hθ
  · exact IsOfFinOrder.one
  · exact hΘ θ hθ

/-- Concrete geometry and actual zero data for a selected detector pair. -/
def DetectorSpec (B e T : ℝ) (u : FrequencyRow K S)
    (k : DetectorIndex (detectorDepth e)) : Prop :=
  51 / 100 ≤ gridRealPart e k.2.val ∧ gridRealPart e k.2.val ≤ B ∧
    (k.2.val = 0 ∨ rowZeroAbove K S ψ Θ P E u
      (selectedHeight T k.1.val) (gridRealPart e k.2.val)) ∧
    rowZeroBelow K S ψ Θ P E u (upperHeight T k.1.val)
      (gridRealPart e k.2.val + 2 * e)

/-- Every row admits one of the explicit finite detector choices. The
common-bound premise is the original old boundary, not a contour or
norm-form estimate. -/
theorem exists_detectorSpec (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (u : FrequencyRow K S)
    (hcommon : ∀ height : ℝ, rowZeroBelow K S ψ Θ P E u height B) :
    ∃ k : DetectorIndex (detectorDepth e), DetectorSpec K S P ψ Θ E B e T u k := by
  let active : ℕ → ℕ → Prop := fun i j =>
    rowZeroAbove K S ψ Θ P E u (selectedHeight T i) (gridRealPart e j)
  have hcap : ∀ i : ℕ, ¬ active i (detectorDepth e + 1) := by
    intro i h
    obtain ⟨χ, _, ρ, _, hρ, hρ1, _⟩ := h
    have hc := gridRealPart_cap e he
    linarith
  obtain ⟨i, j, hi, hj, hselected, hnext⟩ :=
    exists_buffered_level (detectorDepth e) active hcap
  refine ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), gridRealPart_lower e he.le j, ?_,
    hselected, ?_⟩
  · rcases hselected with hj0 | hzero
    · simpa only [hj0, gridRealPart_zero] using hB
    · obtain ⟨χ, hχ, ρ, hρ, haρ, hρ1, hheight⟩ := hzero
      have hρ0 : 1 / 2 ≤ ρ.re := by
        have ha := gridRealPart_lower e he.le j
        linarith
      exact haρ.trans (hcommon (selectedHeight T i) χ hχ ρ hρ hρ0 hρ1 hheight)
  · intro χ hχ ρ hρ hρ0 hρ1 hheight
    by_contra hupper
    apply hnext
    refine ⟨χ, hχ, ρ, hρ, ?_, hρ1, ?_⟩
    · rw [gridRealPart_succ]
      change ¬ ρ.re ≤ gridRealPart e j + 2 * e at hupper
      linarith
    · simpa only [selectedHeight_succ] using hheight

/-- Specialization to the literal common Hecke packet boundary. Every
finite-order companion is allowed, and no improved zero-free region is
assumed. -/
theorem exists_detectorSpec_of_packet {ω : HeckeCharacter K}
    (hψ : ψ ∈ HeckePacket K ω) (hΘ : ∀ θ ∈ Θ, FiniteOrder θ)
    (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hboundary : ∀ χ r, r ∈ heckePacketZeros K ω χ →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B) (u : FrequencyRow K S) :
    ∃ k : DetectorIndex (detectorDepth e), DetectorSpec K S P ψ Θ E B e T u k := by
  apply exists_detectorSpec K S P ψ Θ E B e T he hB u
  exact fun height => physicalRowFamily_zeroBelow_of_common_bound K S hψ Θ hΘ P E
    hboundary u height

/-- One canonical finite choice for every row. Its value is chosen from
the proven detector specification, rather than supplied as an input. -/
def detectorChoice (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (u : FrequencyRow K S) :
    DetectorIndex (detectorDepth e) :=
  Classical.choose (exists_detectorSpec K S P ψ Θ E B e T he hB u (hcommon u))

theorem detectorChoice_spec (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (u : FrequencyRow K S) :
    DetectorSpec K S P ψ Θ E B e T u
      (detectorChoice K S P ψ Θ E B e T he hB hcommon u) :=
  Classical.choose_spec (exists_detectorSpec K S P ψ Θ E B e T he hB u (hcommon u))

/-- The selected rows are a literal subset of the supplied arithmetic
family. Selection depends only on the row's fixed zero data. -/
def assignedRows (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (k : DetectorIndex (detectorDepth e)) :
    Finset (FrequencyRow K S) :=
  R.filter fun u => detectorChoice K S P ψ Θ E B e T he hB hcommon u = k

theorem assignedRows_subset (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (k : DetectorIndex (detectorDepth e)) :
    assignedRows K S P ψ Θ E B e T he hB hcommon R k ⊆ R :=
  Finset.filter_subset _ _

theorem assignedRows_detectorSpec (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (k : DetectorIndex (detectorDepth e))
    (u : FrequencyRow K S)
    (hu : u ∈ assignedRows K S P ψ Θ E B e T he hB hcommon R k) :
    DetectorSpec K S P ψ Θ E B e T u k := by
  have hk := (Finset.mem_filter.mp hu).2
  exact hk ▸ detectorChoice_spec K S P ψ Θ E B e T he hB hcommon u

/-- Complete finite coverage, with no omitted physical row. -/
theorem assignedRows_union (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (R : Finset (FrequencyRow K S)) :
    Finset.univ.biUnion (assignedRows K S P ψ Θ E B e T he hB hcommon R) = R := by
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, assignedRows,
    Finset.mem_filter]
  constructor
  · rintro ⟨k, hu, _⟩
    exact hu
  · intro hu
    exact ⟨detectorChoice K S P ψ Θ E B e T he hB hcommon u, hu, rfl⟩

/-- Distinct detector choices give disjoint subsets, unlike their raw
enclosing buffered bins. -/
theorem assignedRows_disjoint (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (R : Finset (FrequencyRow K S))
    (k l : DetectorIndex (detectorDepth e)) (hkl : k ≠ l) :
    Disjoint (assignedRows K S P ψ Θ E B e T he hB hcommon R k)
      (assignedRows K S P ψ Θ E B e T he hB hcommon R l) := by
  apply Finset.disjoint_left.mpr
  intro u hk hl
  have hk' := (Finset.mem_filter.mp hk).2
  have hl' := (Finset.mem_filter.mp hl).2
  exact hkl (hk'.symm.trans hl')

/-- Exact partition identity for the original row contributions. The
values may be the original full contour integrals, before any moving
amplitude subdivision is introduced. -/
theorem sum_assignedRows (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (value : FrequencyRow K S → ℂ) :
    (∑ k : DetectorIndex (detectorDepth e),
      ∑ u ∈ assignedRows K S P ψ Θ E B e T he hB hcommon R k, value u) =
        ∑ u ∈ R, value u := by
  simpa only [assignedRows] using
    Finset.sum_fiberwise R (detectorChoice K S P ψ Θ E B e T he hB hcommon) value

/-- The summand may depend on the detector index, for example through
the actual `w = 1-a-6e` contour. Each row uses its own canonical choice. -/
theorem sum_assignedRows_indexed {M : Type*} [AddCommMonoid M]
    (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S))
    (value : DetectorIndex (detectorDepth e) → FrequencyRow K S → M) :
    (∑ k : DetectorIndex (detectorDepth e),
      ∑ u ∈ assignedRows K S P ψ Θ E B e T he hB hcommon R k, value k u) =
        ∑ u ∈ R, value (detectorChoice K S P ψ Θ E B e T he hB hcommon u) u := by
  simp only [assignedRows, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- This finite set removes empty detector pieces while preserving an
explicit uniform count. -/
def retainedChoices (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (R : Finset (FrequencyRow K S)) :
    Finset (DetectorIndex (detectorDepth e)) :=
  Finset.univ.filter fun k => (assignedRows K S P ψ Θ E B e T he hB hcommon R k).Nonempty

theorem retainedChoices_card (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B) (R : Finset (FrequencyRow K S)) :
    (retainedChoices K S P ψ Θ E B e T he hB hcommon R).card ≤
      (detectorDepth e + 1) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans_eq
    ((Finset.card_univ).trans (detectorIndex_card (detectorDepth e)))

/-- Removing empty detector choices preserves the original exact row
sum, rather than merely a support inclusion. -/
theorem sum_retainedChoices (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (value : FrequencyRow K S → ℂ) :
    (∑ k ∈ retainedChoices K S P ψ Θ E B e T he hB hcommon R,
      ∑ u ∈ assignedRows K S P ψ Θ E B e T he hB hcommon R k, value u) =
        ∑ u ∈ R, value u := by
  rw [← sum_assignedRows K S P ψ Θ E B e T he hB hcommon R value]
  simp only [retainedChoices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (assignedRows K S P ψ Θ E B e T he hB hcommon R k).Nonempty
  · simp only [h, if_pos]
  · have hz : assignedRows K S P ψ Θ E B e T he hB hcommon R k = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    simp only [h, if_neg, hz, Finset.sum_empty]

/-- The literal contour summands may depend on the retained detector
index; removing empty fibers still preserves their exact row sum. -/
theorem sum_retainedChoices_indexed {M : Type*} [AddCommMonoid M]
    (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S))
    (value : DetectorIndex (detectorDepth e) → FrequencyRow K S → M) :
    (∑ k ∈ retainedChoices K S P ψ Θ E B e T he hB hcommon R,
      ∑ u ∈ assignedRows K S P ψ Θ E B e T he hB hcommon R k, value k u) =
        ∑ u ∈ R, value (detectorChoice K S P ψ Θ E B e T he hB hcommon u) u := by
  rw [← sum_assignedRows_indexed K S P ψ Θ E B e T he hB hcommon R value]
  simp only [retainedChoices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (assignedRows K S P ψ Θ E B e T he hB hcommon R k).Nonempty
  · simp only [h, if_pos]
  · have hz : assignedRows K S P ψ Θ E B e T he hB hcommon R k = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    simp only [h, if_neg, hz, Finset.sum_empty]

/-- An assigned live piece lies in the original actual buffered bin.
Only the original shell membership, lower norm cutoff and nonprincipal
row condition are supplied by the shell constructor. -/
theorem assignedRows_subset_buffered (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (normLower normUpper : ℝ)
    (hrows : R ⊆ frequencyRows K S normUpper)
    (hlower : ∀ u ∈ R, normLower < frequencyRowNorm K S u)
    (hnonprincipal : ∀ u ∈ R, ¬ principalFrequencyRow K S u)
    (k : DetectorIndex (detectorDepth e)) (hlive : k.2.val ≠ 0) :
    assignedRows K S P ψ Θ E B e T he hB hcommon R k ⊆
      bufferedPhysicalRowBin K S ψ Θ P E (selectedHeight T k.1.val)
        (upperHeight T k.1.val) normLower normUpper (gridRealPart e k.2.val) e := by
  intro u hu
  have huR := assignedRows_subset K S P ψ Θ E B e T he hB hcommon R k hu
  have hs := assignedRows_detectorSpec K S P ψ Θ E B e T he hB hcommon R k u hu
  apply (mem_bufferedPhysicalRowBin_iff K S ψ Θ P E _ _ _ _ _ _ u).mpr
  exact ⟨hrows huR, hlower u huR, hnonprincipal u huR,
    hs.2.2.1.resolve_left hlive, hs.2.2.2⟩

/-- The floor piece uses the original upper detector and never demands
a selected zero. -/
theorem assignedRows_subset_floor (B e T : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
    (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
      rowZeroBelow K S ψ Θ P E u height B)
    (R : Finset (FrequencyRow K S)) (normLower normUpper : ℝ)
    (hrows : R ⊆ frequencyRows K S normUpper)
    (hlower : ∀ u ∈ R, normLower < frequencyRowNorm K S u)
    (hnonprincipal : ∀ u ∈ R, ¬ principalFrequencyRow K S u)
    (k : DetectorIndex (detectorDepth e)) (hfloor : k.2.val = 0) :
    assignedRows K S P ψ Θ E B e T he hB hcommon R k ⊆
      (frequencyRows K S normUpper).filter (fun u =>
        normLower < frequencyRowNorm K S u ∧ ¬ principalFrequencyRow K S u ∧
          rowZeroBelow K S ψ Θ P E u (upperHeight T k.1.val) (51 / 100 + 2 * e)) := by
  intro u hu
  have huR := assignedRows_subset K S P ψ Θ E B e T he hB hcommon R k hu
  have hs := assignedRows_detectorSpec K S P ψ Θ E B e T he hB hcommon R k u hu
  apply Finset.mem_filter.mpr
  refine ⟨hrows huR, hlower u huR, hnonprincipal u huR, ?_⟩
  simpa only [hfloor, gridRealPart_zero] using hs.2.2.2

theorem rowZeroAbove_of_height_le (u : FrequencyRow K S) (H U a : ℝ)
    (hHU : H ≤ U) (h : rowZeroAbove K S ψ Θ P E u H a) :
    rowZeroAbove K S ψ Θ P E u U a := by
  obtain ⟨χ, hχ, ρ, hρ, haρ, hρ1, hheight⟩ := h
  exact ⟨χ, hχ, ρ, hρ, haρ, hρ1, hheight.trans hHU⟩

theorem rowZeroBelow_of_height_le (u : FrequencyRow K S) (H U a : ℝ)
    (hHU : H ≤ U) (h : rowZeroBelow K S ψ Θ P E u U a) :
    rowZeroBelow K S ψ Θ P E u H a := by
  intro χ hχ ρ hρ hρ0 hρ1 hheight
  exact h χ hχ ρ hρ hρ0 hρ1 (hheight.trans hHU)

/-- A row with an inner selected zero and an outer upper bound belongs
to both enclosing raw buffered bins. Thus using selector fibers, rather
than asserting disjointness of raw bins, is necessary in the partition. -/
theorem mem_two_raw_buffered_bins (u : FrequencyRow K S)
    (H₁ H₂ U₁ U₂ normLower normUpper a e : ℝ)
    (hH : H₁ ≤ H₂) (hU : U₁ ≤ U₂)
    (hu : u ∈ frequencyRows K S normUpper)
    (hlower : normLower < frequencyRowNorm K S u)
    (hnonprincipal : ¬ principalFrequencyRow K S u)
    (hselected : rowZeroAbove K S ψ Θ P E u H₁ a)
    (hupper : rowZeroBelow K S ψ Θ P E u U₂ (a + 2 * e)) :
    u ∈ bufferedPhysicalRowBin K S ψ Θ P E H₁ U₁ normLower normUpper a e ∧
      u ∈ bufferedPhysicalRowBin K S ψ Θ P E H₂ U₂ normLower normUpper a e := by
  constructor
  · apply (mem_bufferedPhysicalRowBin_iff K S ψ Θ P E _ _ _ _ _ _ u).mpr
    exact ⟨hu, hlower, hnonprincipal, hselected,
      rowZeroBelow_of_height_le K S P ψ Θ E u U₁ U₂ (a + 2 * e) hU hupper⟩
  · apply (mem_bufferedPhysicalRowBin_iff K S ψ Θ P E _ _ _ _ _ _ u).mpr
    exact ⟨hu, hlower, hnonprincipal,
      rowZeroAbove_of_height_le K S P ψ Θ E u H₁ H₂ a hH hselected, hupper⟩

end HeckeSkeleton.HighBinActualBoundaryGeometry
