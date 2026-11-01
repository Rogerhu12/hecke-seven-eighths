import HeckeSkeleton.HighBinSupport.HighNormFormSlots
import HeckeSkeleton.HighBinSupport.HighNormFormIntegral
/-!
A concrete finite compensation packet with height-independent labels.
The pieces are integrals of literal subset terms.  Their sum is forced by
the finite product identity, so they cannot be altered by adding arbitrary
cancelling quantities.  Selected error slots and zero slots are retained.
-/

noncomputable section
namespace HighBinVerified.NormForm
open MeasureTheory
open scoped BigOperators

/-- The complete compensated product before integration. -/
def fullSlotKernel {Row X : Type*} (J : ℕ)
    (prefactor : Row → X → ℂ) (main error : Fin J → Row → X → ℂ)
    (u : Row) (x : X) : ℂ :=
  prefactor u x * ∏ i, (main i u x + error i u x)

/-- One literal error-subset contribution. -/
def errorSubsetKernel {Row X : Type*} (J : ℕ)
    (prefactor : Row → X → ℂ) (main error : Fin J → Row → X → ℂ)
    (selected : Finset (Fin J)) (u : Row) (x : X) : ℂ :=
  prefactor u x * (∏ i ∈ selected, error i u x) *
    ∏ i ∈ (Finset.univ : Finset (Fin J)) \ selected, main i u x

/-- Every error subset participates, including subsets with zero product. -/
theorem fullSlotKernel_eq_sum {Row X : Type*} (J : ℕ)
    (prefactor : Row → X → ℂ) (main error : Fin J → Row → X → ℂ)
    (u : Row) (x : X) :
    fullSlotKernel J prefactor main error u x =
      ∑ selected ∈ (Finset.univ : Finset (Fin J)).powerset,
        errorSubsetKernel J prefactor main error selected u x := by
  unfold fullSlotKernel errorSubsetKernel
  rw [full_slot_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected hselected
  ring

/-- Rows in one static amplitude label. -/
def labelledRows {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (selector : Row → Label) (label : Label) : Finset Row :=
  rows.filter (fun u => selector u = label)

@[simp] theorem mem_labelledRows {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (selector : Row → Label) (label : Label) (u : Row) :
    u ∈ labelledRows rows selector label ↔ u ∈ rows ∧ selector u = label := by
  simp [labelledRows]

/-- Different arithmetic selection fibers do not repeat a row.  Apply
this to the triple (dyadic shell, chosen height index, chosen bin index),
before introducing the compensation-subset labels. -/
theorem labelledRows_disjoint {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (selector : Row → Label) {a b : Label} (hab : a ≠ b) :
    Disjoint (labelledRows rows selector a) (labelledRows rows selector b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u hua hub
  exact hab (((mem_labelledRows rows selector a u).mp hua).2.symm.trans
    ((mem_labelledRows rows selector b u).mp hub).2)

/-- Every retained row belongs to exactly one arithmetic selection fiber. -/
theorem existsUnique_labelledRows {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (selector : Row → Label) (u : Row) (hu : u ∈ rows) :
    ∃! label, u ∈ labelledRows rows selector label := by
  refine ⟨selector u, ?_, ?_⟩
  · exact (mem_labelledRows rows selector (selector u) u).mpr ⟨hu, rfl⟩
  · intro label hlabel
    exact ((mem_labelledRows rows selector label u).mp hlabel).2.symm

/-- Grouping a finite row family by static labels preserves its exact sum. -/
theorem sum_labelledRows {Row Label : Type*} [Fintype Label] [DecidableEq Label]
    (rows : Finset Row) (selector : Row → Label) (value : Row → ℂ) :
    (∑ label : Label, ∑ u ∈ labelledRows rows selector label, value u) =
      ∑ u ∈ rows, value u := by
  unfold labelledRows
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The actual integrated subset pieces furnish the two required total
identifications.  Genuine integrability, supplied by the norm-form
majorant, justifies linearity.  No moving label set is integrated. -/
theorem fullSlotKernel_integral_decomposition
    {Row X Label : Type*} [MeasurableSpace X] [Fintype Label] [DecidableEq Label]
    (μ : Measure X) (rows : Finset Row) (J : ℕ)
    (prefactor : Row → X → ℂ) (main error : Fin J → Row → X → ℂ)
    (selector : Finset (Fin J) → Row → Label)
    (hpieces : ∀ selected ∈ (Finset.univ : Finset (Fin J)).powerset,
      ∀ u ∈ rows, Integrable (errorSubsetKernel J prefactor main error selected u) μ) :
    (∑ u ∈ rows, ∫ x, fullSlotKernel J prefactor main error u x ∂μ) =
      ∑ selected ∈ (Finset.univ : Finset (Fin J)).powerset,
        ∑ label : Label, ∑ u ∈ labelledRows rows (selector selected) label,
          ∫ x, errorSubsetKernel J prefactor main error selected u x ∂μ := by
  simp_rw [sum_labelledRows]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  have hfun : fullSlotKernel J prefactor main error u =
      fun x => ∑ selected ∈ (Finset.univ : Finset (Fin J)).powerset,
        errorSubsetKernel J prefactor main error selected u x := by
    funext x
    exact fullSlotKernel_eq_sum J prefactor main error u x
  rw [hfun]
  exact integral_finsetSum _ (fun selected hs => hpieces selected hs u hu)

/-- A fixed grid and fixed slot system have a fixed finite total label
count, even after every compensation subset has been retained. -/
theorem full_packet_label_card (J N : ℕ) :
    Fintype.card (Finset (Fin J) × (Fin J → Fin (N + 1))) =
      2 ^ J * (N + 1) ^ J := by
  simp

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.fullSlotKernel_eq_sum
#print axioms HighBinVerified.NormForm.fullSlotKernel_integral_decomposition
#print axioms HighBinVerified.NormForm.full_packet_label_card
