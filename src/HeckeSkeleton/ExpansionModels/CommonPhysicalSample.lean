import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# One physical parameter point per amplitude label

An individual row may not choose its own physical prime-profile parameter.
For each label we instead maximize the cardinality of its pointwise row set
inside a nonempty physical parameter domain.  Finite base rows imply that
this maximum is attained, without compactness or continuity hypotheses.

The resulting integral theorem is a majorant.  It does not identify sampled
row contributions with contributions of a different physical row.  Exact
transport of those contributions is a separate finite-injection argument.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe.CommonPhysicalSample

open MeasureTheory
open scoped Classical BigOperators

variable {Parameter Label Row : Type*}

/-- An attained maximum, because only finitely many row subsets occur. -/
theorem exists_card_max_point (base : Finset Row) (B : Set Parameter)
    (hB : B.Nonempty) (rows : Parameter → Finset Row)
    (hrows : ∀ x ∈ B, rows x ⊆ base) :
    ∃ x₀ ∈ B, ∀ x ∈ B, (rows x).card ≤ (rows x₀).card := by
  let possible := base.powerset.filter (fun R => ∃ x ∈ B, rows x = R)
  have hp : possible.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    refine ⟨rows x, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hrows x hx), ?_⟩⟩
    exact ⟨x, hx, rfl⟩
  obtain ⟨R₀, hR₀, hmax⟩ := possible.exists_max_image Finset.card hp
  obtain ⟨x₀, hx₀, hr₀⟩ := (Finset.mem_filter.mp hR₀).2
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  rw [hr₀]
  apply hmax
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hrows x hx), ⟨x, hx, rfl⟩⟩

/-- A common physical point for all rows of each fixed amplitude label. -/
def point (base : Finset Row) (B : Set Parameter) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base) (label : Label) : Parameter :=
  Classical.choose (exists_card_max_point base B hB (fun x => rows x label)
    (fun x hx => hrows x hx label))

theorem point_mem (base : Finset Row) (B : Set Parameter) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base) (label : Label) :
    point base B hB rows hrows label ∈ B :=
  (Classical.choose_spec (exists_card_max_point base B hB (fun x => rows x label)
    (fun x hx => hrows x hx label))).1

theorem card_le_at_point (base : Finset Row) (B : Set Parameter) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base)
    (x : Parameter) (hx : x ∈ B) (label : Label) :
    (rows x label).card ≤ (rows (point base B hB rows hrows label) label).card :=
  (Classical.choose_spec (exists_card_max_point base B hB (fun x => rows x label)
    (fun x hx => hrows x hx label))).2 x hx

/-- Every sampled row satisfies all simultaneous prime-slot threshold
properties at this ONE physical parameter point. -/
theorem simultaneous_properties_at_point
    (base : Finset Row) (B : Set Parameter) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base)
    (property : Parameter → Label → Row → Prop)
    (hproperty : ∀ x ∈ B, ∀ label, ∀ u ∈ rows x label, property x label u)
    (label : Label) (u : Row)
    (hu : u ∈ rows (point base B hB rows hrows label) label) :
    property (point base B hB rows hrows label) label u :=
  hproperty _ (point_mem base B hB rows hrows label) label u hu

theorem weighted_card_sum_le (base : Finset Row) (B : Set Parameter) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base)
    (labels : Finset Label) (weight : Label → ℝ)
    (hweight : ∀ label ∈ labels, 0 ≤ weight label) (x : Parameter) (hx : x ∈ B) :
    (∑ label ∈ labels, weight label * (rows x label).card) ≤
      ∑ label ∈ labels, weight label *
        (rows (point base B hB rows hrows label) label).card := by
  apply Finset.sum_le_sum
  intro label hl
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast card_le_at_point base B hB rows hrows x hx label) (hweight label hl)

/-- The pointwise cardinality maximum gives a bound for the unchanged
physical integral.  Integrability of the actual kernel is explicit. -/
theorem norm_integral_le_sampled_cards
    [MeasurableSpace Parameter] (μ : Measure Parameter)
    (base : Finset Row) (B : Set Parameter) (hBm : MeasurableSet B) (hB : B.Nonempty)
    (rows : Parameter → Label → Finset Row)
    (hrows : ∀ x ∈ B, ∀ label, rows x label ⊆ base)
    (labels : Finset Label) (weight : Label → ℝ)
    (hweight : ∀ label ∈ labels, 0 ≤ weight label)
    (f : Parameter → ℂ) (g : Parameter → ℝ)
    (hf : IntegrableOn f B μ) (hg : IntegrableOn g B μ)
    (hg0 : ∀ x ∈ B, 0 ≤ g x)
    (hpoint : ∀ x ∈ B, ‖f x‖ ≤ g x *
      ∑ label ∈ labels, weight label * (rows x label).card) :
    ‖∫ x in B, f x ∂μ‖ ≤ (∫ x in B, g x ∂μ) *
      ∑ label ∈ labels, weight label *
        (rows (point base B hB rows hrows label) label).card := by
  let C : ℝ := ∑ label ∈ labels, weight label *
    (rows (point base B hB rows hrows label) label).card
  have hm : ∀ᵐ x ∂μ.restrict B, ‖f x‖ ≤ g x * C := by
    filter_upwards [ae_restrict_mem hBm] with x hx
    exact (hpoint x hx).trans (mul_le_mul_of_nonneg_left
      (weighted_card_sum_le base B hB rows hrows labels weight hweight x hx) (hg0 x hx))
  calc
    _ ≤ ∫ x in B, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in B, g x * C ∂μ := integral_mono_ae hf.norm (hg.mul_const C) hm
    _ = _ := integral_mul_const C g

end ExpansionRecipe.CommonPhysicalSample

#print axioms ExpansionRecipe.CommonPhysicalSample.exists_card_max_point
#print axioms ExpansionRecipe.CommonPhysicalSample.norm_integral_le_sampled_cards
