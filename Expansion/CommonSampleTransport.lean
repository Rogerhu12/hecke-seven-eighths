import HeckeSkeleton.ExpansionModels.CommonPhysicalSample
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact transport to a common physical sample

For a fixed label, the rows at any physical parameter inject into a row set
of maximal cardinality.  The injection is chosen once for each finite row
subset.  Thus each transported contribution is a finite measurable
combination of the original kernels, with at most one original row at each
parameter.  The exact integral identity and the uniform per-row bound are
both preserved.  No new amplitude label is introduced.

Transported contributions are indexed by sampled rows; they are not asserted
to be the original kernel of that sampled row.  The bound must be uniform
over the original row set, as in the physical high-presentation bound.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.CommonSampleTransport

open MeasureTheory
open scoped Classical BigOperators

variable {Row Parameter : Type*}

def rowEmbedding (A B : Finset Row) (h : A.card ≤ B.card) : A ↪ B :=
  A.equivFin.toEmbedding.trans ((Fin.castLEEmb h).trans B.equivFin.symm.toEmbedding)

def transportAlong {A B : Finset Row} (e : A ↪ B) (f : A → ℂ) (v : B) : ℂ :=
  ∑ u : A, if e u = v then f u else 0

theorem sum_transportAlong {A B : Finset Row} (e : A ↪ B) (f : A → ℂ) :
    (∑ v : B, transportAlong e f v) = ∑ u : A, f u := by
  unfold transportAlong
  rw [Finset.sum_comm]
  simp

theorem transportAlong_at_image {A B : Finset Row} (e : A ↪ B) (f : A → ℂ) (u : A) :
    transportAlong e f (e u) = f u := by
  simp [transportAlong, e.injective.eq_iff]

theorem transportAlong_norm_le {A B : Finset Row} (e : A ↪ B) (f : A → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ u, ‖f u‖ ≤ C) (v : B) :
    ‖transportAlong e f v‖ ≤ C := by
  by_cases hv : ∃ u, e u = v
  · obtain ⟨u, rfl⟩ := hv
    rw [transportAlong_at_image]
    exact hf u
  · have he : ∀ u, e u ≠ v := by simpa only [not_exists] using hv
    simpa [transportAlong, he] using hC

def patterns (base target : Finset Row) : Finset (Finset Row) :=
  base.powerset.filter fun A => A.card ≤ target.card

theorem mem_patterns {base target A : Finset Row} :
    A ∈ patterns base target ↔ A ⊆ base ∧ A.card ≤ target.card := by
  simp only [patterns, Finset.mem_filter, Finset.mem_powerset]

def patternEmbedding (base target : Finset Row) (A : patterns base target) : A.val ↪ target :=
  rowEmbedding A.val target (mem_patterns.mp A.property).2

def patternPiece (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ) (A : patterns base target) (v : target) (x : Parameter) : ℂ :=
  if rows x = A.val then
    transportAlong (patternEmbedding base target A) (fun u => kernel u.val x) v else 0

def movingPiece (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ) (v : target) (x : Parameter) : ℂ :=
  ∑ A : patterns base target, patternPiece base target rows kernel A v x

theorem movingPiece_eq (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ) (x : Parameter)
    (hx : rows x ∈ patterns base target) (v : target) :
    movingPiece base target rows kernel v x =
      transportAlong (patternEmbedding base target ⟨rows x, hx⟩)
        (fun u => kernel u.val x) v := by
  let A₀ : patterns base target := ⟨rows x, hx⟩
  have he (A : patterns base target) : rows x = A.val ↔ A = A₀ := by
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      rw [h]
  simp only [movingPiece, patternPiece, he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem sum_movingPiece (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ) (x : Parameter)
    (hx : rows x ∈ patterns base target) :
    (∑ v : target, movingPiece base target rows kernel v x) =
      ∑ u ∈ rows x, kernel u x := by
  simp_rw [movingPiece_eq base target rows kernel x hx]
  rw [sum_transportAlong]
  exact Finset.sum_coe_sort (rows x) (fun u => kernel u x)

theorem movingPiece_norm_le (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ) (x : Parameter)
    (hx : rows x ∈ patterns base target) (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ u ∈ rows x, ‖kernel u x‖ ≤ C) (v : target) :
    ‖movingPiece base target rows kernel v x‖ ≤ C := by
  rw [movingPiece_eq base target rows kernel x hx]
  exact transportAlong_norm_le _ _ C hC (fun u => hkernel u.val u.property) v

section Measurability

variable [MeasurableSpace Parameter]

/-- Measurability of all row-membership predicates suffices: there are only
finitely many possible row subsets. -/
theorem measurableSet_rows_eq (base : Finset Row) (rows : Parameter → Finset Row)
    (hrows : ∀ x, rows x ⊆ base)
    (hmem : ∀ u ∈ base, MeasurableSet {x | u ∈ rows x})
    (A : Finset Row) (hA : A ⊆ base) : MeasurableSet {x | rows x = A} := by
  have heq : {x | rows x = A} =
      ⋂ u : base, {x | (u.val ∈ rows x ↔ u.val ∈ A)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h u
      rw [h]
    · intro h
      apply Finset.ext
      intro u
      by_cases hu : u ∈ base
      · exact h ⟨u, hu⟩
      · exact iff_of_false (fun hm => hu (hrows x hm)) (fun hm => hu (hA hm))
  rw [heq]
  apply MeasurableSet.iInter
  intro u
  by_cases hu : u.val ∈ A
  · simpa only [hu, iff_true] using hmem u.val u.property
  · simpa only [hu, iff_false, Set.compl_ofPred] using (hmem u.val u.property).compl

theorem patternPiece_integrable (μ : Measure Parameter) (D : Set Parameter)
    (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ)
    (hkernel : ∀ u ∈ base, IntegrableOn (kernel u) D μ)
    (hsets : ∀ A ∈ patterns base target, MeasurableSet {x | rows x = A})
    (A : patterns base target) (v : target) :
    IntegrableOn (patternPiece base target rows kernel A v) D μ := by
  have hf : Integrable
      (fun x => transportAlong (patternEmbedding base target A) (fun u => kernel u.val x) v)
      (μ.restrict D) := by
    unfold transportAlong
    apply integrable_finsetSum
    intro u _
    by_cases hu : patternEmbedding base target A u = v
    · simp only [hu, ite_true]
      exact hkernel u.val ((mem_patterns.mp A.property).1 u.property)
    · simp only [hu, ite_false]
      exact integrable_zero _ _ _
  have he : patternPiece base target rows kernel A v =
      {x | rows x = A.val}.indicator
        (fun x => transportAlong (patternEmbedding base target A) (fun u => kernel u.val x) v) := by
    funext x
    simp only [patternPiece, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [he]
  unfold IntegrableOn
  exact hf.indicator (hsets A.val A.property)

theorem movingPiece_integrable (μ : Measure Parameter) (D : Set Parameter)
    (base target : Finset Row) (rows : Parameter → Finset Row)
    (kernel : Row → Parameter → ℂ)
    (hkernel : ∀ u ∈ base, IntegrableOn (kernel u) D μ)
    (hsets : ∀ A ∈ patterns base target, MeasurableSet {x | rows x = A}) (v : target) :
    IntegrableOn (movingPiece base target rows kernel v) D μ := by
  exact integrable_finsetSum Finset.univ
    (fun A _ => patternPiece_integrable μ D base target rows kernel hkernel hsets A v)

/-- Exact identity for the unchanged physical integral, indexed by the rows
at one common sample.  Only finite sums and actual kernel transport occur. -/
theorem exact_integral_identity (μ : Measure Parameter) (D : Set Parameter)
    (hD : MeasurableSet D) (base target : Finset Row)
    (rows : Parameter → Finset Row) (kernel : Row → Parameter → ℂ)
    (hkernel : ∀ u ∈ base, IntegrableOn (kernel u) D μ)
    (hsets : ∀ A ∈ patterns base target, MeasurableSet {x | rows x = A})
    (hrows : ∀ x ∈ D, rows x ⊆ base)
    (hcard : ∀ x ∈ D, (rows x).card ≤ target.card) :
    (∑ v : target, ∫ x in D, movingPiece base target rows kernel v x ∂μ) =
      ∫ x in D, ∑ u ∈ rows x, kernel u x ∂μ := by
  rw [← integral_finsetSum Finset.univ
    (fun v _ => movingPiece_integrable μ D base target rows kernel hkernel hsets v)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD] with x hx
  exact sum_movingPiece base target rows kernel x (mem_patterns.mpr ⟨hrows x hx, hcard x hx⟩)

/-- The transport does not multiply the analytic row bound by the number of
finite row patterns: each target row receives at most one summand at a time. -/
theorem norm_integrated_piece_le (μ : Measure Parameter) (D : Set Parameter)
    (hD : MeasurableSet D) (base target : Finset Row)
    (rows : Parameter → Finset Row) (kernel : Row → Parameter → ℂ)
    (hkernel : ∀ u ∈ base, IntegrableOn (kernel u) D μ)
    (hsets : ∀ A ∈ patterns base target, MeasurableSet {x | rows x = A})
    (hrows : ∀ x ∈ D, rows x ⊆ base)
    (hcard : ∀ x ∈ D, (rows x).card ≤ target.card)
    (g : Parameter → ℝ) (hg : IntegrableOn g D μ)
    (hg0 : ∀ x ∈ D, 0 ≤ g x)
    (hbound : ∀ x ∈ D, ∀ u ∈ rows x, ‖kernel u x‖ ≤ g x) (v : target) :
    ‖∫ x in D, movingPiece base target rows kernel v x ∂μ‖ ≤ ∫ x in D, g x ∂μ := by
  have hm : ∀ᵐ x ∂μ.restrict D,
      ‖movingPiece base target rows kernel v x‖ ≤ g x := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact movingPiece_norm_le base target rows kernel x
      (mem_patterns.mpr ⟨hrows x hx, hcard x hx⟩) (g x) (hg0 x hx) (hbound x hx) v
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae
      (movingPiece_integrable μ D base target rows kernel hkernel hsets v).norm hg hm)

end Measurability

end Expansion.CommonSampleTransport
