import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Complex.Basic

/-!
Finite amplitude labels are introduced inside the already shifted integral.
A fixed label may be active at different parameters for different rows, and
the resulting fixed row sets may overlap.  The pieces retain their indicator
inside the integral, so the exact expansion is nevertheless preserved.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion

open MeasureTheory
open scoped Classical BigOperators

variable {Ω Row Label : Type*} [MeasurableSpace Ω] [Fintype Label]
variable (μ : Measure Ω) (D : Set Ω) (rows : Finset Row)
variable (code : Ω → Row → Label) (kernel : Row → Ω → ℂ)

/-- Fixed row support of one pointwise label.  Different labels need not give
disjoint supports: a row may meet several labels at different parameters. -/
def integratedRows (label : Label) : Finset Row :=
  rows.filter fun u => ∃ x ∈ D, code x u = label

omit [MeasurableSpace Ω] [Fintype Label] in
theorem integratedRows_subset (label : Label) :
    integratedRows D rows code label ⊆ rows := Finset.filter_subset _ _

omit [MeasurableSpace Ω] [Fintype Label] in
@[simp] theorem mem_integratedRows (label : Label) (u : Row) :
    u ∈ integratedRows D rows code label ↔
      u ∈ rows ∧ ∃ x ∈ D, code x u = label := by
  simp only [integratedRows, Finset.mem_filter]

def pointwisePiece (label : Label) (u : Row) (x : Ω) : ℂ :=
  if code x u = label then kernel u x else 0

def integratedPiece (label : Label) (u : Row) : ℂ :=
  ∫ x in D, pointwisePiece code kernel label u x ∂μ

omit [MeasurableSpace Ω] in
theorem sum_pointwisePiece (u : Row) (x : Ω) :
    (∑ label, pointwisePiece code kernel label u x) = kernel u x := by
  simp [pointwisePiece]

omit [Fintype Label] in
theorem pointwisePiece_integrable (label : Label) (u : Row)
    (hf : IntegrableOn (kernel u) D μ)
    (hcode : MeasurableSet {x | code x u = label}) :
    IntegrableOn (pointwisePiece code kernel label u) D μ := by
  unfold IntegrableOn at hf ⊢
  change Integrable ({x | code x u = label}.indicator (kernel u)) (μ.restrict D)
  exact hf.indicator hcode

omit [Fintype Label] in
theorem integratedPiece_eq_zero_of_not_mem (hD : MeasurableSet D)
    (label : Label) {u : Row} (hu : u ∈ rows)
    (hmiss : u ∉ integratedRows D rows code label) :
    integratedPiece μ D code kernel label u = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hD] with x hx
  have hne : code x u ≠ label := by
    intro heq
    exact hmiss ((mem_integratedRows D rows code label u).mpr ⟨hu, x, hx, heq⟩)
  simp only [pointwisePiece, hne, ite_false, Pi.zero_apply]

theorem sum_integratedPiece (u : Row)
    (hf : IntegrableOn (kernel u) D μ)
    (hcode : ∀ label, MeasurableSet {x | code x u = label}) :
    (∑ label, integratedPiece μ D code kernel label u) =
      ∫ x in D, kernel u x ∂μ := by
  unfold integratedPiece
  rw [← integral_finsetSum Finset.univ
    (fun label _ => pointwisePiece_integrable μ D code kernel label u hf (hcode label))]
  congr 1
  funext x
  exact sum_pointwisePiece code kernel u x

/-- Exact finite-label decomposition of the original fixed-row integral.
The indicator is integrated before the rowwise witness parameters are chosen. -/
theorem integrated_partition_identity (hD : MeasurableSet D)
    (hf : ∀ u ∈ rows, IntegrableOn (kernel u) D μ)
    (hcode : ∀ u ∈ rows, ∀ label, MeasurableSet {x | code x u = label}) :
    (∑ label, ∑ u ∈ integratedRows D rows code label,
      integratedPiece μ D code kernel label u) =
      ∑ u ∈ rows, ∫ x in D, kernel u x ∂μ := by
  have heq (label : Label) :
      (∑ u ∈ integratedRows D rows code label, integratedPiece μ D code kernel label u) =
        ∑ u ∈ rows, integratedPiece μ D code kernel label u := by
    apply Finset.sum_subset (integratedRows_subset D rows code label)
    intro u hu hmiss
    exact integratedPiece_eq_zero_of_not_mem μ D rows code kernel hD label hu hmiss
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact sum_integratedPiece μ D code kernel u (hf u hu) (hcode u hu)

/-- Every active row admits an actual parameter in the retained integration
domain.  Choosing this parameter adds no new discrete label. -/
def labelSample (label : Label)
    (u : {u : Row // u ∈ integratedRows D rows code label}) : Ω :=
  Classical.choose ((mem_integratedRows D rows code label u.val).mp u.property).2

omit [MeasurableSpace Ω] [Fintype Label] in
theorem labelSample_spec (label : Label)
    (u : {u : Row // u ∈ integratedRows D rows code label}) :
    labelSample D rows code label u ∈ D ∧
      code (labelSample D rows code label u) u.val = label :=
  Classical.choose_spec ((mem_integratedRows D rows code label u.val).mp u.property).2

omit [MeasurableSpace Ω] [Fintype Label] in
/-- Any simultaneous pointwise property can now be used at the chosen rowwise
parameter.  In particular one sample can retain all slot lower bounds.
This rowwise sample is not a common physical prime-profile parameter. -/
theorem labelSample_preserves (label : Label)
    (P : Ω → Row → Prop)
    (hP : ∀ x ∈ D, ∀ u ∈ rows, code x u = label → P x u)
    (u : {u : Row // u ∈ integratedRows D rows code label}) :
    P (labelSample D rows code label u) u.val := by
  have hx := labelSample_spec D rows code label u
  exact hP _ hx.1 _ ((mem_integratedRows D rows code label u.val).mp u.property).1 hx.2

omit [MeasurableSpace Ω] [Fintype Label] in
/-- All fixed supports inherit the original norm envelope. -/
theorem integratedRows_in_envelope (envelope : Finset Row)
    (hrows : rows ⊆ envelope) (label : Label) :
    integratedRows D rows code label ⊆ envelope :=
  (integratedRows_subset D rows code label).trans hrows

end Expansion
