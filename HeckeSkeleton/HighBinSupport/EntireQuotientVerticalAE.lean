import HeckeSkeleton.HighBinSupport.EntireVerticalZeros
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Initial equality of quotients and vertical almost-everywhere equality

Quotients of entire functions that agree on a nonempty complex open set
agree almost everywhere on every product of vertical real lines. An
identically-zero denominator is handled using Lean's actual division by
zero convention. Nonzero denominators are not supplied as assumptions:
their almost-everywhere nonvanishing follows from `EntireVerticalZeros`.

This is an analytic comparison lemma. Its initial equality still has to
be proved from the actual arithmetic calibration before it can be used
for a physical Euler product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open Set Filter MeasureTheory Complex
open scoped Classical Topology

private theorem entire_eq_of_eqOn_open {f g : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    {U : Set (ℂ × ℂ × ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (heq : EqOn f g U) : f = g := by
  obtain ⟨v, hv⟩ := hne
  exact hf.eq_of_eventuallyEq hg
    (Filter.mem_of_superset (hU.mem_nhds hv) fun x hx => heq hx)

private theorem entire_exists_ne_zero_mem_open {f : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {v : ℂ × ℂ × ℂ} (hv : f v ≠ 0)
    {U : Set (ℂ × ℂ × ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, f x ≠ 0 := by
  by_contra h
  have hzero : EqOn f (fun _ => 0) U := by
    intro x hx
    by_contra hfx
    exact h ⟨x, hx, hfx⟩
  exact hv (congrFun
    (entire_eq_of_eqOn_open hf analyticOnNhd_const hU hne hzero) v)

private theorem entire_div_zero_of_eqOn_open {n d : (ℂ × ℂ × ℂ) → ℂ}
    (hn : AnalyticOnNhd ℂ n univ) (hd : AnalyticOnNhd ℂ d univ)
    {U : Set (ℂ × ℂ × ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hzero : EqOn (fun x => n x / d x) (fun _ => 0) U) :
    ∀ x, n x / d x = 0 := by
  by_cases hd0 : ∀ x, d x = 0
  · intro x
    simp only [hd0 x, div_zero]
  · obtain ⟨v, hv⟩ := not_forall.mp hd0
    have hdopen : IsOpen {x | d x ≠ 0} :=
      (isClosed_eq (continuousOn_univ.mp hd.continuousOn)
        continuous_const).isOpen_compl
    obtain ⟨w, hwU, hwd⟩ := entire_exists_ne_zero_mem_open hd hv hU hne
    have hnzero : EqOn n (fun _ => 0) (U ∩ {x | d x ≠ 0}) := by
      intro x hx
      exact (div_eq_zero_iff.mp (hzero hx.1)).resolve_right hx.2
    have hn0 := entire_eq_of_eqOn_open hn analyticOnNhd_const
      (hU.inter hdopen) ⟨w, hwU, hwd⟩ hnzero
    intro x
    rw [congrFun hn0 x, zero_div]

/-- Initial equality on an actual nonempty complex open set determines
the quotient on every vertical real parameter space up to a null set.
The zero-denominator alternatives are proved internally, including the
case where a complete table is the zero function. -/
theorem entire_quotients_ae_eq_vertical
    {n₁ d₁ n₂ d₂ : (ℂ × ℂ × ℂ) → ℂ}
    (hn₁ : AnalyticOnNhd ℂ n₁ univ) (hd₁ : AnalyticOnNhd ℂ d₁ univ)
    (hn₂ : AnalyticOnNhd ℂ n₂ univ) (hd₂ : AnalyticOnNhd ℂ d₂ univ)
    {U : Set (ℂ × ℂ × ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (heq : EqOn (fun x => n₁ x / d₁ x) (fun x => n₂ x / d₂ x) U)
    (σ : ℝ × ℝ × ℝ) :
    ∀ᵐ t : ℝ × (ℝ × ℝ),
      n₁ ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) /
        d₁ ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) =
      n₂ ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) /
        d₂ ((σ.1 : ℂ) + (t.1 : ℂ) * I,
          (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
          (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I) := by
  let line : (ℝ × (ℝ × ℝ)) → (ℂ × ℂ × ℂ) := fun t =>
    ((σ.1 : ℂ) + (t.1 : ℂ) * I,
      (σ.2.1 : ℂ) + (t.2.1 : ℂ) * I,
      (σ.2.2 : ℂ) + (t.2.2 : ℂ) * I)
  change ∀ᵐ t : ℝ × (ℝ × ℝ), n₁ (line t) / d₁ (line t) =
    n₂ (line t) / d₂ (line t)
  by_cases h₁0 : ∀ x, d₁ x = 0
  · have h₂0U : EqOn (fun x => n₂ x / d₂ x) (fun _ => 0) U := by
      intro x hx
      simpa only [h₁0 x, div_zero] using (heq hx).symm
    have h₂0 := entire_div_zero_of_eqOn_open hn₂ hd₂ hU hne h₂0U
    exact Eventually.of_forall fun t => by
      rw [h₁0 (line t), div_zero, h₂0 (line t)]
  by_cases h₂0 : ∀ x, d₂ x = 0
  · have h₁0U : EqOn (fun x => n₁ x / d₁ x) (fun _ => 0) U := by
      intro x hx
      simpa only [h₂0 x, div_zero] using heq hx
    have h₁0' := entire_div_zero_of_eqOn_open hn₁ hd₁ hU hne h₁0U
    exact Eventually.of_forall fun t => by
      rw [h₁0' (line t), h₂0 (line t), div_zero]
  obtain ⟨v₁, hv₁⟩ := not_forall.mp h₁0
  obtain ⟨v₂, hv₂⟩ := not_forall.mp h₂0
  have hd₁open : IsOpen {x | d₁ x ≠ 0} :=
    (isClosed_eq (continuousOn_univ.mp hd₁.continuousOn)
      continuous_const).isOpen_compl
  have hd₂open : IsOpen {x | d₂ x ≠ 0} :=
    (isClosed_eq (continuousOn_univ.mp hd₂.continuousOn)
      continuous_const).isOpen_compl
  obtain ⟨a, haU, ha⟩ := entire_exists_ne_zero_mem_open hd₁ hv₁ hU hne
  obtain ⟨b, hb, hb₂⟩ := entire_exists_ne_zero_mem_open hd₂ hv₂
    (hU.inter hd₁open) ⟨a, haU, ha⟩
  have hcrossU : EqOn (fun x => n₁ x * d₂ x) (fun x => n₂ x * d₁ x)
      ((U ∩ {x | d₁ x ≠ 0}) ∩ {x | d₂ x ≠ 0}) := by
    intro x hx
    exact (div_eq_div_iff hx.1.2 hx.2).mp (heq hx.1.1)
  have hcross := entire_eq_of_eqOn_open (hn₁.mul hd₂) (hn₂.mul hd₁)
    ((hU.inter hd₁open).inter hd₂open) ⟨b, hb, hb₂⟩ hcrossU
  filter_upwards [entire_triple_ne_zero_ae_vertical hd₁ hv₁ σ,
    entire_triple_ne_zero_ae_vertical hd₂ hv₂ σ] with t ht₁ ht₂
  exact (div_eq_div_iff ht₁ ht₂).mpr (congrFun hcross (line t))

#print axioms entire_quotients_ae_eq_vertical

end HeckeSkeleton.HighBinContinuation
