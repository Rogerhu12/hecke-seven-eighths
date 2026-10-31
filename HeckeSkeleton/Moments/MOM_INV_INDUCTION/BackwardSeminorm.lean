import HeckeSkeleton.Moments.MOM_INV_INDUCTION.InductionGeometry
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Uniform finite seminorms by backward choice

The one-step provider accepts a prescribed finite child seminorm and then
chooses a finite parent seminorm and scalar, before any varying source.
This order is enough: a seminorm stable under every transformed test is
not required.  This file makes the finite backward choice and the strict
row-length induction together.  A node may include its base, all real
parameters, arbitrary finite prime lists, and continuous spectral data.

The successor premise has exactly the normalized implication form of
`ProviderStep.exists_uniform_normalized_step`.  Its terminal premise is
the separately proved completed-energy estimate.  There is no estimate
for an admissible nonterminal among the premises without its actual
child estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

private theorem finite_schwartz_square_mono
    (s t : Finset (ℕ × ℕ)) (hst : s ⊆ t) (W : SchwartzMap ℝ ℂ) :
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 ≤
      (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 :=
  pow_le_pow_left₀ (apply_nonneg _ _)
    (Seminorm.le_def.mp (Finset.sup_mono hst) W) 2

/-- Select the child order first and the parent order afterward at each
of finitely many levels. The final scalar and finite order are uniform
over every source node, including its base and its spectral parameters.

`Good h` retains the actual two margins and bounded length range after
`h` steps. `Child` is the provider's generation relation; it need not be
finite. The explicit rank condition ensures the last level is empty,
rather than assuming an estimate at depth zero. -/
theorem exists_backward_finite_seminorm {α : Type*}
    (E F M Z : α → ℝ) (W : α → SchwartzMap ℝ ℂ)
    (Child : α → α → Prop) (Terminal : α → Prop) (Good : ℕ → α → Prop)
    (D : ℕ) (d Mmax L : ℝ)
    (hdepth : Mmax < (D : ℝ) * d) (hL : 0 ≤ L)
    (hZ : ∀ h x, Good h x → 1 ≤ Z x)
    (hM : ∀ h x, Good h x → 0 ≤ M x)
    (hchild : ∀ h x y, h < D → Good h x → ¬ Terminal x → Child x y →
      Good (h + 1) y ∧ M y + d ≤ M x)
    (hterminal : ∃ t : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ h x, h < D → Good h x → Terminal x →
        E x ≤ C * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 * Z x ^ F x)
    (hstep : ∀ t : Finset (ℕ × ℕ), ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ h x, h < D → Good h x → ¬ Terminal x →
        ∀ B eps : ℝ, 1 ≤ B → 0 ≤ eps →
        (∀ y, Child x y →
          E y ≤ B * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W y)) ^ 2 *
            Z y ^ (F y + eps)) →
        E x ≤ (3 * C * B) *
          (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 *
            Z x ^ (F x + L + eps)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ x, Good 0 x → M x ≤ Mmax →
        E x ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 *
          Z x ^ (F x + (D : ℝ) * L) := by
  obtain ⟨t₀, C₀, hC₀, ht₀⟩ := hterminal
  have stages : ∀ n : ℕ, n ≤ D →
      ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
        ∀ h x, h + n = D → Good h x → M x + (h : ℝ) * d ≤ Mmax →
          E x ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 *
            Z x ^ (F x + (n : ℝ) * L) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨∅, 1, le_rfl, ?_⟩
      intro h x hn hx hrank
      have heq : h = D := by simpa using hn
      subst h
      have hm := hM D x hx
      exfalso
      linarith
    | succ n ih =>
      intro hn
      obtain ⟨t, B, hB, ht⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨q, C, hC, hq⟩ := hstep t
      let qstar := t₀ ∪ q
      let Cstar := max C₀ (3 * C * B)
      have hCstar : 1 ≤ Cstar := hC₀.trans (le_max_left _ _)
      refine ⟨qstar, Cstar, hCstar, ?_⟩
      intro h x hhn hx hrank
      have hh : h < D := by omega
      have hz := hZ h x hx
      have hz0 : 0 ≤ Z x := zero_le_one.trans hz
      have hpow0 : 0 ≤ Z x ^ F x := Real.rpow_nonneg hz0 _
      have hpow : Z x ^ F x ≤ Z x ^ (F x + ((n + 1 : ℕ) : ℝ) * L) :=
        Real.rpow_le_rpow_of_exponent_le hz
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hL))
      by_cases hterm : Terminal x
      · have hseminorm := finite_schwartz_square_mono t₀ qstar
          (Finset.subset_union_left) (W x)
        have hscalar :
            C₀ * (t₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 ≤
              Cstar * (qstar.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 :=
          mul_le_mul (le_max_left _ _) hseminorm (sq_nonneg _)
            (zero_le_one.trans hCstar)
        exact (ht₀ h x hh hx hterm).trans
          (mul_le_mul hscalar hpow hpow0
            (mul_nonneg (zero_le_one.trans hCstar) (sq_nonneg _)))
      · have hih : ∀ y, Child x y →
            E y ≤ B * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W y)) ^ 2 *
              Z y ^ (F y + (n : ℝ) * L) := by
          intro y hy
          obtain ⟨hgood, hdrop⟩ := hchild h x y hh hx hterm hy
          apply ht (h + 1) y (by omega) hgood
          have hcast : ((h + 1 : ℕ) : ℝ) = (h : ℝ) + 1 := by push_cast; rfl
          rw [hcast]
          linarith
        have hbound := hq h x hh hx hterm B ((n : ℝ) * L) hB
          (mul_nonneg (Nat.cast_nonneg _) hL) hih
        have hex : F x + L + (n : ℝ) * L =
            F x + ((n + 1 : ℕ) : ℝ) * L := by push_cast; ring
        rw [hex] at hbound
        have hseminorm := finite_schwartz_square_mono q qstar
          (Finset.subset_union_right) (W x)
        have hscalar :
            (3 * C * B) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 ≤
              Cstar * (qstar.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 :=
          mul_le_mul (le_max_right _ _) hseminorm (sq_nonneg _)
            (zero_le_one.trans hCstar)
        exact hbound.trans (mul_le_mul_of_nonneg_right hscalar
          (Real.rpow_nonneg hz0 _))
  obtain ⟨q, C, hC, hbound⟩ := stages D le_rfl
  refine ⟨q, C, hC, ?_⟩
  intro x hx hm
  exact hbound 0 x (by omega) hx (by simpa using hm)

/-- The allocated descent loss may be replaced by the requested
epsilon after all finite seminorm choices have been made. -/
theorem backward_bound_with_epsilon {α : Type*}
    (E F Z : α → ℝ) (W : α → SchwartzMap ℝ ℂ) (Good : α → Prop)
    (q : Finset (ℕ × ℕ)) {C loss eps : ℝ}
    (hC : 0 ≤ C) (hloss : loss ≤ eps)
    (hZ : ∀ x, Good x → 1 ≤ Z x)
    (hbound : ∀ x, Good x →
      E x ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 *
        Z x ^ (F x + loss)) :
    ∀ x, Good x →
      E x ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W x)) ^ 2 *
        Z x ^ (F x + eps) := by
  intro x hx
  exact (hbound x hx).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hZ x hx) (add_le_add_left hloss _))
    (mul_nonneg hC (sq_nonneg _)))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
