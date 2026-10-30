import HeckeSkeleton.LowHybrid.Assembly
import HeckeSkeleton.LowHybrid.Normalization
import HeckeSkeleton.LowFrozenCube.Phases

/-!
# Arithmetic bounds for the exact hybrid decomposition

These lemmas supply the coefficient contractions, product-fiber counts and
injective quotient-row pullbacks used when constructing the weighted blocks.
All hypotheses concern elementary algebra or finite sets. No hybrid-energy
bound is an input.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
noncomputable section

theorem norm_sextic_le_one (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) : ‖z‖ ≤ 1 := by
  rcases hz with rfl | hz
  · simp
  · exact le_of_eq (Complex.norm_eq_one_of_pow_eq_one hz (by decide))

theorem norm_sextic_neg_two_le_one (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    ‖z ^ (-2 : ℤ)‖ ≤ 1 := by
  rw [HeckeSkeleton.LowFrozenCube.zpow_neg_two_eq_fourth z hz, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg z) (norm_sextic_le_one z hz) 4).trans_eq
    (one_pow 4)

theorem norm_symbol_le_one {I : Type*} (symbol : I → I → ℂ)
    (cop : I → I → Prop)
    (h6 : ∀ i j, symbol i j ^ 6 = if cop i j then 1 else 0) (i j : I) :
    ‖symbol i j‖ ≤ 1 := by
  apply norm_sextic_le_one
  by_cases h : cop i j
  · exact Or.inr (by simpa [h] using h6 i j)
  · apply Or.inl
    apply (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp
    simpa [h] using h6 i j

theorem norm_symbol_neg_two_le_one {I : Type*} (symbol : I → I → ℂ)
    (cop : I → I → Prop)
    (h6 : ∀ i j, symbol i j ^ 6 = if cop i j then 1 else 0) (i j : I) :
    ‖symbol i j ^ (-2 : ℤ)‖ ≤ 1 := by
  apply norm_sextic_neg_two_le_one
  by_cases h : cop i j
  · exact Or.inr (by simpa [h] using h6 i j)
  · apply Or.inl
    apply (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp
    simpa [h] using h6 i j

theorem complex_mask_norm_le_one (p : Prop) :
    ‖if p then (1 : ℂ) else 0‖ ≤ 1 := by
  by_cases h : p <;> simp [h]

theorem mul_contraction_norm (z u : ℂ) (hu : ‖u‖ ≤ 1) : ‖z * u‖ ≤ ‖z‖ := by
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg z)

theorem twisted_beta_norm_le (beta z w : ℂ) (p : Prop)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖beta * z ^ 3 * w * (if p then (1 : ℂ) else 0)‖ ≤ ‖beta‖ := by
  have hz3 : ‖z ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg z) hz 3).trans_eq (one_pow 3)
  exact (mul_contraction_norm _ _ (complex_mask_norm_le_one p)).trans
    ((mul_contraction_norm _ _ hw).trans (mul_contraction_norm beta _ hz3))

theorem twisted_column_mass_le {I : Type*}
    (ps : Finset I) (a u : I → ℂ) (normI : I → ℝ)
    (hu : ∀ p ∈ ps, ‖u p‖ ≤ 1) (hn : ∀ p ∈ ps, 0 < normI p) :
    (∑ p ∈ ps, ‖(a p / (Real.sqrt (normI p) : ℂ)) * u p‖ ^ 2) ≤
      ∑ p ∈ ps, ‖a p‖ ^ 2 / normI p := by
  apply Finset.sum_le_sum
  intro p hp
  calc
    _ ≤ ‖a p / (Real.sqrt (normI p) : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (mul_contraction_norm _ _ (hu p hp)) 2
    _ = _ := norm_div_sqrt_sq (a p) (normI p) (le_of_lt (hn p hp))

section Products

variable {I : Type*} [CancelCommMonoid I] [DecidableEq I]

/-- Both hybrid product fibers are bounded by the ordinary divisor count.
The proof uses only cancellation and the first-factor map. -/
theorem product_fiber_card_le_divisors
    (pairs : Finset (I × I)) (j : I) (divisors : Finset I)
    (hdivisors : ∀ d, d ∣ j → d ∈ divisors) :
    (pairs.filter fun x => x.1 * x.2 = j).card ≤ divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    exact hdivisors x.1 ⟨x.2, (Finset.mem_filter.mp hx).2.symm⟩
  · intro x hx y hy hxy
    apply Prod.ext hxy
    have hxprod := (Finset.mem_filter.mp hx).2
    have hyprod := (Finset.mem_filter.mp hy).2
    apply mul_left_cancel (a := x.1)
    simpa only [hxy] using hxprod.trans hyprod.symm

/-- Dividing all original rows by a fixed divisor loses no multiplicity. -/
theorem quotient_injOn (rows : Finset I) (d : I) (quotient : I → I)
    (hquotient : ∀ k ∈ rows, d * quotient k = k) :
    Set.InjOn quotient (rows : Set I) := by
  intro k hk l hl hkl
  rw [← hquotient k hk, ← hquotient l hl, hkl]

end Products

/-- Pull a positive row sum back through an injective quotient map. -/
theorem row_pullback_le {I J : Type*} [DecidableEq J]
    (rows : Finset I) (target : Finset J) (phi : I → J) (f : J → ℝ)
    (hphi : Set.InjOn phi (rows : Set I))
    (hmap : ∀ i ∈ rows, phi i ∈ target) (hf : ∀ j ∈ target, 0 ≤ f j) :
    (∑ i ∈ rows, f (phi i)) ≤ ∑ j ∈ target, f j := by
  classical
  calc
    _ = ∑ j ∈ rows.image phi, f j := (Finset.sum_image hphi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj; exact hmap i hi)
      (fun j hj _ => hf j hj)

/-- An arbitrary-coefficient sieve survives the original-to-quotient row
change without an extra divisor loss. -/
theorem operator_bound_pullback {I J P : Type*} [DecidableEq J]
    (rows : Finset I) (target : Finset J) (columns : Finset P)
    (phi : I → J) (kernel : J → P → ℂ) (Q : ℝ)
    (hphi : Set.InjOn phi (rows : Set I))
    (hmap : ∀ i ∈ rows, phi i ∈ target)
    (hbound : ∀ a : P → ℂ,
      (∑ j ∈ target, ‖∑ p ∈ columns, kernel j p * a p‖ ^ 2) ≤
        Q * ∑ p ∈ columns, ‖a p‖ ^ 2) (a : P → ℂ) :
    (∑ i ∈ rows, ‖∑ p ∈ columns, kernel (phi i) p * a p‖ ^ 2) ≤
      Q * ∑ p ∈ columns, ‖a p‖ ^ 2 :=
  (row_pullback_le rows target phi (fun j => ‖∑ p ∈ columns, kernel j p * a p‖ ^ 2)
    hphi hmap (fun _ _ => sq_nonneg _)).trans (hbound a)

/-- Multiplicative norms at least one give the quotient support bound. -/
theorem factor_norm_le_product {I : Type*} [Monoid I]
    (normI : I → ℝ) (hn : ∀ i, 1 ≤ normI i)
    (hmul : ∀ i j, normI (i * j) = normI i * normI j) (i j : I) :
    normI j ≤ normI (i * j) := by
  rw [hmul]
  nlinarith [hn i, hn j]

theorem quotient_norm_le {I : Type*} [Monoid I]
    (normI : I → ℝ) (hn : ∀ i, 1 ≤ normI i)
    (hmul : ∀ i j, normI (i * j) = normI i * normI j)
    (d q k : I) (hk : d * q = k) : normI q ≤ normI k := by
  rw [← hk]
  exact factor_norm_le_product normI hn hmul d q

#print axioms product_fiber_card_le_divisors
#print axioms operator_bound_pullback
#print axioms twisted_column_mass_le

end
end HeckeSkeleton.LowHybrid
