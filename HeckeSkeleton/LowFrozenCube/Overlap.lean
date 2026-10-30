import HeckeSkeleton.LowFrozenCube.FrozenReduction

/-!
# Whole-index overlap vanishing from the actual sextic symbol

The primal mark tests divisibility of the complete summation index, not one
chosen cube slot. A shared marked prime makes the symbol vanish by its sixth
power law. The reflected mixed phases also vanish on each actual collision.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace PrimeCoordinates

variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def idealWholeIndexMark {σ : Type*} (slots : Finset σ) (prime : σ → ι) (a : A) : ℂ :=
  wholeIndexMark slots prime (valuation coords a)

theorem not_coprime_of_shared_prime (a b : A) (p : ι)
    (ha : valuation coords a p ≠ 0) (hb : valuation coords b p ≠ 0) :
    ¬ Coprime coords a b := by
  intro h
  exact (h p).elim ha hb

theorem not_coprime_iff_shared_prime (a b : A) :
    ¬ Coprime coords a b ↔ ∃ p, valuation coords a p ≠ 0 ∧ valuation coords b p ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    apply h
    intro p
    by_cases ha : valuation coords a p = 0
    · exact Or.inl ha
    · right
      by_contra hb
      exact hn ⟨p, ha, hb⟩
  · rintro ⟨p, ha, hb⟩
    exact not_coprime_of_shared_prime coords a b p ha hb

/-- Overlap is killed before reflection, for arbitrary complete indices and
possibly repeated marked slots. The zero-symbol rule is derived from `h6`. -/
theorem wholeIndex_overlap_zero {σ : Type*}
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (row : A) (slots : Finset σ) (prime : σ → ι)
    (i : σ) (hi : i ∈ slots) (hrow : valuation coords row (prime i) ≠ 0)
    (a : A) : chi row a * idealWholeIndexMark coords slots prime a = 0 := by
  by_cases ha : valuation coords a (prime i) = 0
  · have hm : idealWholeIndexMark coords slots prime a = 0 := by
      unfold idealWholeIndexMark wholeIndexMark
      apply Finset.prod_eq_zero hi
      simp [ha]
    rw [hm, mul_zero]
  · rw [symbol_zero_of_shared_prime coords chi h6 row a (prime i) hrow ha, zero_mul]

theorem primal_marked_sum_overlap_zero {σ κ : Type*}
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (row : A) (slots : Finset σ) (prime : σ → ι)
    (i : σ) (hi : i ∈ slots) (hrow : valuation coords row (prime i) ≠ 0)
    (indices : Finset κ) (index : κ → A) (weight : κ → ℂ) :
    (∑ a ∈ indices, weight a * chi row (index a) *
      idealWholeIndexMark coords slots prime (index a)) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  rw [mul_assoc, wholeIndex_overlap_zero coords chi h6 row slots prime i hi hrow,
    mul_zero]

end PrimeCoordinates

namespace FrozenReduction.Data

variable (D : FrozenReduction.Data ι A)

theorem mixedPhase_row_overlap_zero (d P c n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hd : PrimeCoordinates.valuation D.coords d p ≠ 0) :
    D.mixedPhase d P c n = 0 := by
  have hn := PrimeCoordinates.not_coprime_of_shared_prime D.coords P d p hP hd
  rw [D.mixedPhase_eq]
  simp [hn]

theorem mixedPhase_column_overlap_zero (d P c n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hc : PrimeCoordinates.valuation D.coords c p ≠ 0) :
    D.mixedPhase d P c n = 0 := by
  have hz := PrimeCoordinates.symbol_zero_of_shared_prime D.coords D.symbol
    D.sixth P c p hP hc
  simp [mixedPhase, hz]

theorem mixedPhase_cube_overlap_zero (d P c n : A)
    (hn : ¬ PrimeCoordinates.Coprime D.coords P n) :
    D.mixedPhase d P c n = 0 := by
  simp [mixedPhase, hn]

theorem sourceTerm_row_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hd : PrimeCoordinates.valuation D.coords d p ≠ 0) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
  simp [sourceTerm, D.mixedPhase_row_overlap_zero d P c n p hP hd]

theorem sourceTerm_column_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hc : PrimeCoordinates.valuation D.coords c p ≠ 0) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
  simp [sourceTerm, D.mixedPhase_column_overlap_zero d P c n p hP hc]

/-- The full cube, not just its complementary part, has the correct zero
mask because canonical freezing forces the supported factor away from P. -/
theorem sourceTerm_fullCube_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) (hx : D.CanonicalCube x)
    (hcollision : ¬ PrimeCoordinates.Coprime D.coords P (x * n)) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
  have hn : ¬ PrimeCoordinates.Coprime D.coords P n := by
    intro hn
    exact hcollision ((PrimeCoordinates.coprime_fullCube D.coords D.support P x n
      hP (D.canonical_supported x hx)).mpr hn)
  simp [sourceTerm, D.mixedPhase_cube_overlap_zero d P c n hn]

end FrozenReduction.Data

end

end HeckeSkeleton.LowFrozenCube
