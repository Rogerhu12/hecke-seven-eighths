import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact hybrid extraction while preserving the original row

The two moving masks are expanded in divisors `D | k,P` and `r | k,c`.
Only the column and common factor are reindexed: `P = D P'`, `c = r c'`.
The quadratic row remains `k`. Consequently no quotient row, coprimality
of `D,r`, or extra row-character factor is needed by the weighted proof.
-/

namespace HeckeSkeleton.LowEnergy.KeepOriginalRow

open NumberField Ideal
open scoped BigOperators NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def mask (I J : Ideal (𝓞 K)) : ℂ := if IsCoprime I J then 1 else 0

theorem mask_mul_right (I J L : Ideal (𝓞 K)) :
    mask I (J * L) = mask I J * mask I L := by
  unfold mask
  rw [IsCoprime.mul_right_iff]
  by_cases hJ : IsCoprime I J <;> by_cases hL : IsCoprime I L <;> simp [hJ, hL]

theorem mask_mul_left (I J L : Ideal (𝓞 K)) :
    mask (I * J) L = mask I L * mask J L := by
  unfold mask
  rw [IsCoprime.mul_left_iff]
  by_cases hI : IsCoprime I L <;> by_cases hJ : IsCoprime J L <;> simp [hI, hJ]

theorem mask_norm_le (I J : Ideal (𝓞 K)) : ‖mask I J‖ ≤ 1 := by
  unfold mask
  split_ifs <;> simp

theorem normalized_product_coefficient (D P : Ideal (𝓞 K)) (a : ℂ) :
    a / (Real.sqrt (Ideal.absNorm (D * P) : ℝ) : ℂ) =
      (1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)) *
        (a / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The common factor of `n,b` can leave the cubic collision mask only
after its zero contribution has been checked. -/
theorem cubic_column_mask
    (Ext : Ideal (𝓞 K) → Prop) (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hzero : ∀ P n, Ext P → Ext n → ¬ IsCoprime P n → cubic P n = 0)
    (P n b c m h t : Ideal (𝓞 K)) (hP : Ext P) (hnExt : Ext n)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    cubic P n * mask P b = cubic P n * mask P (h * t) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [mask, he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [hzero P n hP hnExt hPn]
    simp

/-- Exact extraction of the `D,r` column factors, with the original row
`k` on both sides. The inputs are only multiplicativity, the cubic zero
law, and the local quadratic square-mask identity. -/
theorem keep_row_extracted_term
    (Ext : Ideal (𝓞 K) → Prop)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hmul_left : ∀ D P n, cubic (D * P) n = cubic D n * cubic P n)
    (hmul_right : ∀ P n m, Ext P → cubic P (n * m) = cubic P n * cubic P m)
    (hzero : ∀ P n, Ext P → Ext n → ¬ IsCoprime P n → cubic P n = 0)
    (k D P r c m h t n b : Ideal (𝓞 K)) (hP : Ext P) (hnExt : Ext n)
    (hn : n = (r * c) * m) (hb : b = ((r * c) * h) * t ^ 2)
    (hsq : quad k (n * b) = mask k ((r * c) * t) * quad k (m * h))
    (a beta : ℂ) :
    a / (Real.sqrt (Ideal.absNorm (D * P) : ℝ) : ℂ) * beta *
        quad k (n * b) * cubic (D * P) n * mask (D * P) b =
      (1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)) *
        mask k t * mask k (r * c) * quad k (m * h) *
        (beta * cubic D n * mask D b) *
        ((a * cubic P r * mask P (h * t)) /
          (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) * cubic P (c * m) := by
  have hmask := cubic_column_mask Ext cubic hzero P n b (r * c) m h t hP hnExt hn hb
  have hcubic : cubic P n = cubic P r * cubic P (c * m) := by
    rw [hn, mul_assoc, hmul_right P r (c * m) hP]
  calc
    _ = (1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)) *
        (a / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) * beta *
        mask k ((r * c) * t) * quad k (m * h) * cubic D n *
        (cubic P n * mask P b) * mask D b := by
      rw [normalized_product_coefficient, hsq, hmul_left, mask_mul_left]
      ring
    _ = _ := by
      rw [hmask, hcubic, mask_mul_right]
      ring

/-- Exact simultaneous expansion of the two masks, before any Cauchy
inequality. The local Möbius formula is an algebraic identity, not an
energy hypothesis. -/
theorem double_mask_mobius
    (divisors : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
    (mu : Ideal (𝓞 K) → ℂ)
    (hmask : ∀ k n, mask k n =
      ∑ D ∈ divisors k, if D ∣ n then mu D else 0)
    (k P c : Ideal (𝓞 K)) :
    mask k P * mask k c =
      ∑ D ∈ divisors k, ∑ r ∈ divisors k,
        if D ∣ P ∧ r ∣ c then mu D * mu r else 0 := by
  rw [hmask, hmask, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hDP : D ∣ P <;> by_cases hrc : r ∣ c <;> simp [hDP, hrc]

/-- A selected quotient is used only when divisibility holds. -/
def idealQuotient (D I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  if h : D ∣ I then Classical.choose h else 1

theorem idealQuotient_mul {D I : Ideal (𝓞 K)} (h : D ∣ I) :
    D * idealQuotient D I = I := by
  rw [idealQuotient, dif_pos h]
  exact (Classical.choose_spec h).symm

def quotientSupport (D : Ideal (𝓞 K)) (s : Finset (Ideal (𝓞 K))) :
    Finset (Ideal (𝓞 K)) :=
  (s.filter (fun I => D ∣ I)).image (idealQuotient D)

theorem quotient_injective_on (D : Ideal (𝓞 K)) {I J : Ideal (𝓞 K)}
    (hI : D ∣ I) (hJ : D ∣ J) (h : idealQuotient D I = idealQuotient D J) : I = J := by
  rw [← idealQuotient_mul hI, ← idealQuotient_mul hJ, h]

theorem mem_quotientSupport (D J : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (s : Finset (Ideal (𝓞 K))) :
    J ∈ quotientSupport D s ↔ D * J ∈ s := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIs, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, idealQuotient_mul hDI]
    exact hIs
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr
      ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal (𝓞 K)) (s : Finset (Ideal (𝓞 K))) (f : Ideal (𝓞 K) → A) :
    (∑ I ∈ s with D ∣ I, f I) = ∑ J ∈ quotientSupport D s, f (D * J) := by
  classical
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact quotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

/-- Both moving column variables can be reindexed while the row is fixed. -/
theorem double_column_reindex {A : Type*} [AddCommMonoid A]
    (ps cs : Finset (Ideal (𝓞 K))) (D r : Ideal (𝓞 K))
    (f : Ideal (𝓞 K) → Ideal (𝓞 K) → A) :
    (∑ P ∈ ps, ∑ c ∈ cs, if D ∣ P ∧ r ∣ c then f P c else 0) =
      ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs, f (D * P) (r * c) := by
  classical
  calc
    _ = ∑ P ∈ ps with D ∣ P, ∑ c ∈ cs with r ∣ c, f P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases h : D ∣ P <;> simp [h]
    _ = ∑ P ∈ quotientSupport D ps, ∑ c ∈ cs with r ∣ c, f (D * P) c :=
      sum_quotientSupport D ps (fun P => ∑ c ∈ cs with r ∣ c, f P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cs (f (D * P))

#print axioms keep_row_extracted_term
#print axioms double_mask_mobius
#print axioms double_column_reindex

end
end HeckeSkeleton.LowEnergy.KeepOriginalRow
