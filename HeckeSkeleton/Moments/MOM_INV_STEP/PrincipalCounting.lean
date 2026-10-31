module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers

/-!
# Counting the actual square-product cube pairs

A pair b₁ b₂=q² is encoded by q and the divisor b₁ of q². Both bᵢ have
norm at most H, so q does too. The existing linear ideal count and divisor
epsilon estimate give O(H^(1+ε)), with constants selected before the
source set. No square-pair counting assumption is introduced.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.PrincipalCounting

open NumberField IsDedekindDomain
open DedekindZetaZeroFree.LargeSieve FixedTripleFibers
open scoped Classical BigOperators NumberField

variable (K : Type*) [Field K] [NumberField K]

def squarePairs (B : Finset (Ideal (𝓞 K))) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  (B ×ˢ B).filter fun x => ∃ q : Ideal (𝓞 K), q ^ 2 = x.1 * x.2

def squareRoot (B : Finset (Ideal (𝓞 K))) (x : squarePairs K B) : Ideal (𝓞 K) :=
  Classical.choose (Finset.mem_filter.mp x.property).2

theorem squareRoot_sq (B : Finset (Ideal (𝓞 K))) (x : squarePairs K B) :
    squareRoot K B x ^ 2 = x.val.1 * x.val.2 :=
  Classical.choose_spec (Finset.mem_filter.mp x.property).2

theorem squareRoot_ne_zero (B : Finset (Ideal (𝓞 K)))
    (hB : ∀ I ∈ B, I ≠ 0) (x : squarePairs K B) : squareRoot K B x ≠ 0 := by
  have hx := Finset.mem_product.mp (Finset.mem_filter.mp x.property).1
  have hp : x.val.1 * x.val.2 ≠ 0 := mul_ne_zero (hB _ hx.1) (hB _ hx.2)
  intro h
  rw [← squareRoot_sq K B x, h, zero_pow (by decide : 2 ≠ 0)] at hp
  exact hp rfl

theorem squareRoot_norm_le (B : Finset (Ideal (𝓞 K))) (H : ℝ)
    (hH : 0 ≤ H) (hB : ∀ I ∈ B, (Ideal.absNorm I : ℝ) ≤ H)
    (x : squarePairs K B) : (Ideal.absNorm (squareRoot K B x) : ℝ) ≤ H := by
  have hx := Finset.mem_product.mp (Finset.mem_filter.mp x.property).1
  have he := congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ))
    (squareRoot_sq K B x)
  simp only [map_pow, map_mul, Nat.cast_pow, Nat.cast_mul] at he
  have hb := mul_le_mul (hB _ hx.1) (hB _ hx.2) (Nat.cast_nonneg _) hH
  have hq : 0 ≤ (Ideal.absNorm (squareRoot K B x) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- An injective encoding into actual roots and their actual divisors. -/
theorem squarePairs_card_le (B : Finset (Ideal (𝓞 K))) (H : ℝ)
    (hH : 0 ≤ H) (hB0 : ∀ I ∈ B, I ≠ 0)
    (hB : ∀ I ∈ B, (Ideal.absNorm I : ℝ) ≤ H) :
    (squarePairs K B).card ≤
      ∑ q ∈ boundedNormIdeals K H, (idealDivisors (q ^ 2)).card := by
  let T := Σ q : boundedNormIdeals K H, idealDivisors (q.val ^ 2)
  let encode (x : squarePairs K B) : T :=
    ⟨⟨squareRoot K B x, mem_boundedNormIdeals.mpr (squareRoot_norm_le K B H hH hB x)⟩,
      ⟨x.val.1, (mem_idealDivisors (pow_ne_zero 2 (squareRoot_ne_zero K B hB0 x))).mpr
        (by rw [squareRoot_sq]; exact dvd_mul_right _ _)⟩⟩
  have hinj : Function.Injective encode := by
    intro x y he
    have hq : squareRoot K B x = squareRoot K B y :=
      congrArg (fun a : T => a.1.val) he
    have hleft : x.val.1 = y.val.1 := congrArg (fun a : T => a.2.val) he
    apply Subtype.ext
    apply Prod.ext hleft
    apply mul_left_cancel₀ (hB0 x.val.1
      (Finset.mem_product.mp (Finset.mem_filter.mp x.property).1).1)
    calc
      x.val.1 * x.val.2 = squareRoot K B x ^ 2 := (squareRoot_sq K B x).symm
      _ = squareRoot K B y ^ 2 := congrArg (fun I => I ^ 2) hq
      _ = x.val.1 * y.val.2 := by rw [squareRoot_sq, hleft]
  have hc := Fintype.card_le_of_injective encode hinj
  simp only [T, Fintype.card_sigma, Fintype.card_coe] at hc
  rw [Finset.sum_coe_sort (boundedNormIdeals K H)
    (fun q : Ideal (𝓞 K) => (idealDivisors (q ^ 2)).card)] at hc
  exact hc

/-- The principal cube-pair count has one norm exponent, not two. -/
theorem exists_squarePairs_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B : Finset (Ideal (𝓞 K))) (H : ℝ),
      1 ≤ H → (∀ I ∈ B, I ≠ 0) →
      (∀ I ∈ B, (Ideal.absNorm I : ℝ) ≤ H) →
      ((squarePairs K B).card : ℝ) ≤ C * H ^ (1 + ε) := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_count_bound K
  obtain ⟨D, hD, hdiv⟩ := exists_divisor_power_bound (K := K) 1 (by decide)
    (ε / 2) (by positivity)
  refine ⟨A * D, one_le_mul_of_one_le_of_one_le hA hD, ?_⟩
  intro B H hH hB0 hB
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hpoint (q : Ideal (𝓞 K)) (hq : q ∈ boundedNormIdeals K H) :
      ((idealDivisors (q ^ 2)).card : ℝ) ≤ D * H ^ ε := by
    have hd := hdiv (q ^ 2)
    simp only [pow_one, map_pow, Nat.cast_pow] at hd
    have hp : ((Ideal.absNorm q : ℝ) ^ 2) ^ (ε / 2) =
        (Ideal.absNorm q : ℝ) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      ring
    rw [hp] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (mem_boundedNormIdeals.mp hq) hε.le) hD0)
  calc
    _ ≤ ∑ q ∈ boundedNormIdeals K H, ((idealDivisors (q ^ 2)).card : ℝ) := by
      exact_mod_cast squarePairs_card_le K B H hHpos.le hB0 hB
    _ ≤ ∑ _q ∈ boundedNormIdeals K H, D * H ^ ε := Finset.sum_le_sum hpoint
    _ = ((boundedNormIdeals K H).card : ℝ) * (D * H ^ ε) := by simp
    _ ≤ (A * H) * (D * H ^ ε) :=
      mul_le_mul_of_nonneg_right (hcount H hH)
        (mul_nonneg hD0 (Real.rpow_nonneg hHpos.le _))
    _ = (A * D) * H ^ (1 + ε) := by
      rw [Real.rpow_add hHpos, Real.rpow_one]
      ring

/-- The surviving first principal sum has one column count and one
cube-root count. The pointwise coefficient bound can contain the actual
test values and original divisor/mark losses. -/
theorem exists_principal_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B N : Finset (Ideal (𝓞 K))) (H X U : ℝ)
      (a : Ideal (𝓞 K) → Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ),
      1 ≤ H → 1 ≤ X → 0 ≤ U →
      (∀ I ∈ B, I ≠ 0) →
      (∀ I ∈ B, (Ideal.absNorm I : ℝ) ≤ H) →
      (∀ I ∈ N, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ n ∈ N, ∀ b ∈ squarePairs K B, ‖a n b‖ ≤ U) →
      ‖∑ n ∈ N, ∑ b ∈ squarePairs K B, a n b‖ ≤ C * X * H ^ (1 + ε) * U := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_count_bound K
  obtain ⟨D, hD, hpairs⟩ := exists_squarePairs_bound K ε hε
  refine ⟨A * D, one_le_mul_of_one_le_of_one_le hA hD, ?_⟩
  intro B N H X U a hH hX hU hB0 hB hN ha
  have hNcard : (N.card : ℝ) ≤ A * X := by
    apply le_trans _ (hcount X hX)
    exact_mod_cast Finset.card_le_card (show N ⊆ boundedNormIdeals K X from by
      intro I hI
      exact mem_boundedNormIdeals.mpr (hN I hI))
  have hsum (n : Ideal (𝓞 K)) (hn : n ∈ N) :
      ‖∑ b ∈ squarePairs K B, a n b‖ ≤ ((squarePairs K B).card : ℝ) * U := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _b ∈ squarePairs K B, U := Finset.sum_le_sum (ha n hn)
      _ = _ := by simp
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  calc
    _ ≤ ∑ n ∈ N, ‖∑ b ∈ squarePairs K B, a n b‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ N, ((squarePairs K B).card : ℝ) * U := Finset.sum_le_sum hsum
    _ = (N.card : ℝ) * ((squarePairs K B).card : ℝ) * U := by simp [mul_assoc]
    _ ≤ (A * X) * (D * H ^ (1 + ε)) * U := by
      apply mul_le_mul_of_nonneg_right _ hU
      exact mul_le_mul hNcard (hpairs B H hH hB0 hB) (Nat.cast_nonneg _)
        (mul_nonneg (le_trans zero_le_one hA) hX0)
    _ = (A * D) * X * H ^ (1 + ε) * U := by ring

end HeckeSkeleton.Moments.MOMInvStep.PrincipalCounting

end
