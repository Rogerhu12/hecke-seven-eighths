import HeckeSkeleton.HighBinSupport.HighNormFormDeficit
/-!
Uniform summation of repeated-prime tuples.

The tuple cost is a fixed power of the row's prime-support cardinality,
not a row-family count.  An explicit factorial/exponential inequality
absorbs that cost into any prescribed positive row-norm power.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- Products of norm-at-least-two primes force exponential growth in
support size. -/
theorem two_pow_support_card_le {ι : Type*} (support : Finset ι)
    (Q : ι → ℝ) (m : ι → ℕ)
    (hQ : ∀ i ∈ support, 2 ≤ Q i) (hm : ∀ i ∈ support, 1 ≤ m i) :
    (2 : ℝ) ^ support.card ≤ ∏ i ∈ support, Q i ^ m i := by
  calc
    _ = ∏ _i ∈ support, (2 : ℝ) := by simp
    _ ≤ ∏ i ∈ support, Q i ^ m i := by
      apply Finset.prod_le_prod₀ (by intros; norm_num)
      intro i hi
      exact (hQ i hi).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith [hQ i hi]) (hm i hi))

/-- An explicit constant valid for every norm N≥2^n.  This controls all
choices of at most J distinct row primes, with an additional ordinary
error option in each slot. -/
theorem support_tuple_count_subpower (N : ℝ) (n J : ℕ) (eps : ℝ)
    (heps : 0 < eps) (hN : (2 : ℝ) ^ n ≤ N) :
    ((n : ℝ) + 1) ^ J ≤
      (((Nat.factorial J : ℝ) / (eps * Real.log 2) ^ J) * (2 : ℝ) ^ eps) * N ^ eps := by
  have hNpos : 0 < N := (pow_pos (by norm_num : (0 : ℝ) < 2) n).trans_le hN
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < eps * Real.log (2 : ℝ) := mul_pos heps hlog2
  have hlog : (n : ℝ) * Real.log (2 : ℝ) ≤ Real.log N := by
    have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) n) hN
    simpa only [Real.log_pow] using hh
  let x : ℝ := (eps * Real.log 2) * ((n : ℝ) + 1)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ eps * Real.log N + eps * Real.log 2 := by
    dsimp only [x]
    nlinarith
  have hfac : (0 : ℝ) < (Nat.factorial J : ℝ) := by exact_mod_cast Nat.factorial_pos J
  have hpower : x ^ J ≤ (Nat.factorial J : ℝ) * Real.exp x := by
    have hh := Real.pow_div_factorial_le_exp x hx J
    have hh' := (div_le_iff₀ hfac).mp hh
    simpa only [mul_comm] using hh'
  have hexp : Real.exp x ≤ N ^ eps * (2 : ℝ) ^ eps := by
    calc
      _ ≤ Real.exp (eps * Real.log N + eps * Real.log 2) := Real.exp_le_exp.mpr hxle
      _ = N ^ eps * (2 : ℝ) ^ eps := by
        rw [Real.exp_add, Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1 <;> congr 1 <;> ring
  have hden : 0 < (eps * Real.log (2 : ℝ)) ^ J := pow_pos hc _
  calc
    ((n : ℝ) + 1) ^ J = x ^ J / (eps * Real.log 2) ^ J := by
      dsimp only [x]
      rw [mul_pow]
      field_simp [ne_of_gt hden]
    _ ≤ ((Nat.factorial J : ℝ) * Real.exp x) / (eps * Real.log 2) ^ J :=
      div_le_div_of_nonneg_right hpower hden.le
    _ ≤ ((Nat.factorial J : ℝ) * (N ^ eps * (2 : ℝ) ^ eps)) /
        (eps * Real.log 2) ^ J :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hfac.le) hden.le
    _ = _ := by ring

/-- A complete finite sum of repeated tuples is controlled jointly with
the conductor radical.  Each tuple may choose different row primes. -/
theorem repeated_tuple_sum_bound {ι : Type*} (tuples : Finset ι)
    (term : ι → ℂ) (M : ι → ℝ) (N R C lam : ℝ)
    (hN : 0 < N) (hR : 0 ≤ R) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hM : ∀ i ∈ tuples, 0 ≤ M i)
    (hallocation : ∀ i ∈ tuples, M i * R ≤ N)
    (hterm : ∀ i ∈ tuples, ‖term i‖ ≤ C * M i ^ lam) :
    R ^ lam * ‖∑ i ∈ tuples, term i‖ ≤
      C * (tuples.card : ℝ) * N ^ lam := by
  calc
    R ^ lam * ‖∑ i ∈ tuples, term i‖ ≤ R ^ lam * ∑ i ∈ tuples, ‖term i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hR _)
    _ = ∑ i ∈ tuples, R ^ lam * ‖term i‖ := Finset.mul_sum ..
    _ ≤ ∑ _i ∈ tuples, C * N ^ lam := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        R ^ lam * ‖term i‖ ≤ R ^ lam * (C * M i ^ lam) :=
          mul_le_mul_of_nonneg_left (hterm i hi) (Real.rpow_nonneg hR _)
        _ = C * (M i * R) ^ lam := by
          rw [Real.mul_rpow (hM i hi) hR]
          ring
        _ ≤ C * N ^ lam := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_nonneg (hM i hi) hR) (hallocation i hi) hlam) hC
    _ = _ := by simp [mul_comm, mul_left_comm, mul_assoc]

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.two_pow_support_card_le
#print axioms HighBinVerified.NormForm.support_tuple_count_subpower
#print axioms HighBinVerified.NormForm.repeated_tuple_sum_bound
