import HeckeSkeleton.HighBinSupport.HighNormFormSlots
/-!
Repeated-prime compensation is paid for by the conductor deficit.

At a repeated row prime the normalized compensated local factor is only
O(q^(a+6e)).  After the q^(z-1) weight this exceeds the regular slot scale
q^(z-1/2) by q^lambda, where lambda=a-1/2+6e.  The product of these extra
factors is bounded by (N/rad(N))^lambda.  The following theorems prove this
joint allocation without discarding the radical-to-row norm ratio.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- Selected primes occur at least twice; all other support primes occur
at least once.  Their product times the radical is bounded by the full
row norm.  Distinctness is encoded by the finite sets. -/
theorem selected_repeated_product_mul_radical_le {ι : Type*} [DecidableEq ι]
    (support selected : Finset ι) (Q : ι → ℝ) (multiplicity : ι → ℕ)
    (hselected : selected ⊆ support)
    (hQ : ∀ i ∈ support, 1 ≤ Q i)
    (hm : ∀ i ∈ support, 1 ≤ multiplicity i)
    (hrepeated : ∀ i ∈ selected, 2 ≤ multiplicity i) :
    (∏ i ∈ selected, Q i) * (∏ i ∈ support, Q i) ≤
      ∏ i ∈ support, Q i ^ multiplicity i := by
  have hid : (∏ i ∈ support, if i ∈ selected then Q i else 1) =
      ∏ i ∈ selected, Q i := by
    calc
      _ = ∏ i ∈ selected, if i ∈ selected then Q i else 1 := by
        symm
        exact Finset.prod_subset hselected (by intro i hi hnot; simp [hnot])
      _ = _ := Finset.prod_congr rfl (by intro i hi; simp [hi])
  rw [← hid, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i hi
    have hqi := hQ i hi
    split_ifs <;> positivity
  · intro i hi
    by_cases hs : i ∈ selected
    · simp only [if_pos hs]
      calc
        Q i * Q i = Q i ^ 2 := by ring
        _ ≤ Q i ^ multiplicity i := pow_le_pow_right₀ (hQ i hi) (hrepeated i hs)
    · simp only [if_neg hs, one_mul]
      simpa only [pow_one] using pow_le_pow_right₀ (hQ i hi) (hm i hi)

/-- Exact absorption with the residual positive power of the conductor
ratio retained.  This is stronger than merely bounding by one. -/
theorem repeated_factor_absorbed_with_surplus (N R M lam eta : ℝ)
    (hN : 0 < N) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hMN : M * R ≤ N) (hlam : 0 ≤ lam)
    (hRpos : 0 < R) :
    M ^ lam * (R / N) ^ (lam + eta) ≤ (R / N) ^ eta := by
  have hratio : 0 < R / N := div_pos hRpos hN
  have hprod : 0 ≤ M * (R / N) := mul_nonneg hM hratio.le
  have hprod_le : M * (R / N) ≤ 1 := by
    have hh : (M * R) / N ≤ 1 := (div_le_one hN).mpr hMN
    simpa only [mul_div_assoc] using hh
  rw [Real.rpow_add hratio]
  calc
    M ^ lam * ((R / N) ^ lam * (R / N) ^ eta) =
        (M * (R / N)) ^ lam * (R / N) ^ eta := by
      rw [Real.mul_rpow hM hratio.le]
      ring
    _ ≤ 1 * (R / N) ^ eta := mul_le_mul_of_nonneg_right
      (Real.rpow_le_one hprod hprod_le hlam) (Real.rpow_nonneg hratio.le _)
    _ = _ := one_mul _

/-- The remaining ratio is at most one when its exponent is nonnegative. -/
theorem repeated_factor_absorbed (N R M lam eta : ℝ)
    (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) (hM : 0 ≤ M)
    (hMN : M * R ≤ N) (hlam : 0 ≤ lam) (heta : 0 ≤ eta) :
    M ^ lam * (R / N) ^ (lam + eta) ≤ 1 := by
  apply (repeated_factor_absorbed_with_surplus N R M lam eta
    hN hR.le hM hMN hlam hR).trans
  exact Real.rpow_le_one (div_nonneg hR.le hN.le)
    ((div_le_one hN).mpr hRN) heta

/-- Loss-free joint allocation for an actual finite valuation table. -/
theorem repeated_table_absorbed {ι : Type*} [DecidableEq ι]
    (support selected : Finset ι) (Q : ι → ℝ) (multiplicity : ι → ℕ)
    (hselected : selected ⊆ support)
    (hQ : ∀ i ∈ support, 1 ≤ Q i)
    (hm : ∀ i ∈ support, 1 ≤ multiplicity i)
    (hrepeated : ∀ i ∈ selected, 2 ≤ multiplicity i)
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta) :
    (∏ i ∈ selected, Q i) ^ lam *
      ((∏ i ∈ support, Q i) / (∏ i ∈ support, Q i ^ multiplicity i)) ^ (lam + eta) ≤ 1 := by
  have hqpos : ∀ i ∈ support, 0 < Q i := fun i hi => zero_lt_one.trans_le (hQ i hi)
  have hN : 0 < ∏ i ∈ support, Q i ^ multiplicity i :=
    Finset.prod_pos (fun i hi => pow_pos (hqpos i hi) _)
  have hR : 0 < ∏ i ∈ support, Q i := Finset.prod_pos hqpos
  have hM : 0 ≤ ∏ i ∈ selected, Q i :=
    Finset.prod_nonneg (fun i hi => (hqpos i (hselected hi)).le)
  have hRN : (∏ i ∈ support, Q i) ≤ ∏ i ∈ support, Q i ^ multiplicity i := by
    apply Finset.prod_le_prod₀ (fun i hi => (hqpos i hi).le)
    intro i hi
    simpa only [pow_one] using pow_le_pow_right₀ (hQ i hi) (hm i hi)
  exact repeated_factor_absorbed _ _ _ lam eta hN hR hRN hM
    (selected_repeated_product_mul_radical_le support selected Q multiplicity
      hselected hQ hm hrepeated) hlam heta

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.selected_repeated_product_mul_radical_le
#print axioms HighBinVerified.NormForm.repeated_factor_absorbed
#print axioms HighBinVerified.NormForm.repeated_table_absorbed
