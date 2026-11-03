import ExpansionDetector.EulerDeletionBounds

/-! Numerator deletion on slightly negative reflected lines. The extra
power is exactly the negative real-part allowance; the factor 2 per prime
is absorbed into an arbitrary subpower, proved from finite small primes. -/
noncomputable section
namespace ExpansionDetector.EulerDeletion
open ExpansionDetector.IdealCutoff
open scoped NumberField Classical BigOperators

lemma two_le_majorant_mul_rpow (δ q : ℝ) (hδ : 0 < δ) (hq : 1 < q) :
    2 ≤ localMajorant δ q * q ^ δ := by
  have hqp := zero_lt_one.trans hq
  have hx : 1 ≤ q ^ δ := Real.one_le_rpow hq.le hδ.le
  have hxp : 0 < q ^ δ := Real.rpow_pos_of_pos hqp _
  by_cases hlarge : 2 ≤ q ^ δ
  · exact hlarge.trans (le_mul_of_one_le_left hxp.le (one_le_localMajorant hδ hq))
  · have hy : (1 / 2 : ℝ) ≤ q ^ (-δ) := by
      rw [Real.rpow_neg hqp.le]
      have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hxp).mpr (lt_of_not_ge hlarge).le
      simpa only [one_div] using h
    have hden : 0 < 1 - q ^ (-δ) :=
      sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hδ))
    have hm : 2 ≤ localMajorant δ q := by
      rw [localMajorant, ← one_div]
      apply (le_div_iff₀ hden).mpr
      linarith
    exact hm.trans (le_mul_of_one_le_right (localMajorant_pos hδ hq).le hx)

variable {K : Type*} [Field K] [NumberField K]

theorem primeSupport_card_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ 0 →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := primeSupport_localMajorant_subpower (K := K)
    (ε / 2) (ε / 2) (by linarith) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro I hI
  have hprodNorm : (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ)) ≤ (Ideal.absNorm I : ℝ) := by
    have hd := divisor_norm_le hI (show primeSupport I ⊆ primeSupport I from fun _ h => h)
    rw [map_prod] at hd
    exact_mod_cast hd
  have hsum : (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ (ε / 2)) ≤
      (Ideal.absNorm I : ℝ) ^ (ε / 2) := by
    rw [Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _) (ε / 2)]
    exact Real.rpow_le_rpow (Finset.prod_nonneg (fun P _ => Nat.cast_nonneg _))
      hprodNorm (by linarith)
  have hNI : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  calc
    _ = ∏ P ∈ primeSupport I, (2 : ℝ) := by simp
    _ ≤ ∏ P ∈ primeSupport I,
        localMajorant (ε / 2) (Ideal.absNorm P : ℝ) * (Ideal.absNorm P : ℝ) ^ (ε / 2) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
      intro P hP
      apply two_le_majorant_mul_rpow _ _ (by linarith)
      have hn := two_le_norm_of_prime (support_prime hP)
      have hn' : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast hn
      linarith
    _ = (∏ P ∈ primeSupport I, localMajorant (ε / 2) (Ideal.absNorm P : ℝ)) *
        (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ (ε / 2)) := Finset.prod_mul_distrib
    _ ≤ (C * (Ideal.absNorm I : ℝ) ^ (ε / 2)) * (Ideal.absNorm I : ℝ) ^ (ε / 2) :=
      mul_le_mul (hb I hI) hsum
        (Finset.prod_nonneg (fun P _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hNI]
      congr 2
      ring

theorem localEuler_negative_norm_bound (η q : ℝ) (hη : 0 ≤ η) (hq : 1 ≤ q)
    (a s : ℂ) (ha : ‖a‖ ≤ 1) (hs : -η ≤ s.re) :
    ‖1 - a * (q : ℂ) ^ (-s)‖ ≤ 2 * q ^ η := by
  have hqp := zero_lt_one.trans_le hq
  have hp : 1 ≤ q ^ η := Real.one_le_rpow hq hη
  have hterm : ‖a * (q : ℂ) ^ (-s)‖ ≤ q ^ η := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hqp, Complex.neg_re]
    calc
      _ ≤ 1 * q ^ (-s.re) := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hqp.le _)
      _ ≤ q ^ η := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have h := norm_sub_le (1 : ℂ) (a * (q : ℂ) ^ (-s))
  rw [norm_one] at h
  linarith

/-- The moving row deletion costs at most N(row)^(eta+epsilon) throughout
Re(s)>=-eta, uniformly in every unitary local coefficient and height. -/
theorem primeSupport_negative_deletion_subpower (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ a : Ideal (𝓞 K) → ℂ, (∀ P ∈ primeSupport I, ‖a P‖ ≤ 1) →
      ∀ s : ℂ, -η ≤ s.re →
      ‖∏ P ∈ primeSupport I, (1 - a P * (Ideal.absNorm P : ℂ) ^ (-s))‖ ≤
        C * (Ideal.absNorm I : ℝ) ^ (η + ε) := by
  obtain ⟨C, hC, hcard⟩ := primeSupport_card_subpower (K := K) ε hε
  refine ⟨C, hC, ?_⟩
  intro I hI a ha s hs
  have hNI : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hprodNorm : (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ)) ≤ (Ideal.absNorm I : ℝ) := by
    have hd := divisor_norm_le hI (show primeSupport I ⊆ primeSupport I from fun _ h => h)
    rw [map_prod] at hd
    exact_mod_cast hd
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ primeSupport I, 2 * (Ideal.absNorm P : ℝ) ^ η := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      have hn : (1 : ℝ) ≤ Ideal.absNorm P := by
        have hh := two_le_norm_of_prime (support_prime hP)
        exact_mod_cast (by omega : 1 ≤ Ideal.absNorm P)
      simpa only [Complex.ofReal_natCast] using
        localEuler_negative_norm_bound η (Ideal.absNorm P : ℝ) hη hn (a P) s (ha P hP) hs
    _ = (2 : ℝ) ^ (primeSupport I).card * (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ)) ^ η := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _) η]
    _ ≤ (C * (Ideal.absNorm I : ℝ) ^ ε) * (Ideal.absNorm I : ℝ) ^ η :=
      mul_le_mul (hcard I hI)
        (Real.rpow_le_rpow (Finset.prod_nonneg (fun P _ => Nat.cast_nonneg _)) hprodNorm hη)
        (Real.rpow_nonneg (Finset.prod_nonneg (fun P _ => Nat.cast_nonneg _)) _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hNI]
      congr 2
      ring

end ExpansionDetector.EulerDeletion
