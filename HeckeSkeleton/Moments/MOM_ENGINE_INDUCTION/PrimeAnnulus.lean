import PrimeCancellationPairedProfiles

/-!
# Prime cancellation on any fixed positive annulus

The existing compact-family Mellin estimate and contour shift already
accept an arbitrary positive annulus.  Only the elementary prime and
prime-power counting lemmas had specialized their upper endpoint to 2.
Here their original finite-cutoff arguments are applied with cutoff bP.

All constants and the finite family of Schwartz seminorms are selected
before the moving window, arithmetic data, zero boundary, contour buffer,
prime scale and Boolean deletion mask.  Every P >= 1 is covered, including
the short-scale range, so no lower bound on an individual slot length is
introduced.  No prime cancellation estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.PrimeAnnulus

open MeasureTheory Set Complex
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles PrimeCancellationPrimeSeries
open PrimeCancellationPrimePowers
open scoped Classical BigOperators ContDiff SchwartzMap

variable {α : Type*}

/-- A fixed threshold makes logarithmic division smooth on the whole
annulus, even when its lower endpoint is less than one. -/
def threshold (a b : ℝ) : ℝ :=
  Real.exp (2 * (|Real.log a| + |Real.log b|) + 2)

theorem threshold_pos (a b : ℝ) : 0 < threshold a b := Real.exp_pos _

/-- The genuine contour cost, higher-power cost and short-scale cost.
The last two retain the actual fixed upper endpoint b. -/
def primeConstant (a b δ C degreeBound H : ℝ) : ℝ :=
  24 * C * H / δ ^ 2 + degreeBound * (1 + ratio) * Real.sqrt b +
    b * degreeBound * threshold a b

theorem primeConstant_nonneg (a b δ C degreeBound H : ℝ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hd : 0 ≤ degreeBound) (hH : 0 ≤ H) :
    0 ≤ primeConstant a b δ C degreeBound H := by
  have hr := ratio_pos.le
  have ht := (threshold_pos a b).le
  unfold primeConstant
  positivity

private theorem sum_norm_prime_upper
    (ν : α → ℝ) (c : α → ℂ) (W : ℝ → ℂ) (d M P b : ℝ)
    (hP : 0 < P) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hA : PrimeArithmetic ν c d)
    (hsupport : ∀ x, W x ≠ 0 → x ≤ b) (hbound : ∀ x, ‖W x‖ ≤ M)
    (pool : Finset α) :
    (∑ p ∈ pool, ‖c p * W (ν p / P)‖) ≤ b * M * d * P := by
  have hterm (p : α) : ‖c p * W (ν p / P)‖ ≤ M := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hA.coeff_bound p) (hbound _)
      (norm_nonneg _) zero_le_one
  have hfilter : (∑ p ∈ pool, ‖c p * W (ν p / P)‖) =
      ∑ p ∈ pool.filter (fun p => ν p ≤ b * P), ‖c p * W (ν p / P)‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hcut : ¬ν p ≤ b * P := fun h => hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
    have hzero : W (ν p / P) = 0 := by
      by_contra hne
      exact hcut ((div_le_iff₀ hP).mp (hsupport _ hne))
    simp only [hzero, mul_zero, norm_zero]
  calc
    _ = ∑ p ∈ pool.filter (fun p => ν p ≤ b * P), ‖c p * W (ν p / P)‖ := hfilter
    _ ≤ ∑ _p ∈ pool.filter (fun p => ν p ≤ b * P), M :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = ((pool.filter (fun p => ν p ≤ b * P)).card : ℝ) * M := by simp
    _ ≤ (d * (b * P)) * M :=
      mul_le_mul_of_nonneg_right (hA.count pool (b * P) (mul_nonneg hb hP.le)) hM
    _ = _ := by ring

private theorem sum_norm_tail_upper
    (ν : α → ℝ) (c : α → ℂ) (W : ℝ → ℂ) (d M P b : ℝ)
    (hP : 0 < P) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hA : PrimeArithmetic ν c d)
    (hsupport : ∀ x, W x ≠ 0 → x ≤ b) (hbound : ∀ x, ‖W x‖ ≤ M)
    (pool : Finset α) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ p ∈ pool, ‖primePowerWindowTerm ν c W P n p‖) ≤
      M * d * (1 + ratio) * Real.sqrt b * Real.sqrt P := by
  have hfilter (n : ℕ) :
      (∑ p ∈ pool, ‖primePowerWindowTerm ν c W P n p‖) =
        ∑ p ∈ powerCutoff pool ν (b * P) (n + 2),
          ‖primePowerWindowTerm ν c W P n p‖ := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hcut : ¬ν p ^ (n + 2) ≤ b * P :=
      fun h => hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
    have hzero : W (ν p ^ (n + 2) / P) = 0 := by
      by_contra hne
      exact hcut ((div_le_iff₀ hP).mp (hsupport _ hne))
    simp only [primePowerWindowTerm, hzero, mul_zero, zero_div, norm_zero]
  have hrow (n : ℕ) :
      (∑ p ∈ powerCutoff pool ν (b * P) (n + 2),
        ‖primePowerWindowTerm ν c W P n p‖) ≤
        ((powerCutoff pool ν (b * P) (n + 2)).card : ℝ) * (M / 2) := by
    calc
      _ ≤ ∑ _p ∈ powerCutoff pool ν (b * P) (n + 2), M / 2 := by
        apply Finset.sum_le_sum
        intro p _
        apply (norm_primePowerWindowTerm_le ν c W P M n p
          (hA.coeff_bound p) (hbound _)).trans
        apply div_le_div_of_nonneg_left hM (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast (show 2 ≤ n + 2 by omega)
      _ = _ := by simp
  calc
    _ = ∑ n ∈ Finset.range N, ∑ p ∈ powerCutoff pool ν (b * P) (n + 2),
        ‖primePowerWindowTerm ν c W P n p‖ :=
      Finset.sum_congr rfl (fun n _ => hfilter n)
    _ ≤ ∑ n ∈ Finset.range N,
        ((powerCutoff pool ν (b * P) (n + 2)).card : ℝ) * (M / 2) :=
      Finset.sum_le_sum (fun n _ => hrow n)
    _ = (M / 2) * ∑ n ∈ Finset.range N,
        ((powerCutoff pool ν (b * P) (n + 2)).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (M / 2) * (d * Real.sqrt (b * P) / (1 - ratio)) :=
      mul_le_mul_of_nonneg_left
        (sum_powerCutoff_cards_le pool ν d (b * P) N hA.d_nonneg
          (mul_nonneg hb hP.le) (fun p _ => hA.norm_ge_two p) (hA.count pool))
        (div_nonneg hM (by norm_num))
    _ = M * d * Real.sqrt (b * P) * (1 / (2 * (1 - ratio))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [geometric_half_constant, Real.sqrt_mul hb]; ring

set_option maxHeartbeats 6400000 in
private theorem prime_and_tail_upper
    (ν : α → ℝ) (c : α → ℂ) (W : ℝ → ℂ) (d M P b : ℝ)
    (hP : 0 < P) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hA : PrimeArithmetic ν c d)
    (hsupport : ∀ x, W x ≠ 0 → x ≤ b) (hbound : ∀ x, ‖W x‖ ≤ M) :
    ‖primeSum ν c W P‖ ≤ b * M * d * P ∧
    ‖tailSum ν c W P‖ ≤ M * d * (1 + ratio) * Real.sqrt b * Real.sqrt P ∧
    weightedSum ν c W P = primeSum ν c W P + tailSum ν c W P := by
  have hprime : Summable (fun p : α => ‖c p * W (ν p / P)‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _)
      (sum_norm_prime_upper ν c W d M P b hP hb hM hA hsupport hbound)
  have htail : Summable (fun np : ℕ × α => ‖primePowerWindowTerm ν c W P np.1 np.2‖) :=
    summable_norm_of_rectangle_bound (primePowerWindowTerm ν c W P)
      (M * d * (1 + ratio) * Real.sqrt b * Real.sqrt P)
      (sum_norm_tail_upper ν c W d M P b hP hb hM hA hsupport hbound)
  have hrows : ∀ n : ℕ, Summable (fun p : α => ‖allPowerTerm ν c W P n p‖) := by
    intro n
    cases n with
    | zero => simpa only [allPowerTerm_zero] using hprime
    | succ n => simpa only [Nat.succ_eq_add_one, allPowerTerm_add_one] using htail.prod_factor n
  have houter : Summable (fun n : ℕ => ∑' p : α, ‖allPowerTerm ν c W P n p‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [allPowerTerm_add_one] using htail.prod
  have hfull : Summable (fun np : ℕ × α => allPowerTerm ν c W P np.1 np.2) :=
    ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hrows, houter⟩).of_norm
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_tsum_le_tsum_norm hprime).trans
      (Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
        (sum_norm_prime_upper ν c W d M P b hP hb hM hA hsupport hbound))
  · exact norm_tsum_le_of_rectangle_bound (primePowerWindowTerm ν c W P)
      (M * d * (1 + ratio) * Real.sqrt b * Real.sqrt P)
      (sum_norm_tail_upper ν c W d M P b hP hb hM hA hsupport hbound)
  · calc
      weightedSum ν c W P = ∑' np : ℕ × α, allPowerTerm ν c W P np.1 np.2 := by
        apply tsum_congr
        intro np
        exact logWeightedPowerTerm_eq_allPowerTerm ν c W P np.1 np.2 hP (hA.norm_ge_two np.2)
      _ = ∑' n : ℕ, ∑' p : α, allPowerTerm ν c W P n p := hfull.tsum_prod
      _ = primeSum ν c W P + tailSum ν c W P := by
        rw [← hfull.prod.sum_add_tsum_nat_add 1]
        simp only [Finset.sum_range_one, allPowerTerm_zero, allPowerTerm_add_one]
        rw [← htail.of_norm.tsum_prod]
        rfl

private theorem logWindow_uniform (a b : ℝ) (ha : 0 < a) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Icc a b →
      (∀ x : ℝ, ‖W x‖ ≤ sourceSeminorm s W) ∧
      ∀ P : ℝ, threshold a b ≤ P →
        ContDiff ℝ ∞ (PrimeCancellationLogWindow.logWindow P W) ∧
        ∀ σ ∈ Icc (1 / 2 : ℝ) 2, ∀ t : ℝ,
          ‖mellin (PrimeCancellationLogWindow.logWindow P W)
            ((σ : ℂ) + t * I)‖ ≤ C * sourceSeminorm s W / (1 + |t|) ^ 3 := by
  obtain ⟨s, C, hC, hb⟩ :=
    PrimeCancellation.SchwartzControl.uniform_profile_mellin_source_bound a b ha (1 / 2) 2 3
  let q := insert (0, 0) s
  have hs : s ⊆ q := Finset.subset_insert _ _
  have hzero : (0, 0) ∈ q := Finset.mem_insert_self _ _
  refine ⟨q, C, hC, hzero, ?_⟩
  intro W hW
  refine ⟨?_, ?_⟩
  · intro x
    exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
      (Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) hzero) W)
  · intro P hP
    have hPpos : 0 < P := (threshold_pos a b).trans_le hP
    have hlog : 2 * (|Real.log a| + |Real.log b|) + 2 ≤ Real.log P := by
      have h := Real.log_le_log (threshold_pos a b) hP
      simpa only [threshold, Real.log_exp] using h
    have hlogpos : 0 < Real.log P := by
      linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)]
    have hA : (1 / Real.log P : ℝ) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨(one_div_pos.mpr hlogpos).le,
        (div_le_one₀ hlogpos).mpr (by
          linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])⟩
    have heq : PrimeCancellationLogProfile.profile W (1 / Real.log P) =
        PrimeCancellationLogWindow.logWindow P W :=
      PrimeCancellationLogProfile.profile_eq_log_division W a b P ha hW hPpos (by linarith)
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact PrimeCancellationLogProfile.profile_smooth W a b ha hW (W.smooth ⊤) _
    · intro σ hσ t
      have h := hb W hW (1 / Real.log P) hA σ hσ t
      rw [heq] at h
      apply (le_div_iff₀ (show 0 < (1 + |t|) ^ 3 by positivity)).mpr
      have h' : ‖mellin (PrimeCancellationLogWindow.logWindow P W)
          ((σ : ℂ) + t * I)‖ * (1 + |t|) ^ 3 ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa only [mul_comm] using h
      exact h'.trans
        (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp (Finset.sup_mono hs) W) hC.le)

/-- Genuine unmasked cancellation for every fixed positive annulus.
The finite seminorm family precedes all moving windows and SlotData. -/
theorem exists_uniform_annulus_prime_bound (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ {α : Type*} [Countable α] (W : SchwartzMap ℝ ℂ),
      Function.support (W : ℝ → ℂ) ⊆ Icc a b →
      ∀ (β δ degreeBound H : ℝ) (data : SlotData α β degreeBound),
      heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H →
      ∀ P : ℝ, 1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
        ‖primeSum data.norm data.coefficient W P‖ ≤
          primeConstant a b δ C degreeBound H * sourceSeminorm s W * P ^ (β + δ) := by
  obtain ⟨s, C, hC, hs, hsource⟩ := logWindow_uniform a b ha
  refine ⟨s, C, hC, hs, ?_⟩
  intro α _ W hW β δ degreeBound H data hH P hβ hβ' hδ hδ' hP
  let M := sourceSeminorm s W
  have hM : 0 ≤ M := sourceSeminorm_nonneg s W
  have hb : 0 ≤ b := (ha.trans_le hab).le
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hdeg := data.arithmetic.d_nonneg
  have hHnon : 0 ≤ H :=
    (add_nonneg (heightConstant_nonneg data.analytic) (by positivity)).trans hH
  have hbasic := prime_and_tail_upper data.norm data.coefficient W degreeBound M P b
    hPpos hb hM data.arithmetic (fun y hy => (hW hy).2) (hsource W hW).1
  have htail : 0 ≤ M * degreeBound * (1 + ratio) * Real.sqrt b := by
    have hr := ratio_pos.le
    positivity
  have hsmall : 0 ≤ b * M * degreeBound * threshold a b := by
    have ht := (threshold_pos a b).le
    positivity
  have hbig : 0 ≤ 24 * C * H / δ ^ 2 := by positivity
  have hfactor : primeConstant a b δ C degreeBound H * M =
      (24 * ((C * M) * H) / δ ^ 2 +
        M * degreeBound * (1 + ratio) * Real.sqrt b) +
      b * M * degreeBound * threshold a b := by unfold primeConstant; ring
  by_cases hlarge : threshold a b ≤ P
  · have hVs : Function.support (PrimeCancellationLogWindow.logWindow P W) ⊆ Icc a b :=
      (PrimeCancellationLogWindow.support_logWindow_subset P W).trans hW
    have hsmooth := ((hsource W hW).2 P hlarge).1
    have hdecay := ((hsource W hW).2 P hlarge).2
    have hr : ∀ np : ℕ × α, 0 < primePowerNorm data.norm np :=
      fun np => pow_pos (by linarith [data.arithmetic.norm_ge_two np.2]) _
    have hw := norm_weighted_sum_le_of_cubic_decay data.analytic
      (primePowerNorm data.norm) hr (primePowerCoefficient data.norm data.coefficient)
      data.absolute data.euler (PrimeCancellationLogWindow.logWindow P W) a b ha hVs hsmooth
      δ P (C * M) hβ hβ' hδ hδ' hP (mul_nonneg hC.le hM)
      (fun σ hσ t => hdecay σ ⟨by linarith [hσ.1], hσ.2⟩ t)
    change ‖weightedSum data.norm data.coefficient W P‖ ≤
      24 * ((C * M) * (heightConstant data.analytic + 3 * (data.analytic.k : ℝ))) /
        δ ^ 2 * P ^ (β + δ) at hw
    have hweighted : ‖weightedSum data.norm data.coefficient W P‖ ≤
        24 * ((C * M) * H) / δ ^ 2 * P ^ (β + δ) := by
      apply hw.trans
      gcongr
    have hp := norm_prime_sum_le_of_decomposition
      (weightedSum data.norm data.coefficient W P) (primeSum data.norm data.coefficient W P)
      (tailSum data.norm data.coefficient W P) P (β + δ)
      (24 * ((C * M) * H) / δ ^ 2) (M * degreeBound * (1 + ratio) * Real.sqrt b)
      hP (by linarith) htail hbasic.2.2 hweighted hbasic.2.1
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hPpos.le _)
    change _ ≤ primeConstant a b δ C degreeBound H * M
    rw [hfactor]
    exact le_add_of_nonneg_right hsmall
  · have hshort : P ≤ threshold a b := (lt_of_not_ge hlarge).le
    have hone : 1 ≤ P ^ (β + δ) := Real.one_le_rpow hP (by linarith)
    calc
      _ ≤ b * M * degreeBound * P := hbasic.1
      _ ≤ b * M * degreeBound * threshold a b :=
        mul_le_mul_of_nonneg_left hshort (by positivity)
      _ ≤ (b * M * degreeBound * threshold a b) * P ^ (β + δ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hsmall
      _ ≤ primeConstant a b δ C degreeBound H * sourceSeminorm s W * P ^ (β + δ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hPpos.le _)
        change _ ≤ primeConstant a b δ C degreeBound H * M
        rw [hfactor]
        have hcontour : 0 ≤ 24 * ((C * M) * H) / δ ^ 2 := by positivity
        exact le_add_of_nonneg_left (add_nonneg hcontour htail)

/-- The same genuine estimate with the original finite Boolean mask.
The only mask cost is the count of deleted prime terms. -/
theorem exists_uniform_annulus_masked_prime_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ (0, 0) ∈ s ∧
      ∀ {α : Type*} [Countable α] (W : SchwartzMap ℝ ℂ),
      Function.support (W : ℝ → ℂ) ⊆ Icc a b →
      ∀ (β δ degreeBound H B : ℝ) (data : SlotData α β degreeBound),
      heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H →
      ∀ (P : ℝ) (pool : Finset α) (keep : α → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
      (∀ p : α, W (data.norm p / P) ≠ 0 → p ∈ pool) →
      ((pool.filter (fun p => keep p = false)).card : ℝ) ≤ B →
        ‖maskedPrimeSum data W P pool keep‖ ≤
          (primeConstant a b δ C degreeBound H + B) *
            sourceSeminorm s W * P ^ (β + δ) := by
  obtain ⟨s, C, hC, hs, hprime⟩ := exists_uniform_annulus_prime_bound a b ha hab
  refine ⟨s, C, hC, hs, ?_⟩
  intro α _ W hW β δ degreeBound H B data hH P pool keep hβ hβ' hδ hδ' hP hcover hdeleted
  let M := sourceSeminorm s W
  have hM : 0 ≤ M := sourceSeminorm_nonneg s W
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hB : 0 ≤ B := (Nat.cast_nonneg _).trans hdeleted
  have hnorm (p : α) : ‖data.coefficient p * W (data.norm p / P)‖ ≤ M := by
    have hb : ‖W (data.norm p / P)‖ ≤ M :=
      (SchwartzMap.norm_le_seminorm ℝ W _).trans
        (Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) hs) W)
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (data.arithmetic.coeff_bound p) hb
      (norm_nonneg _) zero_le_one
  have hbase := hprime W hW β δ degreeBound H data hH P hβ hβ' hδ hδ' hP
  have hmask := PrimeCancellationAux.norm_maskedSum_le_of_card pool
    (fun p => data.coefficient p * W (data.norm p / P)) keep M B hM
    (fun p _ _ => hnorm p) hdeleted
  rw [finite_sum_eq_primeSum data W P pool hcover] at hmask
  have hone : 1 ≤ P ^ (β + δ) := Real.one_le_rpow hP (by linarith)
  have hcost : B * M ≤ (B * M) * P ^ (β + δ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (mul_nonneg hB hM)
  calc
    _ ≤ ‖primeSum data.norm data.coefficient W P‖ + B * M := hmask
    _ ≤ primeConstant a b δ C degreeBound H * M * P ^ (β + δ) + B * M :=
      add_le_add hbase le_rfl
    _ ≤ primeConstant a b δ C degreeBound H * M * P ^ (β + δ) +
        (B * M) * P ^ (β + δ) := add_le_add le_rfl hcost
    _ = _ := by dsimp only [M]; ring

end HeckeSkeleton.Moments.EngineInduction.PrimeAnnulus
