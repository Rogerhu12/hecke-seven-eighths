import HeckeSkeleton.LowHybrid.Losses

/-!
# Loss absorption with the natural common-divisor cutoff

Both common-divisor indices range over the original row cutoff K.  Keeping
that complete support gives the harmonic factor H(K), while the completed
variables contribute H(B)^3 H(N).  The same twelve-factor ledger absorbs
all arithmetic losses uniformly before the four scales are selected.
-/

namespace HeckeSkeleton.LowHybrid

noncomputable section

def naturalHybridArithmeticLoss (divisor harmonic : ℝ → ℝ)
    (eta K N B L : ℝ) : ℝ :=
  divisor K ^ 2 * divisor (N * B) * divisor N * divisor L *
    (K * N * B) ^ eta * (N * L) ^ eta * harmonic B ^ 3 * harmonic N * harmonic K

theorem natural_hybrid_arithmetic_loss_le
    (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ)
    (hCD : 0 ≤ CD) (hCH : 0 ≤ CH) (heta : 0 ≤ eta)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : ∀ X : ℝ, 1 ≤ X → divisor X ≤ CD * X ^ eta)
    (hh : ∀ X : ℝ, 1 ≤ X → harmonic X ≤ CH * X ^ eta) :
    naturalHybridArithmeticLoss divisor harmonic eta K N B L ≤
      (CD ^ 5 * CH ^ 5) * (K * N * B * L) ^ (12 * eta) := by
  let M := K * N * B * L
  obtain ⟨hM, hKM, hNM, hBM, hLM, hNBM, hKNBM, hNLM⟩ :=
    hybrid_total_scale_bounds K N B L hK hN hB hL
  have hNB : 1 ≤ N * B := one_le_mul_of_one_le_of_one_le hN hB
  have hKNB : 1 ≤ K * N * B :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hNL : 1 ≤ N * L := one_le_mul_of_one_le_of_one_le hN hL
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hD (X : ℝ) (hX : 1 ≤ X) (hXM : X ≤ M) :
      divisor X ≤ CD * M ^ eta :=
    (hd X hX).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_trans zero_le_one hX) hXM heta) hCD)
  have hH (X : ℝ) (hX : 1 ≤ X) (hXM : X ≤ M) :
      harmonic X ≤ CH * M ^ eta :=
    (hh X hX).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_trans zero_le_one hX) hXM heta) hCH)
  have hdK := hD K hK hKM
  have hdNB := hD (N * B) hNB hNBM
  have hdN := hD N hN hNM
  have hdL := hD L hL hLM
  have hhB := hH B hB hBM
  have hhN := hH N hN hNM
  have hhK := hH K hK hKM
  have hpQ := Real.rpow_le_rpow (le_trans zero_le_one hKNB) hKNBM heta
  have hpC := Real.rpow_le_rpow (le_trans zero_le_one hNL) hNLM heta
  have hdK0 := hd0 K hK
  have hdNB0 := hd0 (N * B) hNB
  have hdN0 := hd0 N hN
  have hdL0 := hd0 L hL
  have hhB0 := hh0 B hB
  have hhN0 := hh0 N hN
  have hhK0 := hh0 K hK
  have hMP0 : 0 ≤ M ^ eta := Real.rpow_nonneg hM0 eta
  calc
    naturalHybridArithmeticLoss divisor harmonic eta K N B L ≤
        (CD * M ^ eta) ^ 2 * (CD * M ^ eta) * (CD * M ^ eta) * (CD * M ^ eta) *
          M ^ eta * M ^ eta * (CH * M ^ eta) ^ 3 * (CH * M ^ eta) *
            (CH * M ^ eta) := by
      unfold naturalHybridArithmeticLoss
      gcongr
    _ = (CD ^ 5 * CH ^ 5) * (M ^ eta) ^ 12 := by ring
    _ = (CD ^ 5 * CH ^ 5) * M ^ (12 * eta) := by
      rw [← Real.rpow_mul_natCast hM0 eta 12]
      congr 1
      congr 1
      ring
    _ = _ := rfl

theorem natural_hybrid_arithmetic_loss_subpower
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        naturalHybridArithmeticLoss divisor harmonic eta K N B L ≤
          C * (K * N * B * L) ^ eps := by
  let eta := eps / 12
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨CD, hCD, hdb⟩ := hd eta heta
  obtain ⟨CH, hCH, hhb⟩ := hh eta heta
  refine ⟨eta, CD ^ 5 * CH ^ 5, heta, mul_pos (pow_pos hCD _) (pow_pos hCH _), ?_⟩
  intro K N B L hK hN hB hL
  have h := natural_hybrid_arithmetic_loss_le divisor harmonic CD CH eta K N B L
    (le_of_lt hCD) (le_of_lt hCH) (le_of_lt heta) hK hN hB hL hd0 hh0 hdb hhb
  have hbudget : 12 * eta = eps := by dsimp [eta]; ring
  simpa only [hbudget] using h

#print axioms natural_hybrid_arithmetic_loss_le
#print axioms natural_hybrid_arithmetic_loss_subpower

end
end HeckeSkeleton.LowHybrid
