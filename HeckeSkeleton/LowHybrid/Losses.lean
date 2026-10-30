import HeckeSkeleton.LowHybrid.Parameters

/-!
# Uniform absorption of the hybrid arithmetic losses

The divisor and harmonic envelopes have arbitrary-small-power bounds. Their
constants are chosen before the four scales. This file absorbs the five
divisor factors, two sieve powers, and five harmonic factors into the single
power requested by LOW-HYBRID. No energy estimate is an input here.
-/

namespace HeckeSkeleton.LowHybrid

noncomputable section

/-- A uniform small-power bound on the range X >= 1. -/
def SubpowerBound (f : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ X : ℝ, 1 ≤ X → f X ≤ C * X ^ eps

/-- A direct, explicit bound for the logarithmic loss. -/
theorem one_add_log_le_small_power (X eps : ℝ) (hX : 1 ≤ X) (heps : 0 < eps) :
    1 + Real.log X ≤ (1 + 1 / eps) * X ^ eps := by
  have hpow : 1 ≤ X ^ eps := Real.one_le_rpow hX (le_of_lt heps)
  have hlog := Real.log_le_rpow_div (le_trans zero_le_one hX) heps
  calc
    1 + Real.log X ≤ X ^ eps + X ^ eps / eps := add_le_add hpow hlog
    _ = _ := by ring

/-- Every uniform logarithmic envelope has a uniform small-power bound. -/
theorem subpower_of_logarithmic_bound (f : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ X : ℝ, 1 ≤ X → f X ≤ C * (1 + Real.log X)) :
    SubpowerBound f := by
  intro eps heps
  refine ⟨C * (1 + 1 / eps), mul_pos hC (by positivity), ?_⟩
  intro X hX
  calc
    f X ≤ C * (1 + Real.log X) := hf X hX
    _ ≤ C * ((1 + 1 / eps) * X ^ eps) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_small_power X eps hX heps) (le_of_lt hC)
    _ = _ := by ring

/-- Every argument used in the loss ledger lies between 1 and the total
scale K*N*B*L. -/
theorem hybrid_total_scale_bounds (K N B L : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L) :
    1 ≤ K * N * B * L ∧ K ≤ K * N * B * L ∧ N ≤ K * N * B * L ∧
      B ≤ K * N * B * L ∧ L ≤ K * N * B * L ∧
      N * B ≤ K * N * B * L ∧ K * N * B ≤ K * N * B * L ∧
      N * L ≤ K * N * B * L := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  constructor
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hN) hB) hL
  constructor
  · calc
      K = K * 1 * 1 * 1 := by ring
      _ ≤ K * N * B * L := by gcongr
  constructor
  · calc
      N = 1 * N * 1 * 1 := by ring
      _ ≤ K * N * B * L := by gcongr
  constructor
  · calc
      B = 1 * 1 * B * 1 := by ring
      _ ≤ K * N * B * L := by gcongr
  constructor
  · calc
      L = 1 * 1 * 1 * L := by ring
      _ ≤ K * N * B * L := by gcongr
  constructor
  · calc
      N * B = 1 * N * B * 1 := by ring
      _ ≤ K * N * B * L := by gcongr
  constructor
  · calc
      K * N * B = K * N * B * 1 := by ring
      _ ≤ K * N * B * L := by gcongr
  · calc
      N * L = 1 * N * 1 * L := by ring
      _ ≤ K * N * B * L := by gcongr

/-- The exact remaining arithmetic loss after the D-column mass has been
charged to its own divisors and all harmonic cutoffs enlarged to B or N. -/
def hybridArithmeticLoss (divisor harmonic : ℝ → ℝ)
    (eta K N B L : ℝ) : ℝ :=
  divisor K ^ 2 * divisor (N * B) * divisor N * divisor L *
    (K * N * B) ^ eta * (N * L) ^ eta * harmonic B ^ 3 * harmonic N ^ 2

/-- A pointwise twelve-factor ledger. The two sieve exponents, all five
divisor factors, and all five harmonic factors are accounted for. -/
theorem hybrid_arithmetic_loss_le
    (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ)
    (hCD : 0 ≤ CD) (hCH : 0 ≤ CH) (heta : 0 ≤ eta)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : ∀ X : ℝ, 1 ≤ X → divisor X ≤ CD * X ^ eta)
    (hh : ∀ X : ℝ, 1 ≤ X → harmonic X ≤ CH * X ^ eta) :
    hybridArithmeticLoss divisor harmonic eta K N B L ≤
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
  have hpQ := Real.rpow_le_rpow (le_trans zero_le_one hKNB) hKNBM heta
  have hpC := Real.rpow_le_rpow (le_trans zero_le_one hNL) hNLM heta
  have hdK0 := hd0 K hK
  have hdNB0 := hd0 (N * B) hNB
  have hdN0 := hd0 N hN
  have hdL0 := hd0 L hL
  have hhB0 := hh0 B hB
  have hhN0 := hh0 N hN
  have hMP0 : 0 ≤ M ^ eta := Real.rpow_nonneg hM0 eta
  calc
    hybridArithmeticLoss divisor harmonic eta K N B L ≤
        (CD * M ^ eta) ^ 2 * (CD * M ^ eta) * (CD * M ^ eta) * (CD * M ^ eta) *
          M ^ eta * M ^ eta * (CH * M ^ eta) ^ 3 * (CH * M ^ eta) ^ 2 := by
      unfold hybridArithmeticLoss
      gcongr
    _ = (CD ^ 5 * CH ^ 5) * (M ^ eta) ^ 12 := by ring
    _ = (CD ^ 5 * CH ^ 5) * M ^ (12 * eta) := by
      rw [← Real.rpow_mul_natCast hM0 eta 12]
      congr 1
      congr 1
      ring
    _ = _ := rfl

/-- Uniform epsilon absorption, with the auxiliary exponent and constant
chosen before all four scales. eta=eps/12 is sufficient. -/
theorem hybrid_arithmetic_loss_subpower
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        hybridArithmeticLoss divisor harmonic eta K N B L ≤
          C * (K * N * B * L) ^ eps := by
  let eta := eps / 12
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨CD, hCD, hdb⟩ := hd eta heta
  obtain ⟨CH, hCH, hhb⟩ := hh eta heta
  refine ⟨eta, CD ^ 5 * CH ^ 5, heta, mul_pos (pow_pos hCD _) (pow_pos hCH _), ?_⟩
  intro K N B L hK hN hB hL
  have h := hybrid_arithmetic_loss_le divisor harmonic CD CH eta K N B L
    (le_of_lt hCD) (le_of_lt hCH) (le_of_lt heta) hK hN hB hL hd0 hh0 hdb hhb
  have hbudget : 12 * eta = eps := by dsimp [eta]; ring
  simpa only [hbudget] using h

#print axioms one_add_log_le_small_power
#print axioms subpower_of_logarithmic_bound
#print axioms hybrid_arithmetic_loss_le
#print axioms hybrid_arithmetic_loss_subpower

end
end HeckeSkeleton.LowHybrid
