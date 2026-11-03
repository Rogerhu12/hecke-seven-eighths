import HeckeGeneral.Analysis.SlotSelection
import HeckeGeneral.Analysis.DynamicWitnessCrossing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
Row counts from saturated witnesses (Q Proposition 19.2, `prop:detector-counts`;
M (7.1)--(7.3)).  Q uses it for `Δ ≤ 1/24`; the selected counts below allow
`Δ ≤ 1/8`, i.e. capacities up to `κ = 1`, which Q Lemma 18.1 covers.

One witness subdivision `C` of one amplitude set is fixed at base `U`.  Every
row carries an inverse value `M u` and a plain value `S u` with the saturated
spikes of Q Proposition 8.3, and the physical slot values `Qv i u` obey the
amplitude lower bounds of Q Section 19.1.  The hypotheses `hI`, `hIamp`, `hP`
and `hP0` are the marked inverse moment with selected slots, the amplified
no-slot inverse moment, the paired fourth moment at the DYNAMIC capacity
`κ = 3/4 + 2Δ ≤ 1`, and its zero-slot case, all for these same values.

The conclusion is the short/long crossing count with the dynamic capacity
loss `Δ/4` and an explicit total of the real losses.  Markov counting, the
slot selection and the case analysis are proved here; neither the witnesses
nor the moment estimates are constructed.
-/

namespace HeckeGeneral.Analysis

open OAI.SevenEighths.Endpoint
open scoped BigOperators

/-- Markov counting on a finite row set. -/
theorem card_mul_le_of_forall_le {ι : Type*} (C : Finset ι) (f : ι → ℝ) {a B : ℝ}
    (hlow : ∀ u ∈ C, a ≤ f u) (hsum : ∑ u ∈ C, f u ≤ B) : (C.card : ℝ) * a ≤ B := by
  have h := Finset.card_nsmul_le_sum C f a hlow
  rw [nsmul_eq_mul] at h
  linarith

/-- The amplified no-slot inverse exponent `e(r)` of Q (19.10). -/
noncomputable def amplifiedInverseExponent (r : ℝ) : ℝ := max 1 ((1 + 5 * r) / 6)

/-- Markov counting at base `U`: a pointwise lower bound `U ^ a` and a moment
bound `k U ^ b H` leave at most `k U ^ (b - a) H` rows. -/
private theorem card_le_rpow_of_markov {Row : Type*} (C : Finset Row) (f : Row → ℝ)
    {U a b k H : ℝ} (hU : 0 < U) (hlow : ∀ u ∈ C, U ^ a ≤ f u)
    (hsum : ∑ u ∈ C, f u ≤ k * U ^ b * H) :
    (C.card : ℝ) ≤ k * U ^ (b - a) * H := by
  have h := card_mul_le_of_forall_le C f hlow hsum
  have hpos : 0 < U ^ a := Real.rpow_pos_of_pos hU a
  have heq : k * U ^ (b - a) * H = k * U ^ b * H / U ^ a := by
    rw [Real.rpow_sub hU]
    ring
  rw [heq, le_div_iff₀ hpos]
  exact h

/-- Raising the exponent of a row-count bound at base `U ≥ 1`. -/
private theorem card_le_rpow_mono {Row : Type*} {C : Finset Row} {U a b k H : ℝ}
    (hU : 1 ≤ U) (hk : 0 ≤ k) (hH : 0 ≤ H)
    (h : (C.card : ℝ) ≤ k * U ^ a * H) (hab : a ≤ b) :
    (C.card : ℝ) ≤ k * U ^ b * H :=
  h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hab) hk) hH)

private theorem rpow_two_mul_eq_sq {U : ℝ} (hU : 0 < U) (a : ℝ) :
    U ^ (2 * a) = (U ^ a) ^ 2 := by
  rw [two_mul, Real.rpow_add hU, sq]

/-- The selected slot values multiply their amplitude lower bounds. -/
private theorem rpow_sum_le_norm_prod {Row ι : Type*} (I : Finset ι) (w g : ι → ℝ)
    (Qv : ι → Row → ℂ) {U : ℝ} (hU : 0 < U) (u : Row)
    (h : ∀ i ∈ I, U ^ (w i * g i) ≤ ‖Qv i u‖) :
    U ^ (∑ i ∈ I, w i * g i) ≤ ‖∏ i ∈ I, Qv i u‖ := by
  rw [Real.rpow_sum_of_pos hU, norm_prod]
  exact Finset.prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos hU _).le) h

/-- Pointwise lower bound for a marked inverse row. -/
private theorem marked_inverse_lower {Row ι : Type*} (I : Finset ι) (w g : ι → ℝ)
    (Qv : ι → Row → ℂ) (M : Row → ℂ) {U δ r lam : ℝ} (hU : 0 < U) (u : Row)
    (hM : U ^ (δ * r - lam) ≤ ‖M u‖ ^ 2)
    (hQ : ∀ i ∈ I, U ^ (w i * g i) ≤ ‖Qv i u‖) :
    U ^ (δ * r - lam + 2 * ∑ i ∈ I, w i * g i) ≤ ‖M u * ∏ i ∈ I, Qv i u‖ ^ 2 := by
  have hprod := rpow_sum_le_norm_prod I w g Qv hU u hQ
  rw [Real.rpow_add hU, rpow_two_mul_eq_sq hU, norm_mul, mul_pow]
  exact mul_le_mul hM (pow_le_pow_left₀ (Real.rpow_pos_of_pos hU _).le hprod 2)
    (by positivity) (by positivity)

/-- Pointwise lower bound for a marked plain (paired fourth moment) row. -/
private theorem marked_plain_lower {Row ι : Type*} (I : Finset ι) (w g : ι → ℝ)
    (Qv : ι → Row → ℂ) (S : Row → ℂ) {U δ m lam : ℝ} (hU : 0 < U) (u : Row)
    (hS : U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2)
    (hQ : ∀ i ∈ I, U ^ (w i * g i) ≤ ‖Qv i u‖) :
    U ^ (2 * (δ * m - lam) + 2 * ∑ i ∈ I, w i * g i) ≤
      ‖S u ^ 2 * ∏ i ∈ I, Qv i u‖ ^ 2 := by
  have hprod := rpow_sum_le_norm_prod I w g Qv hU u hQ
  rw [Real.rpow_add hU, rpow_two_mul_eq_sq hU, rpow_two_mul_eq_sq hU, norm_mul, mul_pow,
    norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (Real.rpow_pos_of_pos hU _).le hS 2)
    (pow_le_pow_left₀ (Real.rpow_pos_of_pos hU _).le hprod 2) (by positivity) (by positivity)

/-- Pointwise lower bound for a zero-slot plain row. -/
private theorem plain_lower {Row : Type*} (S : Row → ℂ) {U δ m lam : ℝ} (hU : 0 < U)
    (u : Row) (hS : U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2) :
    U ^ (2 * (δ * m - lam)) ≤ ‖S u ^ 2‖ ^ 2 := by
  rw [rpow_two_mul_eq_sq hU, norm_pow]
  exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hU _).le hS 2

/-- The short witness count at `y = 1/2 - q/δ` is `1 - δ + K`, where
`K (3δ - 17q/9) = (2δ - 8q/9)(δ - q)(3/2 - t)` (the coordinates
`D_x = 3 - 17x/9`, `P_x = (2 - 8x/9)(1 - x)` with `x = q/δ`, cleared of `δ`). -/
private theorem shortWitnessCount_split {δ q t : ℝ} (hδ0 : 0 < δ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ δ / 2) (ht2 : t ≤ 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧
      K * (3 * δ - 17 * q / 9) = (2 * δ - 8 * q / 9) * (δ - q) * (3 / 2 - t) ∧
      shortWitnessCount δ (1 / 2 - q / δ) t = 1 - δ + K := by
  have hδne : δ ≠ 0 := hδ0.ne'
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = q / δ := ⟨_, rfl⟩
  have hqx : q = δ * x := by
    rw [hx]
    field_simp
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact div_nonneg hq0 hδ0.le
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ hδ0]
    linarith
  have hD : 0 < 3 - 17 * x / 9 := by linarith
  refine ⟨δ * ((2 - 8 * x / 9) * (1 - x)) * (3 / 2 - t) / (3 - 17 * x / 9), ?_, ?_, ?_⟩
  · apply div_nonneg _ hD.le
    apply mul_nonneg (mul_nonneg hδ0.le (mul_nonneg (by linarith) (by linarith)))
    linarith
  · have h := div_mul_cancel₀ (δ * ((2 - 8 * x / 9) * (1 - x)) * (3 / 2 - t)) hD.ne'
    rw [hqx]
    linear_combination δ * h
  · unfold shortWitnessCount
    rw [← hx, witnessPrimeWeight_coordinate, witnessDenominator_coordinate]
    ring

/-- Q `prop:detector-counts`: selected witnesses at parameter `t`, dynamic capacity. -/
theorem witness_row_count {Row ι : Type*} [DecidableEq ι]
    (C : Finset Row) (slots : Finset ι) (w g : ι → ℝ) (Qv : ι → Row → ℂ) (M S : Row → ℂ)
    {U δ Δ q t r m lam η ν k H wmax : ℝ}
    (hU : 1 < U) (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ δ / 2)
    (hqmean : q * ∑ i ∈ slots, w i = ∑ i ∈ slots, w i * g i)
    (hw : ∀ i ∈ slots, 0 < w i) (hg0 : ∀ i ∈ slots, 0 ≤ g i) (hg1 : ∀ i ∈ slots, g i ≤ δ / 2)
    (hwmax : ∀ i ∈ slots, w i ≤ wmax) (hwmax0 : 0 ≤ wmax)
    (hsupply : 7 / 37 ≤ ∑ i ∈ slots, w i)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 3 / 2) (_hr0 : 0 ≤ r) (_hm0 : 0 ≤ m)
    (hrt : r ≤ t + η) (hrmt : t - η ≤ r + m)
    (hlam : 0 ≤ lam) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 100) (hν : 0 < ν) (hν1 : ν ≤ 1 / 100)
    (hk : 0 ≤ k) (hH : 0 ≤ H)
    (hMspike : ∀ u ∈ C, U ^ (δ * r - lam) ≤ ‖M u‖ ^ 2)
    (hSspike : ∀ u ∈ C, U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2)
    (hQspike : ∀ i ∈ slots, 0 < g i → ∀ u ∈ C, U ^ (w i * g i) ≤ ‖Qv i u‖)
    (hI : ∀ I ⊆ slots, r + 2 * ∑ i ∈ I, w i ≤ 1 - 2 * ν →
      2 * r + 8 * ∑ i ∈ I, w i ≤ 3 - 2 * ν →
      ∑ u ∈ C, ‖M u * ∏ i ∈ I, Qv i u‖ ^ 2 ≤ k * U ^ (1 + lam) * H)
    (hIamp : ∑ u ∈ C, ‖M u‖ ^ 2 ≤ k * U ^ (amplifiedInverseExponent r + lam) * H)
    (hP : ∀ I ⊆ slots, 2 * m + 6 * (3 / 4 + 2 * Δ) * ∑ i ∈ I, w i ≤ 1 →
      ∑ u ∈ C, ‖S u ^ 2 * ∏ i ∈ I, Qv i u‖ ^ 2 ≤ k * U ^ (1 + lam) * H)
    (hP0 : ∑ u ∈ C, ‖S u ^ 2‖ ^ 2 ≤ k * U ^ (1 + lam) * H) :
    (C.card : ℝ) ≤ k * U ^ (max (shortWitnessCount δ (1 / 2 - q / δ) t)
      (longWitnessCount δ t) + Δ / 4 + (3 * lam + δ * wmax + 12 * ν + 4 * η)) * H := by
  have hU0 : (0 : ℝ) < U := by linarith
  /- Markov bounds: (amp) amplified inverse, (P0) zero-slot plain,
  (I) marked inverse, (P) marked plain. -/
  have hAmp : (C.card : ℝ) ≤ k * U ^ (amplifiedInverseExponent r + lam - (δ * r - lam)) * H :=
    card_le_rpow_of_markov C (fun u => ‖M u‖ ^ 2) hU0 hMspike hIamp
  have hZero : (C.card : ℝ) ≤ k * U ^ (1 + lam - 2 * (δ * m - lam)) * H :=
    card_le_rpow_of_markov C (fun u => ‖S u ^ 2‖ ^ 2) hU0
      (fun u hu => plain_lower S hU0 u (hSspike u hu)) hP0
  have hInv : ∀ I ⊆ slots, (∀ i ∈ I, 0 < g i) → r + 2 * ∑ i ∈ I, w i ≤ 1 - 2 * ν →
      2 * r + 8 * ∑ i ∈ I, w i ≤ 3 - 2 * ν →
      (C.card : ℝ) ≤ k * U ^ (1 + lam - (δ * r - lam + 2 * ∑ i ∈ I, w i * g i)) * H :=
    fun I hIs hIg h1 h2 =>
      card_le_rpow_of_markov C (fun u => ‖M u * ∏ i ∈ I, Qv i u‖ ^ 2) hU0
        (fun u hu => marked_inverse_lower I w g Qv M hU0 u (hMspike u hu)
          (fun i hi => hQspike i (hIs hi) (hIg i hi) u hu))
        (hI I hIs h1 h2)
  have hPl : ∀ I ⊆ slots, (∀ i ∈ I, 0 < g i) →
      2 * m + 6 * (3 / 4 + 2 * Δ) * ∑ i ∈ I, w i ≤ 1 →
      (C.card : ℝ) ≤ k * U ^ (1 + lam - (2 * (δ * m - lam) + 2 * ∑ i ∈ I, w i * g i)) * H :=
    fun I hIs hIg h1 =>
      card_le_rpow_of_markov C (fun u => ‖S u ^ 2 * ∏ i ∈ I, Qv i u‖ ^ 2) hU0
        (fun u hu => marked_plain_lower I w g Qv S hU0 u (hSspike u hu)
          (fun i hi => hQspike i (hIs hi) (hIg i hi) u hu))
        (hP I hIs h1)
  -- Whole-slot selection with amplitude ceiling `δ / 2`.
  have hsel : ∀ z : ℝ, 0 ≤ z → z ≤ ∑ i ∈ slots, w i → ∃ I ⊆ slots, (∀ i ∈ I, 0 < g i) ∧
      ∑ i ∈ I, w i ≤ z ∧ q * z - δ / 2 * wmax ≤ ∑ i ∈ I, w i * g i :=
    fun z hz0 hzW => exists_slot_selection slots w g hw hg0 hg1 hwmax (by linarith) hwmax0
      hqmean hz0 hzW
  -- The short count as `1 - δ + K`, and the long count.
  obtain ⟨K, hK0, hKD, hRs⟩ := shortWitnessCount_split (t := t) hδ0 hq0 hq1 ht2
  have hLdef : longWitnessCount δ t = 1 - δ + (5 / 6 - δ) * (t - 1) := rfl
  have hmaxS : 1 - δ + K ≤
      max (shortWitnessCount δ (1 / 2 - q / δ) t) (longWitnessCount δ t) := by
    rw [← hRs]
    exact le_max_left _ _
  have hmaxL : 1 - δ + (5 / 6 - δ) * (t - 1) ≤
      max (shortWitnessCount δ (1 / 2 - q / δ) t) (longWitnessCount δ t) := by
    rw [← hLdef]
    exact le_max_right _ _
  have hwm : 0 ≤ δ * wmax := mul_nonneg hδ0.le hwmax0
  have hqν : q * ν ≤ 1 / 2 * ν := mul_le_mul_of_nonneg_right (by linarith) hν.le
  have hδν : δ * ν ≤ 5 / 6 * ν := mul_le_mul_of_nonneg_right hδ1 hν.le
  rcases le_or_gt 1 r with hr1 | hr1
  · -- Case `r ≥ 1`: the amplified inverse moment gives the long count.
    have he : amplifiedInverseExponent r = (1 + 5 * r) / 6 := by
      unfold amplifiedInverseExponent
      exact max_eq_right (by linarith)
    rw [he] at hAmp
    refine card_le_rpow_mono hU.le hk hH hAmp ?_
    have h1 : (5 / 6 - δ) * r ≤ (5 / 6 - δ) * (t + η) :=
      mul_le_mul_of_nonneg_left hrt (by linarith)
    have h2 : 0 ≤ δ * η := mul_nonneg hδ0.le hη
    linarith
  rcases le_or_gt (1 / 2) m with hm2 | hm2
  · -- Case `r < 1`, `m ≥ 1/2`: the zero-slot plain moment.
    refine card_le_rpow_mono hU.le hk hH hZero ?_
    have h1 : δ * (1 / 2) ≤ δ * m := mul_le_mul_of_nonneg_left hm2 hδ0.le
    linarith
  -- Case `r < 1`, `m < 1/2`.
  have ha2 : 0 < δ - q := by linarith
  have ha1 : 0 < 2 * δ - 8 * q / 9 := by linarith
  have hD' : 0 < 3 * δ - 17 * q / 9 := by linarith
  have he1 : amplifiedInverseExponent r = 1 := by
    unfold amplifiedInverseExponent
    exact max_eq_left (by linarith)
  by_cases hcase : 1 - q - (δ - q) * r ≤ 1 - δ + K
  · /- Case `r ≥ r*`: the slotted inverse exponent `A_I(r) = 1 - q - (δ - q) r`
    is at most the short count.  This forces `1 - r ≤ 14/37`. -/
    have h1 : (δ - q) * (1 - r) * (3 * δ - 17 * q / 9) ≤ K * (3 * δ - 17 * q / 9) :=
      mul_le_mul_of_nonneg_right (by linarith) hD'.le
    have h2 : (2 * δ - 8 * q / 9) * (δ - q) * (3 / 2 - t) ≤
        (2 * δ - 8 * q / 9) * (δ - q) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ha1.le ha2.le)
    have h3 : (δ - q) * ((1 - r) * (3 * δ - 17 * q / 9)) ≤
        (δ - q) * ((2 * δ - 8 * q / 9) / 2) := by
      linarith
    have h4 : (1 - r) * (3 * δ - 17 * q / 9) ≤ (2 * δ - 8 * q / 9) / 2 :=
      le_of_mul_le_mul_left h3 ha2
    have hr23 : 1 - r ≤ 14 / 37 := by
      by_contra hcon
      have h5 := mul_lt_mul_of_pos_right (not_le.mp hcon) hD'
      linarith
    rcases le_or_gt (1 - r) (4 * ν) with hν4 | hν4
    · -- `r` is within `4ν` of `1`: the amplified moment with `e(r) = 1`.
      rw [he1] at hAmp
      refine card_le_rpow_mono hU.le hk hH hAmp ?_
      have h6 : δ * (1 - r) ≤ δ * (4 * ν) := mul_le_mul_of_nonneg_left hν4 hδ0.le
      linarith
    · -- Select whole slots of total length at most `(1 - r)/2 - ν`.
      obtain ⟨I, hIs, hIg, hIw, hIgain⟩ :=
        hsel ((1 - r) / 2 - ν) (by linarith) (by linarith)
      have hb := hInv I hIs hIg (by linarith) (by linarith)
      refine card_le_rpow_mono hU.le hk hH hb ?_
      linarith
  · /- Case `r < r*`: then `t - r > 1/3`, and the plain exponent
    `S_t(r) = 1 - 4q/9 - (2δ - 8q/9)(t - r)` is below the short count. -/
    have hcase' : 1 - δ + K < 1 - q - (δ - q) * r := not_le.mp hcase
    have h1 : K * (3 * δ - 17 * q / 9) < (δ - q) * (1 - r) * (3 * δ - 17 * q / 9) :=
      mul_lt_mul_of_pos_right (by linarith) hD'
    have h2 : (δ - q) * ((2 * δ - 8 * q / 9) * (3 / 2 - t)) <
        (δ - q) * ((1 - r) * (3 * δ - 17 * q / 9)) := by
      linarith
    have h3 : (2 * δ - 8 * q / 9) * (3 / 2 - t) < (1 - r) * (3 * δ - 17 * q / 9) :=
      lt_of_mul_lt_mul_left h2 ha2.le
    have htr : 1 / 3 < t - r := by
      by_contra hcon
      have h5 := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hD'.le
      have h6 := mul_le_mul_of_nonneg_left ht1 ha2.le
      linarith
    have hm3 : 1 / 3 - η < m := by linarith
    -- The convex combination `D' R_short = a₁ A_I(r) + a₂ S_t(r)`.
    have hid : (3 * δ - 17 * q / 9) * (1 - δ + K) =
        (2 * δ - 8 * q / 9) * (1 - q - (δ - q) * r) +
          (δ - q) * (1 - 4 * q / 9 - (2 * δ - 8 * q / 9) * (t - r)) := by
      linear_combination hKD
    have hSt : 1 - 4 * q / 9 - (2 * δ - 8 * q / 9) * (t - r) < 1 - δ + K := by
      by_contra hcon
      have h7 := mul_lt_mul_of_pos_left hcase' ha1
      have h8 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha2.le
      linarith
    have hκ : 0 < 6 * (3 / 4 + 2 * Δ) := by linarith
    rcases le_or_gt (1 - 2 * m) (12 * (3 / 4 + 2 * Δ) * ν) with hzP | hzP
    · -- A short plain request: the zero-slot plain moment.
      refine card_le_rpow_mono hU.le hk hH hZero ?_
      have h9 : δ * (1 - 2 * m) ≤ δ * (12 * (3 / 4 + 2 * Δ) * ν) :=
        mul_le_mul_of_nonneg_left hzP hδ0.le
      have h10 : δ * (Δ * ν) ≤ 5 / 6 * (Δ * ν) :=
        mul_le_mul_of_nonneg_right hδ1 (mul_nonneg hΔ0 hν.le)
      have h11 : Δ * ν ≤ 1 / 8 * ν := mul_le_mul_of_nonneg_right hΔ1 hν.le
      linarith
    · -- Select whole slots of total length at most `(1 - 2m)/(6κ) - ν`.
      obtain ⟨zP, hzPdef⟩ : ∃ zP : ℝ, zP = (1 - 2 * m) / (6 * (3 / 4 + 2 * Δ)) :=
        ⟨_, rfl⟩
      have hzPmul : zP * (6 * (3 / 4 + 2 * Δ)) = 1 - 2 * m := by
        rw [hzPdef]
        exact div_mul_cancel₀ _ hκ.ne'
      have hzP0 : 0 ≤ zP := by
        rw [hzPdef]
        exact div_nonneg (by linarith) hκ.le
      have hzP2 : 2 * ν < zP := by
        by_contra hcon
        have h12 := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hκ.le
        linarith
      have hzPup : zP ≤ 53 / 675 := by
        have h13 : zP * (9 / 2) ≤ zP * (6 * (3 / 4 + 2 * Δ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hzP0
        linarith
      obtain ⟨I, hIs, hIg, hIw, hIgain⟩ := hsel (zP - ν) (by linarith) (by linarith)
      have hcap : 2 * m + 6 * (3 / 4 + 2 * Δ) * ∑ i ∈ I, w i ≤ 1 := by
        have h14 : 6 * (3 / 4 + 2 * Δ) * ∑ i ∈ I, w i ≤ 6 * (3 / 4 + 2 * Δ) * (zP - ν) :=
          mul_le_mul_of_nonneg_left hIw hκ.le
        have h15 : 0 ≤ Δ * ν := mul_nonneg hΔ0 hν.le
        linarith
      have hb := hPl I hIs hIg hcap
      refine card_le_rpow_mono hU.le hk hH hb ?_
      -- The dynamic capacity costs `(16/3) q Δ zP ≤ Δ/4`.
      have h16 : q * (zP * (6 * (3 / 4 + 2 * Δ))) = q * (1 - 2 * m) := by rw [hzPmul]
      have h17 : q * zP ≤ 5 / 12 * (53 / 675) :=
        mul_le_mul (by linarith) hzPup hzP0 (by norm_num)
      have h18 : q * zP * Δ ≤ 5 / 12 * (53 / 675) * Δ := mul_le_mul_of_nonneg_right h17 hΔ0
      -- The baseline `1 - 2δm - (4q/9)(1 - 2m)` is decreasing in `m ≥ t - η - r`.
      have h19 : (t - η - r) * (δ - 4 * q / 9) ≤ m * (δ - 4 * q / 9) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h20 : η * δ ≤ η * (5 / 6) := mul_le_mul_of_nonneg_left hδ1 hη
      have h21 : 0 ≤ η * q := mul_nonneg hη hq0
      linarith

/-- The balanced witness parameter of Q `eq:target-cutoff`: the count reaches the
certificate exponent `R_*` with the dynamic loss `Δ/4`. -/
theorem witness_row_count_balanced {Row ι : Type*} [DecidableEq ι]
    (C : Finset Row) (slots : Finset ι) (w g : ι → ℝ) (Qv : ι → Row → ℂ) (M S : Row → ℂ)
    {U δ Δ q r m lam η ν k H wmax : ℝ}
    (hU : 1 < U) (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8)
    (hq0 : 0 ≤ q) (hq1 : q ≤ δ / 2)
    (hqmean : q * ∑ i ∈ slots, w i = ∑ i ∈ slots, w i * g i)
    (hw : ∀ i ∈ slots, 0 < w i) (hg0 : ∀ i ∈ slots, 0 ≤ g i) (hg1 : ∀ i ∈ slots, g i ≤ δ / 2)
    (hwmax : ∀ i ∈ slots, w i ≤ wmax) (hwmax0 : 0 ≤ wmax)
    (hsupply : 7 / 37 ≤ ∑ i ∈ slots, w i)
    (hr0 : 0 ≤ r) (hm0 : 0 ≤ m)
    (hrt : r ≤ balancedCutoff δ (1 / 2 - q / δ) + η)
    (hrmt : balancedCutoff δ (1 / 2 - q / δ) - η ≤ r + m)
    (hlam : 0 ≤ lam) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 100) (hν : 0 < ν) (hν1 : ν ≤ 1 / 100)
    (hk : 0 ≤ k) (hH : 0 ≤ H)
    (hMspike : ∀ u ∈ C, U ^ (δ * r - lam) ≤ ‖M u‖ ^ 2)
    (hSspike : ∀ u ∈ C, U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2)
    (hQspike : ∀ i ∈ slots, 0 < g i → ∀ u ∈ C, U ^ (w i * g i) ≤ ‖Qv i u‖)
    (hI : ∀ I ⊆ slots, r + 2 * ∑ i ∈ I, w i ≤ 1 - 2 * ν →
      2 * r + 8 * ∑ i ∈ I, w i ≤ 3 - 2 * ν →
      ∑ u ∈ C, ‖M u * ∏ i ∈ I, Qv i u‖ ^ 2 ≤ k * U ^ (1 + lam) * H)
    (hIamp : ∑ u ∈ C, ‖M u‖ ^ 2 ≤ k * U ^ (amplifiedInverseExponent r + lam) * H)
    (hP : ∀ I ⊆ slots, 2 * m + 6 * (3 / 4 + 2 * Δ) * ∑ i ∈ I, w i ≤ 1 →
      ∑ u ∈ C, ‖S u ^ 2 * ∏ i ∈ I, Qv i u‖ ^ 2 ≤ k * U ^ (1 + lam) * H)
    (hP0 : ∑ u ∈ C, ‖S u ^ 2‖ ^ 2 ≤ k * U ^ (1 + lam) * H) :
    (C.card : ℝ) ≤ k * U ^ (balancedRowCount δ (1 / 2 - q / δ) + Δ / 4 +
      (3 * lam + δ * wmax + 12 * ν + 4 * η)) * H := by
  have hx0 : 0 ≤ q / δ := div_nonneg hq0 hδ0.le
  have hx1 : q / δ ≤ 1 / 2 := by
    rw [div_le_iff₀ hδ0]
    linarith
  have hy0 : 0 ≤ 1 / 2 - q / δ := by linarith
  have hy1 : 1 / 2 - q / δ ≤ 1 / 2 := by linarith
  obtain ⟨ht1, ht2⟩ := balancedCutoff_mem_Icc hδ0.le hδ1 hy0 hy1
  have h := witness_row_count C slots w g Qv M S hU hδ0 hδ1 hΔ0 hΔ1 hq0 hq1 hqmean hw hg0
    hg1 hwmax hwmax0 hsupply ht1 ht2 hr0 hm0 hrt hrmt hlam hη hη1 hν hν1 hk hH hMspike
    hSspike hQspike hI hIamp hP hP0
  obtain ⟨hD, _⟩ := denominator_bounds hy0 hy1
  obtain ⟨hJ, _⟩ := balanceDenominator_bounds hδ0.le hδ1 hy0 hy1
  rw [shortWitnessCount_balanced (ne_of_gt (by linarith)) (ne_of_gt (by linarith)),
    longWitnessCount_balanced, max_self] at h
  exact h

/-- Q 15438--15445 and M Table 7.3: the unselected count at `t = 1`, using
only the amplified inverse moment and the zero-slot plain moment. -/
theorem witness_row_count_unselected {Row : Type*} (C : Finset Row) (M S : Row → ℂ)
    {U δ r m lam η k H : ℝ}
    (hU : 1 < U) (hδ0 : 0 < δ) (hδ1 : δ ≤ 5 / 6) (_hr0 : 0 ≤ r) (_hm0 : 0 ≤ m)
    (hrt : r ≤ 1 + η) (hrmt : 1 - η ≤ r + m) (hlam : 0 ≤ lam) (hη : 0 ≤ η)
    (hk : 0 ≤ k) (hH : 0 ≤ H)
    (hMspike : ∀ u ∈ C, U ^ (δ * r - lam) ≤ ‖M u‖ ^ 2)
    (hSspike : ∀ u ∈ C, U ^ (δ * m - lam) ≤ ‖S u‖ ^ 2)
    (hIamp : ∑ u ∈ C, ‖M u‖ ^ 2 ≤ k * U ^ (amplifiedInverseExponent r + lam) * H)
    (hP0 : ∑ u ∈ C, ‖S u ^ 2‖ ^ 2 ≤ k * U ^ (1 + lam) * H) :
    (C.card : ℝ) ≤ k * U ^ (1 - 2 * δ / 3 + (3 * lam + 2 * η)) * H := by
  have hU0 : (0 : ℝ) < U := by linarith
  have hAmp : (C.card : ℝ) ≤ k * U ^ (amplifiedInverseExponent r + lam - (δ * r - lam)) * H :=
    card_le_rpow_of_markov C (fun u => ‖M u‖ ^ 2) hU0 hMspike hIamp
  have hZero : (C.card : ℝ) ≤ k * U ^ (1 + lam - 2 * (δ * m - lam)) * H :=
    card_le_rpow_of_markov C (fun u => ‖S u ^ 2‖ ^ 2) hU0
      (fun u hu => plain_lower S hU0 u (hSspike u hu)) hP0
  rcases lt_or_ge 1 r with hr1 | hr1
  · -- `r > 1`: amplified moment, `1/6 + (5/6 - δ) r ≤ 1 - δ + η`.
    have he : amplifiedInverseExponent r = (1 + 5 * r) / 6 := by
      unfold amplifiedInverseExponent
      exact max_eq_right (by linarith)
    rw [he] at hAmp
    refine card_le_rpow_mono hU.le hk hH hAmp ?_
    have h1 : (5 / 6 - δ) * r ≤ (5 / 6 - δ) * (1 + η) :=
      mul_le_mul_of_nonneg_left hrt (by linarith)
    have h2 : 0 ≤ δ * η := mul_nonneg hδ0.le hη
    linarith
  rcases lt_or_ge r (2 / 3) with hr23 | hr23
  · -- `r < 2/3`: zero-slot plain moment with `m ≥ 1/3 - η`.
    refine card_le_rpow_mono hU.le hk hH hZero ?_
    have h1 : δ * (1 / 3 - η) ≤ δ * m := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    have h2 : δ * η ≤ 5 / 6 * η := mul_le_mul_of_nonneg_right hδ1 hη
    linarith
  · -- `2/3 ≤ r ≤ 1`: amplified moment with `e(r) = 1`.
    have he : amplifiedInverseExponent r = 1 := by
      unfold amplifiedInverseExponent
      exact max_eq_left (by linarith)
    rw [he] at hAmp
    refine card_le_rpow_mono hU.le hk hH hAmp ?_
    have h1 : δ * (2 / 3) ≤ δ * r := mul_le_mul_of_nonneg_left hr23 hδ0.le
    linarith

end HeckeGeneral.Analysis
