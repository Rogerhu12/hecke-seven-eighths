import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log

/-!
Pure real-analysis lemmas for GR-12-ASSEMBLY: dyadic shell decomposition of a
finite sum indexed by norms `n i ≥ 1`, and the doubling-sequence geometric sums.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.GramAssembly.Dyadic

open scoped BigOperators

/-- The dyadic shell index of `x ≥ 1`: `x ∈ (2^k/2, 2^k]`. -/
def shellIndex (x : ℝ) : ℕ := Nat.clog 2 ⌈x⌉₊

theorem le_two_pow_shellIndex {x : ℝ} (hx : 1 ≤ x) : x ≤ (2 : ℝ) ^ shellIndex x := by
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : ⌈x⌉₊ ≤ 2 ^ shellIndex x := Nat.le_pow_clog (by norm_num) _
  calc x ≤ (⌈x⌉₊ : ℝ) := h1
    _ ≤ ((2 ^ shellIndex x : ℕ) : ℝ) := by exact_mod_cast h2
    _ = (2 : ℝ) ^ shellIndex x := by push_cast; ring

theorem half_two_pow_shellIndex_lt {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ shellIndex x / 2 < x := by
  set m := ⌈x⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    intro h; have := Nat.ceil_eq_zero.mp h; linarith)
  by_cases hm2 : m = 1
  · have : shellIndex x = 0 := by simp [shellIndex, ← hm, hm2]
    rw [this]; norm_num; linarith
  · have hlt : 1 < m := lt_of_le_of_ne hm1 (Ne.symm hm2)
    have hk : shellIndex x = Nat.clog 2 m := rfl
    have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) hlt
    have h3 : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) hlt
    have h4 : (m : ℝ) - 1 < x := by
      have := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
      linarith
    have h5 : ((2 ^ (Nat.clog 2 m - 1) : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h3
    rw [hk]
    have h6 : (2 : ℝ) ^ Nat.clog 2 m / 2 = ((2 ^ (Nat.clog 2 m - 1) : ℕ) : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 m = j + 1 := ⟨Nat.clog 2 m - 1, by omega⟩
      rw [hj]; push_cast; simp [pow_succ]
    rw [h6]
    linarith

/-- Dyadic shell decomposition of a finite sum. -/
theorem shell_sum_le {ι : Type*} (F : Finset ι) (n : ι → ℝ) (hn : ∀ i ∈ F, 1 ≤ n i)
    (w : ℝ → ℝ) (cnt W : ℕ → ℝ)
    (hcnt : ∀ (k : ℕ) (G : Finset ι), G ⊆ F → (∀ i ∈ G, n i ≤ (2 : ℝ) ^ k) →
      (G.card : ℝ) ≤ cnt k)
    (hW : ∀ (k : ℕ) (x : ℝ), 1 ≤ x → (2 : ℝ) ^ k / 2 < x → x ≤ (2 : ℝ) ^ k → w x ≤ W k)
    (hW0 : ∀ k, 0 ≤ W k) (M : ℕ) (hM : ∀ i ∈ F, shellIndex (n i) < M) :
    ∑ i ∈ F, w (n i) ≤ ∑ k ∈ Finset.range M, cnt k * W k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := Finset.range M)
    (g := fun i => shellIndex (n i)) (fun i hi => Finset.mem_range.mpr (hM i hi))]
  apply Finset.sum_le_sum
  intro k _
  have hG : ∀ i ∈ F.filter (fun i => shellIndex (n i) = k), w (n i) ≤ W k := by
    intro i hi
    rw [Finset.mem_filter] at hi
    apply hW k _ (hn i hi.1)
    · rw [← hi.2]; exact half_two_pow_shellIndex_lt (hn i hi.1)
    · rw [← hi.2]; exact le_two_pow_shellIndex (hn i hi.1)
  calc ∑ i ∈ F.filter (fun i => shellIndex (n i) = k), w (n i)
      ≤ ∑ i ∈ F.filter (fun i => shellIndex (n i) = k), W k := Finset.sum_le_sum hG
    _ = (F.filter (fun i => shellIndex (n i) = k)).card * W k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ cnt k * W k := by
        apply mul_le_mul_of_nonneg_right _ (hW0 k)
        apply hcnt k _ (Finset.filter_subset _ _)
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [← hi.2]; exact le_two_pow_shellIndex (hn i hi.1)


section Doubling

variable (y0 : ℝ)

private def yy (k : ℕ) : ℝ := y0 * (2 : ℝ) ^ k

private theorem yy_succ (k : ℕ) : yy y0 (k + 1) = 2 * yy y0 k := by
  unfold yy; ring

private theorem yy_pos (hy0 : 0 < y0) (k : ℕ) : 0 < yy y0 k := by
  unfold yy; positivity

/-- The part of a doubling sequence below one. -/
private def lowSum (p : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, if yy y0 k ≤ 1 then (yy y0 k) ^ p else 0

private theorem lowSum_bound (p : ℝ) (hp : 0 < p) (hy0 : 0 < y0) (M : ℕ) :
    (yy y0 M ≤ 1 → lowSum y0 p M ≤ (1 / ((2 : ℝ) ^ p - 1)) * (yy y0 M) ^ p) ∧
      lowSum y0 p M ≤ 1 / ((2 : ℝ) ^ p - 1) + 1 := by
  have h2p : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
  have hc : 0 < 1 / ((2 : ℝ) ^ p - 1) := by apply div_pos one_pos; linarith
  have hne : (2 : ℝ) ^ p - 1 ≠ 0 := by linarith
  have hc1 : 1 / ((2 : ℝ) ^ p - 1) + 1 = (1 / ((2 : ℝ) ^ p - 1)) * 2 ^ p := by
    field_simp; ring
  induction M with
  | zero =>
    refine ⟨fun _ => ?_, ?_⟩
    · simp only [lowSum, Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg hc.le (Real.rpow_nonneg (yy_pos y0 hy0 0).le _)
    · simp only [lowSum, Finset.range_zero, Finset.sum_empty]
      linarith
  | succ M ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos := yy_pos y0 hy0 M
    have hsucc : lowSum y0 p (M + 1) = lowSum y0 p M + if yy y0 M ≤ 1 then (yy y0 M) ^ p else 0 := by
      simp [lowSum, Finset.sum_range_succ]
    constructor
    · intro hle
      have hle' : yy y0 M ≤ 1 := by rw [yy_succ] at hle; linarith
      rw [hsucc, if_pos hle', yy_succ, Real.mul_rpow (by norm_num) hpos.le]
      have := ih1 hle'
      have hyp : 0 ≤ (yy y0 M) ^ p := Real.rpow_nonneg hpos.le _
      nlinarith
    · rw [hsucc]
      by_cases hle : yy y0 M ≤ 1
      · rw [if_pos hle]
        have := ih1 hle
        have hyp : (yy y0 M) ^ p ≤ 1 := Real.rpow_le_one hpos.le hle hp.le
        have hyp0 : 0 ≤ (yy y0 M) ^ p := Real.rpow_nonneg hpos.le _
        nlinarith
      · rw [if_neg hle]; linarith

/-- The part of a doubling sequence above one. -/
private def highSum (q : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, if 1 < yy y0 k then (yy y0 k) ^ (-q) else 0

private theorem highSum_bound (q : ℝ) (hq : 0 < q) (hy0 : 0 < y0) (M : ℕ) :
    highSum y0 q M + (1 / (1 - (2 : ℝ) ^ (-q))) *
        (if 1 < yy y0 M then (yy y0 M) ^ (-q) else 0) ≤ 1 / (1 - (2 : ℝ) ^ (-q)) ∧
      (yy y0 M ≤ 1 → highSum y0 q M = 0) := by
  have h2q : (2 : ℝ) ^ (-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h2q0 : 0 < (2 : ℝ) ^ (-q) := by positivity
  have hd : 0 < 1 - (2 : ℝ) ^ (-q) := by linarith
  induction M with
  | zero =>
    have hy : yy y0 0 = y0 := by simp [yy]
    refine ⟨?_, fun _ => by simp [highSum]⟩
    simp only [highSum, Finset.range_zero, Finset.sum_empty, zero_add]
    split_ifs with h
    · rw [hy] at h ⊢
      have : y0 ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
      calc 1 / (1 - (2 : ℝ) ^ (-q)) * y0 ^ (-q) ≤ 1 / (1 - (2 : ℝ) ^ (-q)) * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := mul_one _
    · simp only [mul_zero]; exact div_nonneg zero_le_one hd.le
  | succ M ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos := yy_pos y0 hy0 M
    have hsucc : highSum y0 q (M + 1) = highSum y0 q M + if 1 < yy y0 M then (yy y0 M) ^ (-q) else 0 := by
      simp [highSum, Finset.sum_range_succ]
    constructor
    · rw [hsucc, yy_succ]
      by_cases hle : 1 < yy y0 M
      · have hle2 : 1 < 2 * yy y0 M := by linarith
        rw [if_pos hle, if_pos hle2, Real.mul_rpow (by norm_num) hpos.le]
        rw [if_pos hle] at ih1
        have hyq : 0 ≤ (yy y0 M) ^ (-q) := Real.rpow_nonneg hpos.le _
        have key : (1 / (1 - (2 : ℝ) ^ (-q))) * (2 ^ (-q) * (yy y0 M) ^ (-q)) + (yy y0 M) ^ (-q)
            = (1 / (1 - (2 : ℝ) ^ (-q))) * (yy y0 M) ^ (-q) := by
          field_simp; ring
        nlinarith [key]
      · have hle0 : yy y0 M ≤ 1 := not_lt.mp hle
        have hH0 := ih2 hle0
        rw [if_neg hle, hH0]
        have : (if 1 < 2 * yy y0 M then (2 * yy y0 M) ^ (-q) else 0) ≤ 1 := by
          split_ifs with h
          · exact Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
          · norm_num
        simp only [add_zero, zero_add]
        calc 1 / (1 - (2 : ℝ) ^ (-q)) * (if 1 < 2 * yy y0 M then (2 * yy y0 M) ^ (-q) else 0)
            ≤ 1 / (1 - (2 : ℝ) ^ (-q)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := mul_one _
    · intro hle
      rw [yy_succ] at hle
      have hM : yy y0 M ≤ 1 := by linarith
      have hH0 := ih2 hM
      rw [hsucc, hH0, if_neg (not_lt.mpr hM)]; simp

/-- The geometric sum of `min (y^p) (y^(-q))` along a doubling sequence. -/
theorem doubling_sum_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hy0 : 0 < y0) (M : ℕ) :
    ∑ k ∈ Finset.range M, min ((y0 * (2 : ℝ) ^ k) ^ p) ((y0 * (2 : ℝ) ^ k) ^ (-q)) ≤
      (1 / ((2 : ℝ) ^ p - 1) + 1) + 1 / (1 - (2 : ℝ) ^ (-q)) := by
  have hle : ∀ k, min ((y0 * (2 : ℝ) ^ k) ^ p) ((y0 * (2 : ℝ) ^ k) ^ (-q)) ≤
      (if yy y0 k ≤ 1 then (yy y0 k) ^ p else 0) + (if 1 < yy y0 k then (yy y0 k) ^ (-q) else 0) := by
    intro k
    have hk : yy y0 k = y0 * (2 : ℝ) ^ k := rfl
    have hpos := yy_pos y0 hy0 k
    by_cases h : yy y0 k ≤ 1
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero, ← hk]
      exact min_le_left _ _
    · rw [if_neg h, if_pos (not_le.mp h), zero_add, ← hk]
      exact min_le_right _ _
  have h1 := (lowSum_bound y0 p hp hy0 M).2
  have h2 := highSum_bound y0 q hq hy0 M
  have h3 : 0 ≤ (1 / (1 - (2 : ℝ) ^ (-q))) * (if 1 < yy y0 M then (yy y0 M) ^ (-q) else 0) := by
    have : (2 : ℝ) ^ (-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hyq : 0 ≤ (if 1 < yy y0 M then (yy y0 M) ^ (-q) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg (yy_pos y0 hy0 M).le _
      · exact le_rfl
    exact mul_nonneg (by apply div_nonneg zero_le_one; linarith) hyq
  calc _ ≤ ∑ k ∈ Finset.range M, ((if yy y0 k ≤ 1 then (yy y0 k) ^ p else 0) +
        (if 1 < yy y0 k then (yy y0 k) ^ (-q) else 0)) := Finset.sum_le_sum (fun k _ => hle k)
    _ = lowSum y0 p M + highSum y0 q M := by
        rw [Finset.sum_add_distrib]; rfl
    _ ≤ _ := by linarith [h2.1]

end Doubling


section Series

/-- The scalar profile of the residual bounds, for `σ = 1/12`, `β = 5`, scale `a`. -/
def mfun (a x : ℝ) : ℝ := min ((x / a) ^ (-(1 / 12 : ℝ))) ((x / a) ^ (-(5 : ℝ)))

theorem mfun_nonneg (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : 0 ≤ mfun a x := by
  unfold mfun
  exact le_min (Real.rpow_nonneg (div_pos hx ha).le _) (Real.rpow_nonneg (div_pos hx ha).le _)

theorem mfun_antitone (a : ℝ) (ha : 0 < a) {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') :
    mfun a x' ≤ mfun a x := by
  unfold mfun
  have h1 : 0 < x / a := div_pos hx ha
  have h2 : x / a ≤ x' / a := div_le_div_of_nonneg_right hxx ha.le
  apply min_le_min
  · exact Real.rpow_le_rpow_of_nonpos h1 h2 (by norm_num)
  · exact Real.rpow_le_rpow_of_nonpos h1 h2 (by norm_num)

/-- The constant of the exceptional dyadic series. -/
def Ke : ℝ :=
  ((1 / ((2 : ℝ) ^ (1 / 12 : ℝ) - 1) + 1) + 1 / (1 - (2 : ℝ) ^ (-(29 / 6 : ℝ)))) *
    (2 : ℝ) ^ (1 / 6 : ℝ)

theorem exceptional_series (a : ℝ) (ha : 0 < a) (M : ℕ) :
    ∑ k ∈ Finset.range M, mfun a ((2 : ℝ) ^ k / 2) * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ) ≤
      Ke * a ^ (1 / 6 : ℝ) := by
  have hy0 : 0 < 1 / (2 * a) := by positivity
  have hterm : ∀ k : ℕ, mfun a ((2 : ℝ) ^ k / 2) * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ) =
      (2 * a) ^ (1 / 6 : ℝ) *
        min (((1 / (2 * a)) * (2 : ℝ) ^ k) ^ (1 / 12 : ℝ))
          (((1 / (2 * a)) * (2 : ℝ) ^ k) ^ (-(29 / 6 : ℝ))) := by
    intro k
    set y : ℝ := (1 / (2 * a)) * (2 : ℝ) ^ k with hy
    have hypos : 0 < y := by positivity
    have hx : (2 : ℝ) ^ k / 2 / a = y := by rw [hy]; field_simp
    have h2k : ((2 : ℝ) ^ k) = (2 * a) * y := by rw [hy]; field_simp
    unfold mfun
    have e1 : y ^ (-(1 / 12 : ℝ)) * y ^ (1 / 6 : ℝ) = y ^ (1 / 12 : ℝ) := by
      rw [← Real.rpow_add hypos]; norm_num
    have e2 : y ^ (-(5 : ℝ)) * y ^ (1 / 6 : ℝ) = y ^ (-(29 / 6 : ℝ)) := by
      rw [← Real.rpow_add hypos]; norm_num
    rw [hx, h2k, Real.mul_rpow (by positivity) hypos.le]
    calc min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * ((2 * a) ^ (1 / 6 : ℝ) * y ^ (1 / 6 : ℝ))
        = (2 * a) ^ (1 / 6 : ℝ) * (min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * y ^ (1 / 6 : ℝ)) := by
          ring
      _ = (2 * a) ^ (1 / 6 : ℝ) * min (y ^ (1 / 12 : ℝ)) (y ^ (-(29 / 6 : ℝ))) := by
          rw [min_mul_of_nonneg _ _ (Real.rpow_nonneg hypos.le _), e1, e2]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hd := doubling_sum_le (1 / (2 * a)) (1 / 12) (29 / 6) (by norm_num) (by norm_num) hy0 M
  have h2a : (2 * a) ^ (1 / 6 : ℝ) = (2 : ℝ) ^ (1 / 6 : ℝ) * a ^ (1 / 6 : ℝ) :=
    Real.mul_rpow (by norm_num) ha.le
  rw [h2a]
  unfold Ke
  have hnn : 0 ≤ (2 : ℝ) ^ (1 / 6 : ℝ) * a ^ (1 / 6 : ℝ) := by positivity
  calc (2 : ℝ) ^ (1 / 6 : ℝ) * a ^ (1 / 6 : ℝ) * _ ≤ (2 : ℝ) ^ (1 / 6 : ℝ) * a ^ (1 / 6 : ℝ) * _ :=
        mul_le_mul_of_nonneg_left hd hnn
    _ = _ := by ring

end Series


section Ordinary

theorem min_one_mul_pow_le (t y : ℝ) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    min 1 ((t * y) ^ 3) ≤ min 1 (t ^ 3) * max 1 (y ^ 3) := by
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy 3
  by_cases h : 1 ≤ t ^ 3
  · rw [min_eq_left h, one_mul]
    exact (min_le_left _ _).trans (le_max_left _ _)
  · rw [min_eq_right (not_le.mp h).le]
    calc min 1 ((t * y) ^ 3) ≤ (t * y) ^ 3 := min_le_right _ _
      _ = t ^ 3 * y ^ 3 := by ring
      _ ≤ t ^ 3 * max 1 (y ^ 3) := mul_le_mul_of_nonneg_left (le_max_right _ _) ht3

theorem ordinary_profile_le (y : ℝ) (hy : 0 < y) :
    y * min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * max 1 (y ^ 3) ≤
      min (y ^ (11 / 12 : ℝ)) (y ^ (-(1 : ℝ))) := by
  have h3 : y ^ ((3 : ℕ) : ℝ) = y ^ 3 := Real.rpow_natCast y 3
  by_cases h : y ≤ 1
  · have hy3 : y ^ 3 ≤ 1 := pow_le_one₀ hy.le h
    rw [max_eq_left hy3, mul_one]
    have h1 : y * min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) ≤ y ^ (11 / 12 : ℝ) := by
      calc y * min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) ≤ y * y ^ (-(1 / 12 : ℝ)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hy.le
        _ = y ^ (11 / 12 : ℝ) := by
            have := Real.rpow_add hy 1 (-(1 / 12 : ℝ))
            rw [Real.rpow_one] at this
            rw [← this]; norm_num
    refine le_min h1 (h1.trans ?_)
    exact Real.rpow_le_rpow_of_exponent_ge hy h (by norm_num)
  · have h1 : 1 < y := not_le.mp h
    have hy3 : 1 ≤ y ^ 3 := one_le_pow₀ h1.le
    rw [max_eq_right hy3]
    have e : y * y ^ (-(5 : ℝ)) * y ^ 3 = y ^ (-(1 : ℝ)) := by
      have h3' : y ^ (3 : ℝ) = y ^ 3 := by simpa using h3
      have a1 := Real.rpow_add hy 1 (-(5 : ℝ))
      have a2 := Real.rpow_add hy (1 + -(5 : ℝ)) 3
      rw [Real.rpow_one] at a1
      rw [← h3', ← a1, ← a2]; norm_num
    have hle : y * min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * y ^ 3 ≤ y ^ (-(1 : ℝ)) := by
      rw [← e]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy.le 3)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hy.le
    refine le_min ((hle.trans ?_)) hle
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)

/-- The constant of the ordinary dyadic series. -/
def Ko : ℝ :=
  16 * ((1 / ((2 : ℝ) ^ (11 / 12 : ℝ) - 1) + 1) + 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ))))

theorem Ko_nonneg : 0 ≤ Ko := by
  unfold Ko
  have h1 : (1 : ℝ) < 2 ^ (11 / 12 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have : 0 ≤ 1 / ((2 : ℝ) ^ (11 / 12 : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  have : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ))) := div_nonneg zero_le_one (by linarith)
  positivity

theorem ordinary_series (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (M : ℕ) :
    ∑ k ∈ Finset.range M, (2 : ℝ) ^ k * (mfun a ((2 : ℝ) ^ k / 2) *
        min 1 (((2 : ℝ) ^ k / N) ^ 3)) ≤
      Ko * a * min 1 ((a / N) ^ 3) := by
  have hy0 : 0 < 1 / (2 * a) := by positivity
  set t : ℝ := 2 * a / N with ht
  have ht0 : 0 ≤ t := by positivity
  have hterm : ∀ k : ℕ, (2 : ℝ) ^ k * (mfun a ((2 : ℝ) ^ k / 2) *
        min 1 (((2 : ℝ) ^ k / N) ^ 3)) ≤
      (2 * a) * min 1 (t ^ 3) *
        min (((1 / (2 * a)) * (2 : ℝ) ^ k) ^ (11 / 12 : ℝ))
          (((1 / (2 * a)) * (2 : ℝ) ^ k) ^ (-(1 : ℝ))) := by
    intro k
    set y : ℝ := (1 / (2 * a)) * (2 : ℝ) ^ k with hy
    have hypos : 0 < y := by positivity
    have hx : (2 : ℝ) ^ k / 2 / a = y := by rw [hy]; field_simp
    have h2k : ((2 : ℝ) ^ k) = (2 * a) * y := by rw [hy]; field_simp
    have hdiv : ((2 : ℝ) ^ k / N) = t * y := by rw [h2k, ht]; field_simp
    unfold mfun
    rw [hx, hdiv, h2k]
    have hA := min_one_mul_pow_le t y ht0 hypos.le
    have hB := ordinary_profile_le y hypos
    have hm : 0 ≤ min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) :=
      le_min (Real.rpow_nonneg hypos.le _) (Real.rpow_nonneg hypos.le _)
    calc (2 * a) * y * (min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * min 1 ((t * y) ^ 3))
        ≤ (2 * a) * y * (min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) *
            (min 1 (t ^ 3) * max 1 (y ^ 3))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hA hm
      _ = (2 * a) * min 1 (t ^ 3) *
            (y * min (y ^ (-(1 / 12 : ℝ))) (y ^ (-(5 : ℝ))) * max 1 (y ^ 3)) := by ring
      _ ≤ (2 * a) * min 1 (t ^ 3) * min (y ^ (11 / 12 : ℝ)) (y ^ (-(1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  refine (Finset.sum_le_sum (fun k _ => hterm k)).trans ?_
  rw [← Finset.mul_sum]
  have hd := doubling_sum_le (1 / (2 * a)) (11 / 12) 1 (by norm_num) (by norm_num) hy0 M
  have hmin : min 1 (t ^ 3) ≤ 8 * min 1 ((a / N) ^ 3) := by
    have : t ^ 3 = 8 * (a / N) ^ 3 := by rw [ht]; field_simp; ring
    rw [this]
    have hn : 0 ≤ (a / N) ^ 3 := by positivity
    by_cases h : 1 ≤ (a / N) ^ 3
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right (not_le.mp h).le]
      exact (min_le_right _ _)
  unfold Ko
  have hnn : 0 ≤ 2 * a * min 1 (t ^ 3) := by positivity
  calc (2 * a) * min 1 (t ^ 3) * _ ≤ (2 * a) * min 1 (t ^ 3) * ((1 / ((2 : ℝ) ^ (11 / 12 : ℝ) - 1) + 1) + 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hd hnn
    _ ≤ (2 * a) * (8 * min 1 ((a / N) ^ 3)) * ((1 / ((2 : ℝ) ^ (11 / 12 : ℝ) - 1) + 1) + 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hmin (by positivity)
        · have h1 : (1 : ℝ) < 2 ^ (11 / 12 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
          have h2 : (2 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
          have : 0 ≤ 1 / ((2 : ℝ) ^ (11 / 12 : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
          have : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ))) := div_nonneg zero_le_one (by linarith)
          linarith
    _ = _ := by ring

end Ordinary

end HeckeSkeleton.GramAssembly.Dyadic
