import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

/-!
Whole-slot selection for the equal logarithmic windows used in M.
The loss is one slot times the amplitude ceiling; zero-amplitude slots
are removed. No analytic witness or moment estimate is assumed here.
-/

noncomputable section
namespace HeckeGeneral.Analysis

open scoped Classical BigOperators

theorem exists_subset_sum_ge_average {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    (k : ℕ) (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧
      (k : ℝ) * (∑ i ∈ S, g i) ≤ (S.card : ℝ) * (∑ i ∈ T, g i) := by
  classical
  obtain ⟨T, hT, hmax⟩ := (S.powersetCard k).exists_max_image
    (fun T => ∑ i ∈ T, g i) (Finset.powersetCard_nonempty.mpr hk)
  obtain ⟨hTS, hTk⟩ := Finset.mem_powersetCard.mp hT
  have horder : ∀ i ∈ T, ∀ j ∈ S \ T, g j ≤ g i := by
    intro i hi j hj
    obtain ⟨hjS, hjT⟩ := Finset.mem_sdiff.mp hj
    have hjE : j ∉ T.erase i := fun h => hjT (Finset.mem_of_mem_erase h)
    have hswap : insert j (T.erase i) ∈ S.powersetCard k := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.insert_subset hjS ((Finset.erase_subset _ _).trans hTS), ?_⟩
      rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hi]
      have : 0 < T.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hm := hmax (insert j (T.erase i)) hswap
    rw [Finset.sum_insert hjE] at hm
    have he := Finset.sum_erase_add T g hi
    linarith
  have hpairs :
      (T.card : ℝ) * (∑ j ∈ S \ T, g j) ≤
      ((S \ T).card : ℝ) * (∑ i ∈ T, g i) := by
    have h := Finset.sum_le_sum (s := T) (fun i hi =>
      Finset.sum_le_sum (s := S \ T) (fun j hj => horder i hi j hj))
    simpa [Finset.sum_mul, Finset.mul_sum] using h
  have hsum := Finset.sum_sdiff hTS (f := g)
  have hcard : ((S \ T).card : ℝ) + (T.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hTS
  refine ⟨T, hTS, hTk, ?_⟩
  rw [← hTk]
  calc
    _ = (T.card : ℝ) * (∑ j ∈ S \ T, g j) +
        (T.card : ℝ) * (∑ i ∈ T, g i) := by rw [← hsum, mul_add]
    _ ≤ ((S \ T).card : ℝ) * (∑ i ∈ T, g i) +
        (T.card : ℝ) * (∑ i ∈ T, g i) := add_le_add hpairs le_rfl
    _ = _ := by rw [← add_mul, hcard]

/-- For equal slot length w and amplitudes in [0,G], one may retain only
whole positive slots of total length at most z. Rounding costs at most Gw.
The average q is that of ALL slots, including the zero ones. -/
theorem exists_equal_slot_selection {ι : Type*}
    (S : Finset ι) (g : ι → ℝ) (hne : S.Nonempty)
    {w G q z : ℝ} (hw : 0 < w)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ G)
    (hmean : ∑ i ∈ S, g i = (S.card : ℝ) * q)
    (hz : 0 ≤ z) (hzhi : z ≤ (S.card : ℝ) * w) :
    ∃ T ⊆ S, (∀ i ∈ T, 0 < g i) ∧
      (T.card : ℝ) * w ≤ z ∧ q * z - G * w ≤ w * ∑ i ∈ T, g i := by
  classical
  have hn : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hq0 : 0 ≤ q := by
    have hsum : 0 ≤ ∑ i ∈ S, g i := Finset.sum_nonneg (fun i hi => (hg i hi).1)
    rw [hmean] at hsum
    exact nonneg_of_mul_nonneg_right hsum hn
  have hqG : q ≤ G := by
    have hsum : ∑ i ∈ S, g i ≤ (S.card : ℝ) * G := by
      calc
        _ ≤ ∑ _i ∈ S, G := Finset.sum_le_sum (fun i hi => (hg i hi).2)
        _ = _ := by simp
    rw [hmean] at hsum
    exact (mul_le_mul_iff_right₀ hn).mp hsum
  let k := Nat.floor (z / w)
  have hk : k ≤ S.card := Nat.floor_le_of_le ((div_le_iff₀ hw).mpr (by nlinarith))
  have hkw : (k : ℝ) * w ≤ z :=
    (le_div_iff₀ hw).mp (Nat.floor_le (div_nonneg hz hw.le))
  have hzw : z < ((k : ℝ) + 1) * w :=
    (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one (z / w))
  obtain ⟨T, hTS, hTk, havg⟩ := exists_subset_sum_ge_average S g k hk
  have hgain : (k : ℝ) * q ≤ ∑ i ∈ T, g i := by
    rw [hmean] at havg
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith only [havg]
  let U := T.filter fun i => 0 < g i
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hsumU : ∑ i ∈ U, g i = ∑ i ∈ T, g i := by
    apply Finset.sum_subset hUT
    intro i hi hnot
    have hg0 := (hg i (hTS hi)).1
    have hnotpos : ¬0 < g i := fun h => hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
    linarith
  refine ⟨U, hUT.trans hTS, (fun i hi => (Finset.mem_filter.mp hi).2), ?_, ?_⟩
  · calc
      (U.card : ℝ) * w ≤ (T.card : ℝ) * w :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hUT) hw.le
      _ = (k : ℝ) * w := by rw [hTk]
      _ ≤ z := hkw
  · rw [hsumU]
    calc
      q * z - G * w ≤ q * (((k : ℝ) + 1) * w) - G * w :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hzw.le hq0) _
      _ = w * ((k : ℝ) * q) + (q - G) * w := by ring
      _ ≤ w * (∑ i ∈ T, g i) + 0 := add_le_add
        (mul_le_mul_of_nonneg_left hgain hw.le)
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqG) hw.le)
      _ = _ := add_zero _

/-- The literal squared-product threshold used by the moments. At G=δ/2
the exponent is 2qz-δw, exactly the single-slot loss in the source. -/
theorem exists_equal_slot_product_witness {ι : Type*}
    (S : Finset ι) (g : ι → ℝ) (Q : ι → ℂ) (hne : S.Nonempty)
    {w G q z U : ℝ} (hw : 0 < w) (hU : 1 ≤ U)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ G)
    (hmean : ∑ i ∈ S, g i = (S.card : ℝ) * q)
    (hz : 0 ≤ z) (hzhi : z ≤ (S.card : ℝ) * w)
    (hQ : ∀ i ∈ S, 0 < g i → U ^ (w * g i) ≤ ‖Q i‖) :
    ∃ T ⊆ S, (∀ i ∈ T, 0 < g i) ∧ (T.card : ℝ) * w ≤ z ∧
      U ^ (2 * q * z - 2 * G * w) ≤ ‖∏ i ∈ T, Q i‖ ^ 2 := by
  obtain ⟨T, hTS, hpos, hlen, hgain⟩ :=
    exists_equal_slot_selection S g hne hw hg hmean hz hzhi
  refine ⟨T, hTS, hpos, hlen, ?_⟩
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hprod : U ^ (w * ∑ i ∈ T, g i) ≤ ‖∏ i ∈ T, Q i‖ := by
    rw [norm_prod]
    calc
      _ = ∏ i ∈ T, U ^ (w * g i) := by
        rw [Finset.mul_sum, Real.rpow_sum_of_pos hUpos]
      _ ≤ _ := Finset.prod_le_prod₀
        (fun i _ => (Real.rpow_pos_of_pos hUpos _).le)
        (fun i hi => hQ i (hTS hi) (hpos i hi))
  calc
    U ^ (2 * q * z - 2 * G * w) ≤ U ^ ((w * ∑ i ∈ T, g i) * 2) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    _ = (U ^ (w * ∑ i ∈ T, g i)) ^ (2 : ℕ) := by
      rw [Real.rpow_mul hUpos.le, Real.rpow_two]
    _ ≤ ‖∏ i ∈ T, Q i‖ ^ 2 :=
      (sq_le_sq₀ (Real.rpow_nonneg hUpos.le _) (norm_nonneg _)).mpr hprod

end HeckeGeneral.Analysis
