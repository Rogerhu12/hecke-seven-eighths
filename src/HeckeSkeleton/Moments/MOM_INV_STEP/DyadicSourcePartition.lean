module

public import DedekindZetaZeroFree.Analysis.DyadicLengthBounds
public import Mathlib.Tactic

/-!
# Fixed dyadic centers for the actual source

The finite index type is fixed by the base, one uniform length cap and the
annular slack. Its centers do not contain an extracted ideal, final row,
label, coefficient or Mellin frequency. Actual source values merely select
a fiber of this predetermined finite partition.

One fiber gives a ratio in [1,2]. Two independent fibers give a product
ratio in [1,4]. Both exact finite regrouping identities and arbitrary
small-power bounds for the number of bins are proved below.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.DyadicSourcePartition

open DedekindZetaZeroFree.LargeSieve.Vendor
open scoped Classical BigOperators NumberField

/-- This index type is fixed before any source ideal, row or label. -/
abbrev Index (Z lengthCap eta : ℝ) :=
  Fin (dyadicLength (Z ^ (lengthCap + eta)) + 1)

/-- The lower center of the j-th dyadic interval; the unit interval is
included without inventing a norm below one. -/
def center (j : ℕ) : ℝ := max 1 ((2 : ℝ) ^ j / 2)

theorem one_le_center (j : ℕ) : 1 ≤ center j := le_max_left _ _
theorem center_pos (j : ℕ) : 0 < center j := zero_lt_one.trans_le (one_le_center j)

theorem exists_dyadic_index (Y v : ℝ) (hv : 1 ≤ v) (hY : v ≤ Y) :
    ∃ j : Fin (dyadicLength Y + 1),
      (2 : ℝ) ^ j.val / 2 < v ∧ v ≤ (2 : ℝ) ^ j.val := by
  have hex : ∃ j : ℕ, v ≤ (2 : ℝ) ^ j :=
    ⟨dyadicLength Y, hY.trans (dyadicLength_cover Y)⟩
  let j := Nat.find hex
  have hj : v ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ dyadicLength Y := Nat.find_min' hex
    (hY.trans (dyadicLength_cover Y))
  refine ⟨⟨j, by omega⟩, ?_, hj⟩
  change (2 : ℝ) ^ j / 2 < v
  have hjfind : j = Nat.find hex := rfl
  rcases hjj : j with _ | k
  · norm_num
    linarith
  · have hprev : ¬ v ≤ (2 : ℝ) ^ k := Nat.find_min hex (by omega)
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      lt_of_not_ge hprev

def boundedLabel (Y v : ℝ) : Fin (dyadicLength Y + 1) :=
  if h : 1 ≤ v ∧ v ≤ Y then (exists_dyadic_index Y v h.1 h.2).choose
  else ⟨0, by omega⟩

def label (Z lengthCap eta v : ℝ) : Index Z lengthCap eta :=
  boundedLabel (Z ^ (lengthCap + eta)) v

theorem label_bounds (Z lengthCap eta v : ℝ)
    (hv : 1 ≤ v) (hcap : v ≤ Z ^ (lengthCap + eta)) :
    center (label Z lengthCap eta v).val ≤ v ∧
      v ≤ 2 * center (label Z lengthCap eta v).val := by
  have hb :
      (2 : ℝ) ^ (label Z lengthCap eta v).val / 2 < v ∧
      v ≤ (2 : ℝ) ^ (label Z lengthCap eta v).val := by
    unfold label boundedLabel
    rw [dif_pos ⟨hv, hcap⟩]
    exact (exists_dyadic_index _ _ hv hcap).choose_spec
  refine ⟨max_le hv hb.1.le, ?_⟩
  have hm := le_max_right (1 : ℝ) ((2 : ℝ) ^ (label Z lengthCap eta v).val / 2)
  change (2 : ℝ) ^ (label Z lengthCap eta v).val / 2 ≤
    center (label Z lengthCap eta v).val at hm
  linarith [hb.2]

/-- A source window of length at most `L` controls the product of an
extracted factor and an overlap divisor. The grid parameters are fixed
before either of these actual ideals is selected. -/
theorem quadratic_source_cap (Z L eta X v : ℝ) (hZ : 0 < Z)
    (hwidth : 2 ≤ Z ^ eta) (hX0 : 0 ≤ X) (hX : X ≤ Z ^ L)
    (hv : v ≤ (2 * X) ^ 2) :
    v ≤ Z ^ (2 * L + 2 * eta) := by
  have hx : 2 * X ≤ Z ^ eta * Z ^ L :=
    mul_le_mul hwidth hX hX0 (Real.rpow_nonneg hZ.le eta)
  calc
    v ≤ (2 * X) ^ 2 := hv
    _ ≤ (Z ^ eta * Z ^ L) ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
    _ = Z ^ (2 * L + 2 * eta) := by
      rw [← Real.rpow_add hZ, ← Real.rpow_natCast,
        ← Real.rpow_mul hZ.le]
      congr 1
      ring

theorem quadratic_source_label_bounds (Z L eta X v : ℝ) (hZ : 0 < Z)
    (hwidth : 2 ≤ Z ^ eta) (hX0 : 0 ≤ X) (hX : X ≤ Z ^ L)
    (hv1 : 1 ≤ v) (hv : v ≤ (2 * X) ^ 2) :
    center (label Z (2 * L) (2 * eta) v).val ≤ v ∧
      v ≤ 2 * center (label Z (2 * L) (2 * eta) v).val :=
  label_bounds Z (2 * L) (2 * eta) v hv1
    (quadratic_source_cap Z L eta X v hZ hwidth hX0 hX hv)

theorem center_le_cap (Z lengthCap eta : ℝ)
    (hZ : 1 ≤ Z) (hL : 0 ≤ lengthCap + eta) (j : Index Z lengthCap eta) :
    center j.val ≤ Z ^ (lengthCap + eta) := by
  have hcap : 1 ≤ Z ^ (lengthCap + eta) := Real.one_le_rpow hZ hL
  unfold center
  apply max_le hcap
  cases hj : j.val with
  | zero =>
      simp only [hj, pow_zero]
      linarith
  | succ k =>
      rw [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      apply (pow_lt_of_lt_dyadicLength hcap ?_).le
      have hlt := j.isLt
      change j.val < dyadicLength (Z ^ (lengthCap + eta)) + 1 at hlt
      omega

def bin {α : Type*} (T : Finset α) (v : α → ℝ)
    (Z lengthCap eta : ℝ) (j : Index Z lengthCap eta) : Finset α :=
  T.filter (fun x => label Z lengthCap eta (v x) = j)

@[simp] theorem mem_bin {α : Type*} (T : Finset α) (v : α → ℝ)
    (Z lengthCap eta : ℝ) (j : Index Z lengthCap eta) (x : α) :
    x ∈ bin T v Z lengthCap eta j ↔ x ∈ T ∧ label Z lengthCap eta (v x) = j := by
  simp only [bin, Finset.mem_filter]

theorem bin_bounds {α : Type*} (T : Finset α) (v : α → ℝ)
    (Z lengthCap eta : ℝ)
    (hT : ∀ x ∈ T, 1 ≤ v x ∧ v x ≤ Z ^ (lengthCap + eta))
    (j : Index Z lengthCap eta) (x : α) (hx : x ∈ bin T v Z lengthCap eta j) :
    center j.val ≤ v x ∧ v x ≤ 2 * center j.val := by
  obtain ⟨hxT, hj⟩ := (mem_bin T v Z lengthCap eta j x).mp hx
  have hb := label_bounds Z lengthCap eta (v x) (hT x hxT).1 (hT x hxT).2
  rwa [hj] at hb

theorem bin_ratio {α : Type*} (T : Finset α) (v : α → ℝ)
    (Z lengthCap eta : ℝ)
    (hT : ∀ x ∈ T, 1 ≤ v x ∧ v x ≤ Z ^ (lengthCap + eta))
    (j : Index Z lengthCap eta) (x : α) (hx : x ∈ bin T v Z lengthCap eta j) :
    v x / center j.val ∈ Set.Icc (1 : ℝ) 2 := by
  obtain ⟨hl, hh⟩ := bin_bounds T v Z lengthCap eta hT j x hx
  exact ⟨(le_div_iff₀ (center_pos j.val)).mpr (by simpa only [one_mul] using hl),
    (div_le_iff₀ (center_pos j.val)).mpr hh⟩

/-- Exact regrouping, valid for arbitrary signed or complex coefficients. -/
theorem sum_bins {α A : Type*} [AddCommMonoid A]
    (T : Finset α) (v : α → ℝ) (Z lengthCap eta : ℝ) (F : α → A) :
    (∑ x ∈ T, F x) =
      ∑ j : Index Z lengthCap eta, ∑ x ∈ bin T v Z lengthCap eta j, F x := by
  simp only [bin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

abbrev BoxIndex (Z lengthCap eta : ℝ) :=
  Index Z lengthCap eta × Index Z lengthCap eta

def box {α : Type*} (T : Finset α) (v₁ v₂ : α → ℝ)
    (Z lengthCap eta : ℝ) (j : BoxIndex Z lengthCap eta) : Finset α :=
  T.filter (fun x => (label Z lengthCap eta (v₁ x), label Z lengthCap eta (v₂ x)) = j)

def productCenter {Z lengthCap eta : ℝ} (j : BoxIndex Z lengthCap eta) : ℝ :=
  center j.1.val * center j.2.val

theorem productCenter_pos {Z lengthCap eta : ℝ} (j : BoxIndex Z lengthCap eta) :
    0 < productCenter j := mul_pos (center_pos _) (center_pos _)

theorem box_bounds {α : Type*} (T : Finset α) (v₁ v₂ : α → ℝ)
    (Z lengthCap eta : ℝ)
    (h₁ : ∀ x ∈ T, 1 ≤ v₁ x ∧ v₁ x ≤ Z ^ (lengthCap + eta))
    (h₂ : ∀ x ∈ T, 1 ≤ v₂ x ∧ v₂ x ≤ Z ^ (lengthCap + eta))
    (j : BoxIndex Z lengthCap eta) (x : α) (hx : x ∈ box T v₁ v₂ Z lengthCap eta j) :
    productCenter j ≤ v₁ x * v₂ x ∧ v₁ x * v₂ x ≤ 4 * productCenter j := by
  obtain ⟨hxT, hj⟩ := Finset.mem_filter.mp hx
  have hj₁ := congrArg Prod.fst hj
  have hj₂ := congrArg Prod.snd hj
  change label Z lengthCap eta (v₁ x) = j.1 at hj₁
  change label Z lengthCap eta (v₂ x) = j.2 at hj₂
  have hb₁ := label_bounds Z lengthCap eta (v₁ x) (h₁ x hxT).1 (h₁ x hxT).2
  have hb₂ := label_bounds Z lengthCap eta (v₂ x) (h₂ x hxT).1 (h₂ x hxT).2
  rw [hj₁] at hb₁
  rw [hj₂] at hb₂
  refine ⟨mul_le_mul hb₁.1 hb₂.1 (center_pos _).le
    (zero_le_one.trans (h₁ x hxT).1), ?_⟩
  calc
    _ ≤ (2 * center j.1.val) * (2 * center j.2.val) :=
      mul_le_mul hb₁.2 hb₂.2 (zero_le_one.trans (h₂ x hxT).1)
        (mul_nonneg (by norm_num) (center_pos _).le)
    _ = _ := by unfold productCenter; ring

theorem box_ratio {α : Type*} (T : Finset α) (v₁ v₂ : α → ℝ)
    (Z lengthCap eta : ℝ)
    (h₁ : ∀ x ∈ T, 1 ≤ v₁ x ∧ v₁ x ≤ Z ^ (lengthCap + eta))
    (h₂ : ∀ x ∈ T, 1 ≤ v₂ x ∧ v₂ x ≤ Z ^ (lengthCap + eta))
    (j : BoxIndex Z lengthCap eta) (x : α) (hx : x ∈ box T v₁ v₂ Z lengthCap eta j) :
    v₁ x * v₂ x / productCenter j ∈ Set.Icc (1 : ℝ) 4 := by
  obtain ⟨hl, hh⟩ := box_bounds T v₁ v₂ Z lengthCap eta h₁ h₂ j x hx
  exact ⟨(le_div_iff₀ (productCenter_pos j)).mpr (by simpa only [one_mul] using hl),
    (div_le_iff₀ (productCenter_pos j)).mpr hh⟩

theorem sum_boxes {α A : Type*} [AddCommMonoid A]
    (T : Finset α) (v₁ v₂ : α → ℝ) (Z lengthCap eta : ℝ) (F : α → A) :
    (∑ x ∈ T, F x) =
      ∑ j : BoxIndex Z lengthCap eta, ∑ x ∈ box T v₁ v₂ Z lengthCap eta j, F x := by
  simp only [box, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- The existing logarithmic-length estimate is applied with a fixed
smaller power. No constant depends on Z or the actual source values. -/
theorem exists_bin_count_bound (lengthCap eta pi : ℝ)
    (hL : 0 ≤ lengthCap + eta) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Fintype.card (Index Z lengthCap eta) : ℝ) ≤ C * Z ^ pi := by
  let delta := pi / (lengthCap + eta + 1)
  have hden : 0 < lengthCap + eta + 1 := by linarith
  have hd : 0 < delta := div_pos hpi hden
  let C₀ := 2 + 1 / (delta * Real.log 2)
  let C := max 1 C₀
  have hC₀ : 0 ≤ C₀ := (dyadicLength_small_power_constant_pos hd).le
  refine ⟨C, le_max_left _ _, ?_⟩
  intro Z hZ
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hX := Real.one_le_rpow hZ hL
  have hpower : (Z ^ (lengthCap + eta)) ^ delta ≤ Z ^ pi := by
    rw [← Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    change (lengthCap + eta) * (pi / (lengthCap + eta + 1)) ≤ pi
    have hr : (lengthCap + eta) / (lengthCap + eta + 1) ≤ 1 :=
      (div_le_iff₀ hden).mpr (by linarith)
    calc
      _ = pi * ((lengthCap + eta) / (lengthCap + eta + 1)) := by ring
      _ ≤ pi * 1 := mul_le_mul_of_nonneg_left hr hpi.le
      _ = pi := mul_one _
  calc
    _ ≤ C₀ * (Z ^ (lengthCap + eta)) ^ delta := by
      simpa only [Index, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        dyadicLength_small_power hd hX
    _ ≤ C₀ * Z ^ pi := mul_le_mul_of_nonneg_left hpower hC₀
    _ ≤ C * Z ^ pi := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hz.le _)

theorem exists_box_count_bound (lengthCap eta pi : ℝ)
    (hL : 0 ≤ lengthCap + eta) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Fintype.card (BoxIndex Z lengthCap eta) : ℝ) ≤ C * Z ^ pi := by
  obtain ⟨C, hC, hb⟩ := exists_bin_count_bound lengthCap eta (pi / 2) hL (by positivity)
  refine ⟨C ^ 2, one_le_pow₀ hC, ?_⟩
  intro Z hZ
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have h := mul_le_mul (hb Z hZ) (hb Z hZ) (Nat.cast_nonneg _) (by positivity)
  simpa only [BoxIndex, Fintype.card_prod, Nat.cast_mul] using h.trans_eq (show
    (C * Z ^ (pi / 2)) * (C * Z ^ (pi / 2)) = C ^ 2 * Z ^ pi from by
      rw [show (C * Z ^ (pi / 2)) * (C * Z ^ (pi / 2)) =
        C ^ 2 * (Z ^ (pi / 2) * Z ^ (pi / 2)) by ring,
        ← Real.rpow_add hz]
      congr 1
      congr 1
      ring)

def centerLength (Z : ℝ) (j : ℕ) : ℝ := Real.logb Z (center j)

theorem center_eq_rpow (Z : ℝ) (hZ : 1 < Z) (j : ℕ) :
    center j = Z ^ centerLength Z j :=
  (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (center_pos j)).symm

theorem centerLength_bounds (Z lengthCap eta : ℝ) (hZ : 1 < Z)
    (hL : 0 ≤ lengthCap + eta) (j : Index Z lengthCap eta) :
    0 ≤ centerLength Z j.val ∧ centerLength Z j.val ≤ lengthCap + eta := by
  refine ⟨Real.logb_nonneg hZ (one_le_center _), ?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (center_pos _)).mpr
    (center_le_cap Z lengthCap eta hZ.le hL j)

theorem bin_annulus {α : Type*} (T : Finset α) (v : α → ℝ)
    (Z lengthCap eta : ℝ) (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ eta)
    (hT : ∀ x ∈ T, 1 ≤ v x ∧ v x ≤ Z ^ (lengthCap + eta))
    (j : Index Z lengthCap eta) (x : α) (hx : x ∈ bin T v Z lengthCap eta j) :
    Z ^ centerLength Z j.val ≤ v x ∧
      v x ≤ Z ^ (centerLength Z j.val + eta) := by
  obtain ⟨hl, hh⟩ := bin_bounds T v Z lengthCap eta hT j x hx
  refine ⟨by simpa only [← center_eq_rpow Z hZ] using hl, ?_⟩
  calc
    _ ≤ 2 * center j.val := hh
    _ ≤ Z ^ eta * center j.val :=
      mul_le_mul_of_nonneg_right hwidth (center_pos _).le
    _ = _ := by rw [center_eq_rpow Z hZ, ← Real.rpow_add (zero_lt_one.trans hZ)]; congr 1; ring

section Ideals

variable (K : Type*) [Field K] [NumberField K]

/-- The actual norm, not a separately supplied real label, selects the
fixed source bin. -/
def idealBin (T : Finset (Ideal (𝓞 K))) (Z lengthCap eta : ℝ)
    (j : Index Z lengthCap eta) : Finset (Ideal (𝓞 K)) :=
  bin T (fun I => (Ideal.absNorm I : ℝ)) Z lengthCap eta j

theorem idealBin_ratio (T : Finset (Ideal (𝓞 K))) (Z lengthCap eta : ℝ)
    (hzero : ∀ I ∈ T, I ≠ 0)
    (hcap : ∀ I ∈ T, (Ideal.absNorm I : ℝ) ≤ Z ^ (lengthCap + eta))
    (j : Index Z lengthCap eta) (I : Ideal (𝓞 K)) (hI : I ∈ idealBin K T Z lengthCap eta j) :
    (Ideal.absNorm I : ℝ) / center j.val ∈ Set.Icc (1 : ℝ) 2 := by
  apply bin_ratio T (fun I => (Ideal.absNorm I : ℝ)) Z lengthCap eta ?_ j I hI
  intro J hJ
  refine ⟨?_, hcap J hJ⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun hz => hzero J hJ (Ideal.absNorm_eq_zero_iff.mp hz))

/-- Two actual extracted ideals have the [1,4] product window required
by the second centered family. -/
theorem idealProduct_box_ratio {α : Type*} (T : Finset α)
    (I J : α → Ideal (𝓞 K)) (Z lengthCap eta : ℝ)
    (hI0 : ∀ x ∈ T, I x ≠ 0) (hJ0 : ∀ x ∈ T, J x ≠ 0)
    (hI : ∀ x ∈ T, (Ideal.absNorm (I x) : ℝ) ≤ Z ^ (lengthCap + eta))
    (hJ : ∀ x ∈ T, (Ideal.absNorm (J x) : ℝ) ≤ Z ^ (lengthCap + eta))
    (j : BoxIndex Z lengthCap eta) (x : α)
    (hx : x ∈ box T (fun x => (Ideal.absNorm (I x) : ℝ))
      (fun x => (Ideal.absNorm (J x) : ℝ)) Z lengthCap eta j) :
    (Ideal.absNorm (I x * J x) : ℝ) / productCenter j ∈ Set.Icc (1 : ℝ) 4 := by
  rw [map_mul, Nat.cast_mul]
  apply box_ratio T (fun x => (Ideal.absNorm (I x) : ℝ))
    (fun x => (Ideal.absNorm (J x) : ℝ)) Z lengthCap eta ?_ ?_ j x hx
  · intro y hy
    refine ⟨?_, hI y hy⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI0 y hy (Ideal.absNorm_eq_zero_iff.mp hz))
  · intro y hy
    refine ⟨?_, hJ y hy⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 y hy (Ideal.absNorm_eq_zero_iff.mp hz))

end Ideals

end HeckeSkeleton.Moments.MOM_INV_STEP.DyadicSourcePartition

end

