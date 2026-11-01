module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-!
# Actual column lengths selected by fixed centers

The first center is selected by the norm product of the extracted factor
and the first overlap.  The second center is selected by the product of
the fresh common factor and the second overlap.  Their ratios lie in
[1,2] and [1,4], respectively.

The bounds below retain the resulting errors in the actual logarithmic
column length.  They do not identify that length with its formal center.
All inputs are numerical norm annuli and the two center inequalities;
there is no estimate for an energy among the hypotheses.
-/

@[expose] public section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry

/-- Division by a positive center transports both endpoints of the
actual scale interval. -/
theorem scale_bounds (Z X c L U l u : ℝ) (hZ : 0 < Z) (hc : 0 < c)
    (hXl : Z ^ L ≤ X) (hXu : X ≤ Z ^ U)
    (hcl : Z ^ l ≤ c) (hcu : c ≤ Z ^ u) :
    Z ^ (L - u) ≤ X / c ∧ X / c ≤ Z ^ (U - l) := by
  constructor
  · apply (le_div_iff₀ hc).mpr
    calc
      Z ^ (L - u) * c ≤ Z ^ (L - u) * Z ^ u :=
        mul_le_mul_of_nonneg_left hcu (Real.rpow_nonneg hZ.le _)
      _ = Z ^ L := by rw [← Real.rpow_add hZ]; congr 1; ring
      _ ≤ X := hXl
  · apply (div_le_iff₀ hc).mpr
    calc
      X ≤ Z ^ U := hXu
      _ = Z ^ (U - l) * Z ^ l := by rw [← Real.rpow_add hZ]; congr 1; ring
      _ ≤ Z ^ (U - l) * c :=
        mul_le_mul_of_nonneg_left hcl (Real.rpow_nonneg hZ.le _)

/-- A multiplicative window of width at most `Z ^ w` costs precisely
`w` at the lower endpoint for its center. -/
theorem center_bounds (Z N c W l u w : ℝ) (hZ : 0 < Z) (hc : 0 < c)
    (hNl : Z ^ l ≤ N) (hNu : N ≤ Z ^ u)
    (hcN : c ≤ N) (hNc : N ≤ W * c) (hW : W ≤ Z ^ w) :
    Z ^ (l - w) ≤ c ∧ c ≤ Z ^ u := by
  refine ⟨?_, hcN.trans hNu⟩
  rw [Real.rpow_sub hZ]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hZ w)).mpr
  calc
    Z ^ l ≤ N := hNl
    _ ≤ W * c := hNc
    _ ≤ c * Z ^ w := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hW hc.le

/-- Two genuine positive norm annuli multiply without any rounding. -/
theorem product_two_bounds (Z x y a b h : ℝ) (hZ : 0 < Z)
    (hx : Z ^ (a - h) ≤ x ∧ x ≤ Z ^ (a + h))
    (hy : Z ^ (b - h) ≤ y ∧ y ≤ Z ^ (b + h)) :
    Z ^ (a + b - 2 * h) ≤ x * y ∧ x * y ≤ Z ^ (a + b + 2 * h) := by
  have hx0 : 0 ≤ x := (Real.rpow_pos_of_pos hZ _).le.trans hx.1
  have hy0 : 0 ≤ y := (Real.rpow_pos_of_pos hZ _).le.trans hy.1
  constructor
  · calc
      Z ^ (a + b - 2 * h) = Z ^ (a - h) * Z ^ (b - h) := by
        rw [← Real.rpow_add hZ]; congr 1; ring
      _ ≤ x * y := mul_le_mul hx.1 hy.1 (Real.rpow_nonneg hZ.le _) hx0
  · calc
      x * y ≤ Z ^ (a + h) * Z ^ (b + h) :=
        mul_le_mul hx.2 hy.2 hy0 (Real.rpow_nonneg hZ.le _)
      _ = Z ^ (a + b + 2 * h) := by
        rw [← Real.rpow_add hZ]; congr 1; ring

/-- The three factors are the extracted A, the old common C, and the
first overlap.  Each contributes its own annular error. -/
theorem product_three_bounds (Z x y z a b t h : ℝ) (hZ : 0 < Z)
    (hx : Z ^ (a - h) ≤ x ∧ x ≤ Z ^ (a + h))
    (hy : Z ^ (b - h) ≤ y ∧ y ≤ Z ^ (b + h))
    (hz : Z ^ (t - h) ≤ z ∧ z ≤ Z ^ (t + h)) :
    Z ^ (a + b + t - 3 * h) ≤ x * y * z ∧
      x * y * z ≤ Z ^ (a + b + t + 3 * h) := by
  have hxy := product_two_bounds Z x y a b h hZ hx hy
  have hxy0 : 0 ≤ x * y := (Real.rpow_pos_of_pos hZ _).le.trans hxy.1
  have hz0 : 0 ≤ z := (Real.rpow_pos_of_pos hZ _).le.trans hz.1
  constructor
  · calc
      Z ^ (a + b + t - 3 * h) =
          Z ^ (a + b - 2 * h) * Z ^ (t - h) := by
        rw [← Real.rpow_add hZ]; congr 1; ring
      _ ≤ x * y * z :=
        mul_le_mul hxy.1 hz.1 (Real.rpow_nonneg hZ.le _) hxy0
  · calc
      x * y * z ≤ Z ^ (a + b + 2 * h) * Z ^ (t + h) :=
        mul_le_mul hxy.2 hz.2 hz0 (Real.rpow_nonneg hZ.le _)
      _ = Z ^ (a + b + t + 3 * h) := by
        rw [← Real.rpow_add hZ]; congr 1; ring

theorem four_le_rpow_two (Z h : ℝ) (hZ : 0 < Z) (hwidth : 2 ≤ Z ^ h) :
    (4 : ℝ) ≤ Z ^ (2 * h) := by
  calc
    (4 : ℝ) = (2 : ℝ) * 2 := by norm_num
    _ ≤ Z ^ h * Z ^ h := mul_le_mul hwidth hwidth (by norm_num)
      (Real.rpow_nonneg hZ.le _)
    _ = Z ^ (2 * h) := by rw [← Real.rpow_add hZ]; congr 1; ring

/-- The actual first center selected by a dyadic bin. -/
theorem first_center_bounds (Z a b t h NA NC Ne c : ℝ)
    (hZ : 0 < Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (a - h) ≤ NA ∧ NA ≤ Z ^ (a + h))
    (hC : Z ^ (b - h) ≤ NC ∧ NC ≤ Z ^ (b + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hbin : c ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c) :
    Z ^ (a + b + t - 4 * h) ≤ c ∧ c ≤ Z ^ (a + b + t + 3 * h) := by
  have hn := product_three_bounds Z NA NC Ne a b t h hZ hA hC he
  have hb := center_bounds Z (NA * NC * Ne) c 2
    (a + b + t - 3 * h) (a + b + t + 3 * h) h
    hZ hc hn.1 hn.2 hbin.1 hbin.2 hwidth
  convert hb using 1 <;> congr 1 <;> ring

/-- The real scale X/c, where X = Z^r, differs from the formal first
length by an explicit one-sided error interval. -/
theorem first_scale_bounds (Z r a b t h NA NC Ne c : ℝ)
    (hZ : 0 < Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (a - h) ≤ NA ∧ NA ≤ Z ^ (a + h))
    (hC : Z ^ (b - h) ≤ NC ∧ NC ≤ Z ^ (b + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hbin : c ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c) :
    Z ^ (r - a - b - t - 3 * h) ≤ Z ^ r / c ∧
      Z ^ r / c ≤ Z ^ (r - a - b - t + 4 * h) := by
  have hb := first_center_bounds Z a b t h NA NC Ne c hZ hc hwidth hA hC he hbin
  have hs := scale_bounds Z (Z ^ r) c r r
    (a + b + t - 4 * h) (a + b + t + 3 * h)
    hZ hc le_rfl le_rfl hb.1 hb.2
  convert hs using 1 <;> congr 1 <;> ring

/-- The two independent second bins give a width-four center. -/
theorem second_center_bounds (Z g v h Ng Nv c : ℝ)
    (hZ : 0 < Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hg : Z ^ (g - h) ≤ Ng ∧ Ng ≤ Z ^ (g + h))
    (hv : Z ^ (v - h) ≤ Nv ∧ Nv ≤ Z ^ (v + h))
    (hbin : c ≤ Ng * Nv ∧ Ng * Nv ≤ 4 * c) :
    Z ^ (g + v - 4 * h) ≤ c ∧ c ≤ Z ^ (g + v + 2 * h) := by
  have hn := product_two_bounds Z Ng Nv g v h hZ hg hv
  have hb := center_bounds Z (Ng * Nv) c 4
    (g + v - 2 * h) (g + v + 2 * h) (2 * h)
    hZ hc hn.1 hn.2 hbin.1 hbin.2 (four_le_rpow_two Z h hZ hwidth)
  convert hb using 1 <;> congr 1 <;> ring

/-- Both actual divisions are retained; no formal length is substituted
for the scale produced by the first center. -/
theorem two_scale_bounds (Z r a b t g v h NA NC Ne Ng Nv c₁ c₂ : ℝ)
    (hZ : 0 < Z) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (a - h) ≤ NA ∧ NA ≤ Z ^ (a + h))
    (hC : Z ^ (b - h) ≤ NC ∧ NC ≤ Z ^ (b + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hg : Z ^ (g - h) ≤ Ng ∧ Ng ≤ Z ^ (g + h))
    (hv : Z ^ (v - h) ≤ Nv ∧ Nv ≤ Z ^ (v + h))
    (hbin₁ : c₁ ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c₁)
    (hbin₂ : c₂ ≤ Ng * Nv ∧ Ng * Nv ≤ 4 * c₂) :
    Z ^ (r - a - b - t - g - v - 5 * h) ≤ (Z ^ r / c₁) / c₂ ∧
      (Z ^ r / c₁) / c₂ ≤ Z ^ (r - a - b - t - g - v + 8 * h) := by
  have hfirst := first_scale_bounds Z r a b t h NA NC Ne c₁
    hZ hc₁ hwidth hA hC he hbin₁
  have hsecond := second_center_bounds Z g v h Ng Nv c₂
    hZ hc₂ hwidth hg hv hbin₂
  have hs := scale_bounds Z (Z ^ r / c₁) c₂
    (r - a - b - t - 3 * h) (r - a - b - t + 4 * h)
    (g + v - 4 * h) (g + v + 2 * h)
    hZ hc₂ hfirst.1 hfirst.2 hsecond.1 hsecond.2
  convert hs using 1 <;> congr 1 <;> ring

/-- Reading a true scale interval in logarithmic coordinates preserves
its explicit errors. -/
theorem log_length_bounds (Z U L lo hi : ℝ) (hZ : 1 < Z) (hU : 0 < U)
    (hUlo : Z ^ (L - lo) ≤ U) (hUhi : U ≤ Z ^ (L + hi)) :
    L - lo ≤ Real.logb Z U ∧ Real.logb Z U ≤ L + hi :=
  ⟨(Real.le_logb_iff_rpow_le hZ hU).mpr hUlo,
    (Real.logb_le_iff_le_rpow hZ hU).mpr hUhi⟩

theorem first_log_length_bounds (Z r a b t h NA NC Ne c : ℝ)
    (hZ : 1 < Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (a - h) ≤ NA ∧ NA ≤ Z ^ (a + h))
    (hC : Z ^ (b - h) ≤ NC ∧ NC ≤ Z ^ (b + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hbin : c ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c) :
    r - a - b - t - 3 * h ≤ Real.logb Z (Z ^ r / c) ∧
      Real.logb Z (Z ^ r / c) ≤ r - a - b - t + 4 * h := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hb := first_scale_bounds Z r a b t h NA NC Ne c hz hc hwidth hA hC he hbin
  exact log_length_bounds Z _ (r - a - b - t) (3 * h) (4 * h)
    hZ (div_pos (Real.rpow_pos_of_pos hz r) hc) hb.1 hb.2

theorem two_log_length_bounds (Z r a b t g v h NA NC Ne Ng Nv c₁ c₂ : ℝ)
    (hZ : 1 < Z) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (a - h) ≤ NA ∧ NA ≤ Z ^ (a + h))
    (hC : Z ^ (b - h) ≤ NC ∧ NC ≤ Z ^ (b + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hg : Z ^ (g - h) ≤ Ng ∧ Ng ≤ Z ^ (g + h))
    (hv : Z ^ (v - h) ≤ Nv ∧ Nv ≤ Z ^ (v + h))
    (hbin₁ : c₁ ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c₁)
    (hbin₂ : c₂ ≤ Ng * Nv ∧ Ng * Nv ≤ 4 * c₂) :
    r - a - b - t - g - v - 5 * h ≤ Real.logb Z ((Z ^ r / c₁) / c₂) ∧
      Real.logb Z ((Z ^ r / c₁) / c₂) ≤ r - a - b - t - g - v + 8 * h := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hb := two_scale_bounds Z r a b t g v h NA NC Ne Ng Nv c₁ c₂
    hz hc₁ hc₂ hwidth hA hC he hg hv hbin₁ hbin₂
  exact log_length_bounds Z _ (r - a - b - t - g - v) (5 * h) (8 * h)
    hZ (div_pos (div_pos (Real.rpow_pos_of_pos hz r) hc₁) hc₂) hb.1 hb.2

/-- A mesh at most eta/16 makes the actual second logarithmic length
lie within eta/2 of its formal value. -/
theorem fine_mesh_error (actual formal h eta : ℝ)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hb : formal - 5 * h ≤ actual ∧ actual ≤ formal + 8 * h) :
    |actual - formal| ≤ eta / 2 := by
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- The first logarithmic length consumes at most eta/4 at the same
mesh, leaving room for the second center and the fixed cutoffs. -/
theorem first_fine_mesh_error (actual formal h eta : ℝ)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hb : formal - 3 * h ≤ actual ∧ actual ≤ formal + 4 * h) :
    |actual - formal| ≤ eta / 4 := by
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry

end
