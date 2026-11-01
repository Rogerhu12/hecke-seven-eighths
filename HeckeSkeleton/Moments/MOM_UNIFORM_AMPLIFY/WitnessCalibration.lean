module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Uniform witness-scale calibration for sixth-power amplification

The numerical loss allocation is uniform for every inverse length in one
fixed interval.  The independent-scale estimate is kept separate from the
source's height and length certificates: neither is a consequence of
pointwise polynomial calibration.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

/-- Substitute `D = U^r` in the independent-scale amplifier and allocate
the two preliminary losses before choosing a witness length. -/
theorem independent_factor_at_witness_le
    {U r R a ε loss : ℝ} (hU : 1 ≤ U) (hr : 0 ≤ r) (hrR : r ≤ R)
    (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hbudget : 5 * a * R / 6 + (1 + R) * ε ≤ loss) :
    max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) *
        (U * U ^ r) ^ ε ≤ U ^ (max 1 ((1 + 5 * r) / 6) + loss) := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hR : 0 ≤ R := hr.trans hrR
  have hb : 0 ≤ 5 * a * R / 6 := by positivity
  have he₁ : 1 ≤ max 1 ((1 + 5 * r) / 6) := le_max_left _ _
  have he₂ : (1 + 5 * r) / 6 ≤ max 1 ((1 + 5 * r) / 6) := le_max_right _ _
  have har : a * r ≤ a * R := mul_le_mul_of_nonneg_left hrR ha
  have hm : max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) ≤
      U ^ (max 1 ((1 + 5 * r) / 6) + 5 * a * R / 6) := by
    apply max_le
    · calc
        U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    · rw [← Real.rpow_mul hUpos.le, ← Real.rpow_add hUpos]
      apply Real.rpow_le_rpow_of_exponent_le hU
      nlinarith
  have hscale : (U * U ^ r) ^ ε = U ^ ((1 + r) * ε) := by
    have hbase : U * U ^ r = U ^ (1 + r) := by
      rw [Real.rpow_add hUpos, Real.rpow_one]
    rw [hbase, ← Real.rpow_mul hUpos.le]
  calc
    _ ≤ U ^ (max 1 ((1 + 5 * r) / 6) + 5 * a * R / 6) *
        (U * U ^ r) ^ ε :=
      mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _)
    _ = U ^ (max 1 ((1 + 5 * r) / 6) + 5 * a * R / 6 + (1 + r) * ε) := by
      rw [hscale, ← Real.rpow_add hUpos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by
      have hmul := mul_le_mul_of_nonneg_right hrR hε
      linarith)

/-- A positive preliminary amplification parameter and a positive scale
loss can be chosen uniformly on the entire bounded range `0 ≤ r ≤ R`. -/
theorem exists_witness_loss_allocation {R loss : ℝ} (hR : 0 ≤ R)
    (hloss : 0 < loss) :
    ∃ a ε : ℝ, 0 < a ∧ 0 < ε ∧
      ∀ U r : ℝ, 1 ≤ U → 0 ≤ r → r ≤ R →
        max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) *
            (U * U ^ r) ^ ε ≤ U ^ (max 1 ((1 + 5 * r) / 6) + loss) := by
  let δ : ℝ := loss / (4 * (R + 1))
  have hden : 0 < 4 * (R + 1) := by positivity
  have hδ : 0 < δ := div_pos hloss hden
  have hδeq : δ * (4 * (R + 1)) = loss := by
    exact div_mul_cancel₀ loss (ne_of_gt hden)
  refine ⟨δ, δ, hδ, hδ, ?_⟩
  intro U r hU hr hrR
  apply independent_factor_at_witness_le hU hr hrR hδ.le hδ.le
  nlinarith [mul_nonneg hδ.le hR]

/-- A polynomial height growth certificate gives a fixed physical height
degree; it does not change either arithmetic exponent or preliminary loss. -/
theorem height_factor_le {x T C B A : ℝ}
    (hx : 0 ≤ x) (hT : 0 ≤ T) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hheight : x ≤ C * (1 + T) ^ B) :
    (1 + x) ^ A ≤ (1 + C) ^ A * (1 + T) ^ (B * A) := by
  have hbase : 1 ≤ (1 + T) ^ B := Real.one_le_rpow (by linarith) hB
  have hbound : 1 + x ≤ (1 + C) * (1 + T) ^ B := by nlinarith
  calc
    _ ≤ ((1 + C) * (1 + T) ^ B) ^ A :=
      Real.rpow_le_rpow (by linarith) hbound hA
    _ = _ := by
      rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ 1 + T)]

/-- The height ceiling is fixed before the later `τ`.  A single threshold
even works for every `0 ≤ τ ≤ ceiling`; the constant height multiplier is
absorbed in the positive physical scale exponent. -/
theorem exists_uniform_height_ceiling {d h C B : ℝ}
    (hd : 0 < d) (hh : 0 < h) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ ceiling Z₀ : ℝ, 0 < ceiling ∧ 1 ≤ Z₀ ∧
      ∀ Z τ : ℝ, Z₀ ≤ Z → 0 ≤ τ → τ ≤ ceiling →
        C * (1 + Z ^ τ) ^ B ≤ (Z ^ d) ^ h := by
  let ceiling : ℝ := d * h / (2 * (B + 1))
  have hden : 0 < 2 * (B + 1) := by positivity
  have hceiling : 0 < ceiling := div_pos (mul_pos hd hh) hden
  have hceq : ceiling * (2 * (B + 1)) = d * h :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hhalf : 0 < d * h / 2 := by positivity
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hhalf).eventually (Filter.eventually_ge_atTop (C * (2 : ℝ) ^ B)))
  refine ⟨ceiling, max 1 Z₀, hceiling, le_max_left _ _, ?_⟩
  intro Z τ hZ hτ hτc
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hconst : C * (2 : ℝ) ^ B ≤ Z ^ (d * h / 2) :=
    hZ₀ Z ((le_max_right _ _).trans hZ)
  have hZτ : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ
  have hτB : τ * B ≤ d * h / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hτc hB
    nlinarith
  have hbase : 1 + Z ^ τ ≤ 2 * Z ^ τ := by linarith
  calc
    C * (1 + Z ^ τ) ^ B ≤ C * (2 * Z ^ τ) ^ B :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase hB) hC
    _ = (C * (2 : ℝ) ^ B) * Z ^ (τ * B) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hZpos.le _),
        ← Real.rpow_mul hZpos.le]
      ring
    _ ≤ Z ^ (d * h / 2) * Z ^ (d * h / 2) := by
      exact mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hτB)
        (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _)
    _ = (Z ^ d) ^ h := by
      rw [← Real.rpow_add hZpos, ← Real.rpow_mul hZpos.le]
      congr 1
      ring

/-- Enlarging the row and polynomial scales preserves the height
admissibility obtained at the fixed lower physical scale. -/
theorem height_admissible_of_lower_scale {x Z d U D h : ℝ}
    (hZ : 0 ≤ Z) (hU : Z ^ d ≤ U) (hD : 1 ≤ D) (hh : 0 ≤ h)
    (hx : x ≤ (Z ^ d) ^ h) : x ≤ (U * D) ^ h := by
  have hU0 : 0 ≤ U := (Real.rpow_nonneg hZ d).trans hU
  have hUD : U ≤ U * D := by nlinarith
  exact hx.trans (Real.rpow_le_rpow (Real.rpow_nonneg hZ d) (hU.trans hUD) hh)

/-- The complete pointwise witness bridge.  The analytic bound concerns
the same energy and the same height vector; only the exponents are changed. -/
theorem witness_bound_of_independent_bound
    {E U r R a ε loss x T C A Cht B : ℝ}
    (hU : 1 ≤ U) (hr : 0 ≤ r) (hrR : r ≤ R)
    (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hbudget : 5 * a * R / 6 + (1 + R) * ε ≤ loss)
    (hx : 0 ≤ x) (hT : 0 ≤ T) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hCht : 0 ≤ Cht) (hB : 0 ≤ B) (hheight : x ≤ Cht * (1 + T) ^ B)
    (hE : E ≤ C * max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) *
      (U * U ^ r) ^ ε * (1 + x) ^ A) :
    E ≤ (C * (1 + Cht) ^ A) * U ^ (max 1 ((1 + 5 * r) / 6) + loss) *
      (1 + T) ^ (B * A) := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hf := independent_factor_at_witness_le hU hr hrR ha hε hbudget
  have hh := height_factor_le hx hT hCht hB hA hheight
  calc
    E ≤ C * (max U (U ^ (1 / 6 : ℝ) * (U ^ r) ^ (5 * (1 + a) / 6)) *
        (U * U ^ r) ^ ε) * (1 + x) ^ A := by simpa only [mul_assoc] using hE
    _ ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) + loss) *
        ((1 + Cht) ^ A * (1 + T) ^ (B * A)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hf hC) hh
        (Real.rpow_nonneg (by linarith) _) (mul_nonneg hC (Real.rpow_nonneg hU0 _))
    _ = _ := by ring

/-- Family-level witness calibration with the same quantifier order as
`UniformMomentBound`.  Length, lower physical scale, and height-growth
certificates are explicit source data.  The analytic input is the already
amplified independent-scale bound, before substitution of the witnesses. -/
theorem uniform_witness_calibration
    {ι : ℝ → ℝ → Type*}
    (E U r x : ∀ Z T : ℝ, ι Z T → ℝ)
    {d R loss Cht B : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hloss : 0 < loss)
    (hCht : 0 ≤ Cht) (hB : 0 ≤ B)
    (hdata : ∀ Z T : ℝ, 1 ≤ Z → 1 ≤ T → ∀ i : ι Z T,
      Z ^ d ≤ U Z T i ∧ 0 ≤ r Z T i ∧ r Z T i ≤ R ∧
        0 ≤ x Z T i ∧ x Z T i ≤ Cht * (1 + T) ^ B)
    (hamp : ∀ a ε : ℝ, 0 < a → 0 < ε →
      ∃ C A h : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧
        ∀ Z T : ℝ, ∀ i : ι Z T, 1 ≤ U Z T i → 1 ≤ U Z T i ^ r Z T i →
          x Z T i ≤ (U Z T i * U Z T i ^ r Z T i) ^ h →
          E Z T i ≤
            C * max (U Z T i)
              (U Z T i ^ (1 / 6 : ℝ) *
                (U Z T i ^ r Z T i) ^ (5 * (1 + a) / 6)) *
              (U Z T i * U Z T i ^ r Z T i) ^ ε * (1 + x Z T i) ^ A) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
          ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : ι Z (Z ^ τ),
            E Z (Z ^ τ) i ≤
              k * U Z (Z ^ τ) i ^ (max 1 ((1 + 5 * r Z (Z ^ τ) i) / 6) + loss) *
                (1 + Z ^ τ) ^ A := by
  obtain ⟨a, ε, ha, hε, hallocate⟩ := exists_witness_loss_allocation hR hloss
  obtain ⟨C, A, h, hC, hA, hh, hbound⟩ := hamp a ε ha hε
  obtain ⟨ceiling, Z₀, hc, hZ₀, hlimit⟩ :=
    exists_uniform_height_ceiling hd hh hCht hB
  refine ⟨B * A, ceiling, mul_nonneg hB hA, hc, ?_⟩
  intro τ hτ hτc
  refine ⟨Z₀, C * (1 + Cht) ^ A, hZ₀, ?_, ?_⟩
  · exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  · intro Z hZ i
    have hZ1 : 1 ≤ Z := hZ₀.trans hZ
    have hZn : 0 ≤ Z := zero_le_one.trans hZ1
    have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
    obtain ⟨hU, hr, hrR, hx, hheight⟩ := hdata Z (Z ^ τ) hZ1 hT i
    have hU1 : 1 ≤ U Z (Z ^ τ) i := (Real.one_le_rpow hZ1 hd.le).trans hU
    have hD1 : 1 ≤ U Z (Z ^ τ) i ^ r Z (Z ^ τ) i := Real.one_le_rpow hU1 hr
    have hheight' : x Z (Z ^ τ) i ≤
        (U Z (Z ^ τ) i * U Z (Z ^ τ) i ^ r Z (Z ^ τ) i) ^ h :=
      height_admissible_of_lower_scale hZn hU hD1 hh.le
        (hheight.trans (hlimit Z τ hZ hτ.le hτc))
    have he := hbound Z (Z ^ τ) i hU1 hD1 hheight'
    have hf := hallocate (U Z (Z ^ τ) i) (r Z (Z ^ τ) i) hU1 hr hrR
    have hhfactor := height_factor_le hx (zero_le_one.trans hT) hCht hB hA hheight
    calc
      E Z (Z ^ τ) i ≤
          C * (max (U Z (Z ^ τ) i)
            (U Z (Z ^ τ) i ^ (1 / 6 : ℝ) *
              (U Z (Z ^ τ) i ^ r Z (Z ^ τ) i) ^ (5 * (1 + a) / 6)) *
            (U Z (Z ^ τ) i * U Z (Z ^ τ) i ^ r Z (Z ^ τ) i) ^ ε) *
            (1 + x Z (Z ^ τ) i) ^ A := by simpa only [mul_assoc] using he
      _ ≤ C * U Z (Z ^ τ) i ^ (max 1 ((1 + 5 * r Z (Z ^ τ) i) / 6) + loss) *
          ((1 + Cht) ^ A * (1 + Z ^ τ) ^ (B * A)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hf hC.le) hhfactor
          (Real.rpow_nonneg (by linarith) _)
          (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hU1) _))
      _ = _ := by ring

end HeckeSkeleton.Moments.UniformAmplify
