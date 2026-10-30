import HeckeSkeleton.HighEulerFiniteData
import HeckeSkeleton.HighEulerScalarBounds

/-!
# Checked evaluation and decay of the normalized finite ramified tables

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.

This module connects explicit finite rational data to the scalar table already
bounded in `HighEulerScalarBounds`.  All evaluation identities are proved.
The remaining arithmetic obligation is to identify these normalized phase
parameters with the actual local Fourier/Gauss coefficients.
-/

noncomputable section

namespace HBEulerCheckedTable

open HBEulerFiniteData
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open scoped Classical BigOperators

def powerWeight (q : ℝ) (s w z : ℂ) (e : Exponent) : ℂ :=
  (q : ℂ) ^ (-((e.1 : ℂ) * s + (e.2.1 : ℂ) * w + (e.2.2 : ℂ) * z))

@[simp] theorem powerWeight_zero (q : ℝ) (s w z : ℂ) :
    powerWeight q s w z (0, 0, 0) = 1 := by
  simp [powerWeight]

theorem polynomialValue_ofTerms_weight (ts : Terms) (q : ℝ) (s w z : ℂ) :
    polynomialValue (ofTerms ts) q s w z = termsValue ts (powerWeight q s w z) := by
  exact weightedValue_ofTerms ts (powerWeight q s w z)

theorem powerWeight_shift6 (q : ℝ) (hq : 0 < q) (s w z : ℂ) (e : Exponent) :
    powerWeight q s w z (0 + e.1, 0 + e.2.1, 6 + e.2.2) =
      coordV q z * powerWeight q s w z e := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold powerWeight coordV
  rw [← Complex.cpow_add _ _ hqC]
  congr 1
  push_cast
  ring

theorem termsValue_shift6 (q : ℝ) (hq : 0 < q) (s w z : ℂ) (ts : Terms) :
    termsValue (shiftScale (0, 0, 6) (-1) ts) (powerWeight q s w z) =
      -coordV q z * termsValue ts (powerWeight q s w z) := by
  induction ts with
  | nil => simp [shiftScale]
  | cons t ts ih =>
      change (-1 * t.2) * powerWeight q s w z
          (0 + t.1.1, 0 + t.1.2.1, 6 + t.1.2.2) +
          termsValue (shiftScale (0, 0, 6) (-1) ts) (powerWeight q s w z) =
        -coordV q z * (t.2 * powerWeight q s w z t.1 +
          termsValue ts (powerWeight q s w z))
      rw [powerWeight_shift6 q hq, ih]
      ring

/-- The coefficient and exponent triple evaluate to the scalar monomial. -/
theorem phaseMonomial_from_weight (q : ℝ) (hq : 0 < q)
    (c : ℂ) (r : ℝ) (s w z : ℂ) (m n : ℕ) :
    phaseMonomial q c r s w m n =
      (c * (q : ℂ) ^ (r : ℂ)) *
        powerWeight q s w z ((m : ℤ), (n : ℤ), 0) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold phaseMonomial powerWeight
  simp only [Int.cast_natCast, Int.cast_zero, zero_mul, add_zero]
  rw [mul_assoc, ← Complex.cpow_add _ _ hqC]
  congr 2
  ring

def normalizedSpecialTerms (P : PhaseData) (q : ℝ) (j : Fin 5) : Terms :=
  match j.val with
  | 0 => [((1, 1, 0), P.eta * (q : ℂ) ^ (1 : ℂ))]
  | 1 => [((3, 0, 0), P.c2 * (q : ℂ) ^ (3 / 2 : ℂ))]
  | 2 => [((3, 1, 0), P.c31 * (q : ℂ) ^ (2 : ℂ)),
          ((4, 0, 0), -(P.c32 * (q : ℂ) ^ (2 : ℂ)))]
  | 3 => [((4, 1, 0), -(P.c4 * (q : ℂ) ^ (5 / 2 : ℂ)))]
  | _ => [((6, 0, 0), -(P.alpha ^ 2 * (q : ℂ) ^ (3 : ℂ)))]

theorem normalizedSpecialTerms_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) :
    termsValue (normalizedSpecialTerms P q j) (powerWeight q s w z) =
      specialTerm P q s w j := by
  have hmono : ∀ (c : ℂ) (r : ℝ) (m n : ℕ),
      phaseMonomial q c r s w m n =
        (c * (q : ℂ) ^ (r : ℂ)) *
          powerWeight q s w z ((m : ℤ), (n : ℤ), 0) :=
    fun c r m n => phaseMonomial_from_weight q hq c r s w z m n
  fin_cases j <;>
    simp [normalizedSpecialTerms, specialTerm, hmono,
      sub_eq_add_neg, neg_mul]

def normalizedFiniteFactor (P : PhaseData) (q : ℝ) (j : Fin 5)
    (marked : Bool) : RawRational :=
  let special := normalizedSpecialTerms P q j
  let common : Terms :=
    if marked then
      [((6, 0, 6), P.alpha ^ 2 * (q : ℂ) ^ 3 * ((q : ℂ) - 1)),
       ((1, 1, 0), -(P.eta * ((q : ℂ) - 1)))]
    else
      [((0, 0, 0), 1),
       ((6, 0, 6), -(P.alpha ^ 2 * (q : ℂ) ^ 3)),
       ((1, 1, 0), -(P.eta * ((q : ℂ) - 1)))]
  { numerator := ofTerms (common ++ special ++ shiftScale (0, 0, 6) (-1) special)
    denominator := ofTerms
      [((0, 0, 0), 1), ((6, 0, 6), -(P.alpha ^ 2 * (q : ℂ) ^ 4))] }

theorem powerWeight_110 (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    powerWeight q s w z (1, 1, 0) = (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold powerWeight
  norm_num
  rw [Complex.cpow_add _ _ hqC]
  ring

theorem powerWeight_606 (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    powerWeight q s w z (6, 0, 6) = ((q : ℂ) ^ (-s)) ^ 6 * coordV q z := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  unfold powerWeight coordV
  norm_num
  rw [Complex.cpow_add _ _ hqC]
  have hs : -(6 * s) = (6 : ℂ) * (-s) := by ring
  have hz : -(6 * z) = (-6 : ℂ) * z := by ring
  rw [hs, hz, Complex.cpow_ofNat_mul]
  ring

theorem R_weight (P : PhaseData) (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    P.alpha ^ 2 * (q : ℂ) ^ 4 * powerWeight q s w z (6, 0, 6) =
      coordR P q s z := by
  rw [powerWeight_606 q hq, coordR_eq_original P q hq]
  ring

theorem R_div_weight (P : PhaseData) (q : ℝ) (hq : 0 < q) (s w z : ℂ) :
    P.alpha ^ 2 * (q : ℂ) ^ 3 * powerWeight q s w z (6, 0, 6) =
      coordR P q s z / (q : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [← R_weight P q hq s w z]
  field_simp [hqC]

theorem normalized_denominator_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) (marked : Bool) :
    polynomialValue (normalizedFiniteFactor P q j marked).denominator q s w z =
      1 - coordR P q s z := by
  change polynomialValue (ofTerms
    [((0, 0, 0), 1), ((6, 0, 6), -(P.alpha ^ 2 * (q : ℂ) ^ 4))]) q s w z = _
  rw [polynomialValue_ofTerms_weight]
  simp only [termsValue_cons, termsValue_nil, powerWeight_zero, one_mul, add_zero, neg_mul]
  rw [R_weight P q hq]
  ring

theorem normalized_numerator_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) :
    polynomialValue (normalizedFiniteFactor P q j false).numerator q s w z =
      1 - coordR P q s z / (q : ℂ) -
        P.eta * ((q : ℂ) - 1) * (q : ℂ) ^ (-s) * (q : ℂ) ^ (-w) +
        (1 - coordV q z) * specialTerm P q s w j := by
  change polynomialValue (ofTerms
    ([((0, 0, 0), 1), ((6, 0, 6), -(P.alpha ^ 2 * (q : ℂ) ^ 3)),
      ((1, 1, 0), -(P.eta * ((q : ℂ) - 1)))] ++
      normalizedSpecialTerms P q j ++
      shiftScale (0, 0, 6) (-1) (normalizedSpecialTerms P q j))) q s w z = _
  rw [polynomialValue_ofTerms_weight]
  simp only [termsValue_append]
  rw [termsValue_shift6 q hq, normalizedSpecialTerms_value P q hq]
  simp only [termsValue_cons, termsValue_nil, powerWeight_zero, one_mul, add_zero, neg_mul]
  rw [R_div_weight P q hq, powerWeight_110 q hq]
  ring

/-- Exact evaluation of the finite data, with no denominator premise. -/
theorem normalizedFiniteFactor_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) :
    rationalValue (normalizedFiniteFactor P q j false) q s w z =
      ramifiedTableValue P q s w z j := by
  unfold rationalValue ramifiedTableValue
  rw [normalized_numerator_value P q hq, normalized_denominator_value P q hq]

theorem normalized_marked_numerator_weighted (P : PhaseData) (q : ℝ)
    (j : Fin 5) (weight : Exponent → ℂ) :
    weightedValue (normalizedFiniteFactor P q j true).numerator weight =
      weightedValue (normalizedFiniteFactor P q j false).numerator weight -
        weightedValue (normalizedFiniteFactor P q j false).denominator weight := by
  simp [normalizedFiniteFactor, weightedValue_ofTerms, termsValue,
    List.map_append, List.sum_append]
  ring

theorem normalized_marked_value (P : PhaseData) (q : ℝ) (hq : 0 < q)
    (s w z : ℂ) (j : Fin 5) (hR : 1 - coordR P q s z ≠ 0) :
    rationalValue (normalizedFiniteFactor P q j true) q s w z =
      ramifiedTableValue P q s w z j - 1 := by
  have hnum :
      polynomialValue (normalizedFiniteFactor P q j true).numerator q s w z =
        polynomialValue (normalizedFiniteFactor P q j false).numerator q s w z -
          polynomialValue (normalizedFiniteFactor P q j false).denominator q s w z :=
    normalized_marked_numerator_weighted P q j (powerWeight q s w z)
  have hden : polynomialValue (normalizedFiniteFactor P q j false).denominator q s w z ≠ 0 := by
    rw [normalized_denominator_value P q hq]
    exact hR
  have he : polynomialValue (normalizedFiniteFactor P q j true).denominator q s w z =
      polynomialValue (normalizedFiniteFactor P q j false).denominator q s w z := rfl
  unfold rationalValue
  rw [hnum, he, sub_div, div_self hden]
  exact congrArg (fun x : ℂ => x - 1) (normalizedFiniteFactor_value P q hq s w z j)

/-- The constant-nine bound now applies to evaluation of the finite data itself. -/
theorem normalizedFiniteFactor_dynamic_bound (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5) :
    ‖rationalValue (normalizedFiniteFactor P q j false) q s w z - 1‖ ≤
      9 * q ^ (-10 * e) := by
  rw [normalizedFiniteFactor_value P q (by linarith)]
  exact ramified_table_dynamic_bound P q b e hq hb he s w z hs hw hz j

/-- The marked table is the local error term, with the same uniform bound. -/
theorem normalizedMarkedFiniteFactor_dynamic_bound (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) (j : Fin 5) :
    ‖rationalValue (normalizedFiniteFactor P q j true) q s w z‖ ≤
      9 * q ^ (-10 * e) := by
  rw [normalized_marked_value P q (by linarith) s w z j
    (one_sub_R_ne_zero _ (coordR_norm_le_half P q b e hq hb he s z hs hz))]
  exact ramified_table_dynamic_bound P q b e hq hb he s w z hs hw hz j

/-- Bounds for a possibly surviving local coefficient of the target twist. -/
theorem twistCoefficient_norms (q b e : ℝ) (hq : 2 ≤ q)
    (hb : 1 / 2 ≤ b) (he : 0 ≤ e) (s d : ℂ)
    (hs : s.re = b + 16 * e) (hd : ‖d‖ ≤ 1) :
    ‖d * (q : ℂ) ^ (-s)‖ ≤ q ^ (-10 * e) ∧
      ‖d * (q : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hn : ‖d * (q : ℂ) ^ (-s)‖ ≤ q ^ (-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    simp only [Complex.neg_re]
    simpa using mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hqpos.le (-s.re))
  have hp : (q ^ (-s.re)) ^ 2 = q ^ (-2 * s.re) := by
    rw [← Real.rpow_mul_natCast hqpos.le (-s.re) 2]
    congr 1
    ring
  have hsquare : (q ^ (-s.re)) ^ 2 ≤ 1 / 2 := by
    rw [hp]
    calc
      q ^ (-2 * s.re) ≤ q ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hqone (by rw [hs]; linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
      _ = 1 / 2 := by norm_num
  have hm := mul_self_le_mul_self (norm_nonneg (d * (q : ℂ) ^ (-s))) hn
  constructor
  · exact hn.trans (Real.rpow_le_rpow_of_exponent_le hqone (by rw [hs]; linarith))
  · nlinarith [sq_nonneg (‖d * (q : ℂ) ^ (-s)‖ - 3 / 4)]

/-- A surviving linear Euler denominator costs at most a factor four. -/
theorem divided_correction_norm_bound (H D : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hH : ‖H - 1‖ ≤ 9 * t)
    (hD : ‖D‖ ≤ t) (hsmall : ‖D‖ ≤ 3 / 4) :
    ‖H / (1 - D) - 1‖ ≤ 40 * t := by
  have hden : 1 / 4 ≤ ‖(1 : ℂ) - D‖ := by
    have h := norm_sub_norm_le (1 : ℂ) D
    norm_num at h
    linarith
  have hdenpos : 0 < ‖(1 : ℂ) - D‖ := by linarith
  have hdenne : (1 : ℂ) - D ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    norm_num at hden
  have hid : H / (1 - D) - 1 = (H - 1 + D) / (1 - D) := by
    field_simp [hdenne]
    ring
  rw [hid, norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := norm_add_le (H - 1) D
  nlinarith

/-- A ramified-row table with a nonzero twist coefficient still has uniform decay.
The coefficient `d` is the actual local coefficient of the twist when this
statement is applied arithmetically; no multiplicativity of ramified Euler
coefficients is assumed here.
-/
theorem normalizedFiniteFactor_twisted_dynamic_bound (P : PhaseData) (q b e : ℝ)
    (hq : 2 ≤ q) (hb : 1 / 2 ≤ b) (he : 0 ≤ e)
    (s w z d : ℂ) (hs : s.re = b + 16 * e) (hw : w.re = 1 - b - 6 * e)
    (hz : z.re = 17 / 50) (hd : ‖d‖ ≤ 1) (j : Fin 5) :
    ‖rationalValue (normalizedFiniteFactor P q j false) q s w z /
      (1 - d * (q : ℂ) ^ (-s)) - 1‖ ≤ 40 * q ^ (-10 * e) := by
  obtain ⟨hdecay, hsmall⟩ := twistCoefficient_norms q b e hq hb he s d hs hd
  exact divided_correction_norm_bound _ _ _
    (Real.rpow_nonneg (by linarith) _)
    (normalizedFiniteFactor_dynamic_bound P q b e hq hb he s w z hs hw hz j)
    hdecay hsmall

#print axioms powerWeight_zero
#print axioms polynomialValue_ofTerms_weight
#print axioms powerWeight_shift6
#print axioms termsValue_shift6
#print axioms phaseMonomial_from_weight
#print axioms normalizedSpecialTerms_value
#print axioms powerWeight_110
#print axioms powerWeight_606
#print axioms R_weight
#print axioms R_div_weight
#print axioms normalized_denominator_value
#print axioms normalized_numerator_value
#print axioms normalizedFiniteFactor_value
#print axioms normalized_marked_numerator_weighted
#print axioms normalized_marked_value
#print axioms normalizedFiniteFactor_dynamic_bound
#print axioms normalizedMarkedFiniteFactor_dynamic_bound
#print axioms twistCoefficient_norms
#print axioms divided_correction_norm_bound
#print axioms normalizedFiniteFactor_twisted_dynamic_bound

end HBEulerCheckedTable

end
