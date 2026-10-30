import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# General-field local Euler correction algebra

These identities are the field-independent algebra in §6 of
`sources/hecke_seven_eighths_all_characters.tex` (pinned source in `sources/pins.json`).
`localSum` is the displayed local sum in “The general-field local factor”,
attributed there to P (7.19). `normalizedFactor` removes the local factors of
ζ(6z) L(w, χ) / L(s, ψ χ̄). `compensatedFactor` is the displayed replacement
factor G_p immediately before that subsection, without division by P_p.

The principal specialization is V = W = q⁻¹; t is the compensation phase
ψ̄(p) q^s, and its exact unitarity cancellation on the principal row is t D = 1.
Theorems state all denominator hypotheses explicitly and prove a quantitative
local error bound and nonvanishing under an explicit cutoff. They do not
establish the arithmetic realization of P_p or Euler-product convergence.
-/

namespace HeckeGeneral.Arithmetic.LocalCorrection

open scoped ComplexConjugate

variable {F : Type*} [Field F]

/-- The unmarked part of the local sum: P_p - P_p*. -/
def unmarkedPart (V W : F) : F := 1 / (1 - V) + W / (1 - W)

/-- The source's exact local sum, with inverse norm q⁻¹ kept explicit. -/
def localSum (q V W D E : F) : F :=
  unmarkedPart V W +
    E / (1 - E) * ((1 - q⁻¹) / (1 - V) + W) -
    D / (1 - E) * (1 + (q - 1) * W * V / (1 - V))

/-- Local correction H_p after removing the three simple Euler factors. -/
def normalizedFactor (q V W D E : F) : F :=
  (1 - V) * (1 - W) * localSum q V W D E / (1 - D)

/-- The marked part P_p*, defined through the source's unmarked identity. -/
def markedPart (q V W D E : F) : F :=
  localSum q V W D E - unmarkedPart V W

/-- Full compensated factor G_p, valid without dividing by localSum. -/
def compensatedFactor (q V W D E t u : F) : F :=
  ((t - u) * (1 - V) * (1 - W) * markedPart q V W D E -
    u * (1 - V * W)) / (1 - D)

/-- Exact cancellation of the unmarked Euler factors. -/
theorem unmarkedPart_normalization (V W : F)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) :
    (1 - V) * (1 - W) * unmarkedPart V W = 1 - V * W := by
  unfold unmarkedPart
  field_simp
  ring

/-- Expanded correction numerator, before any analytic estimate. -/
theorem normalizedFactor_eq (q V W D E : F)
    (hq : q ≠ 0) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    normalizedFactor q V W D E =
      ((1 - V * W) - E * ((1 - V) * W ^ 2 + (1 - W) / q) -
        D * (1 - W) * (1 - V + (q - 1) * W * V)) /
      ((1 - E) * (1 - D)) := by
  unfold normalizedFactor localSum unmarkedPart
  field_simp
  ring

/-- Principal-locus simplification: neither the row zeta nor its pole is shifted. -/
theorem normalizedFactor_principal (q D E : F)
    (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    normalizedFactor q q⁻¹ q⁻¹ D E =
      (1 - q⁻¹ ^ 2) * (1 - E / q - D * (1 - q⁻¹)) /
        ((1 - E) * (1 - D)) := by
  have hqi : 1 - q⁻¹ ≠ 0 := by
    intro h
    have hi : q⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply hq1
    calc
      q = (q⁻¹)⁻¹ := (inv_inv q).symm
      _ = 1 := by rw [hi, inv_one]
  rw [normalizedFactor_eq q q⁻¹ q⁻¹ D E hq hqi hqi hD hE]
  field_simp
  ring

/-- Compensation algebra; crucially, this identity assumes no P_p ≠ 0. -/
theorem compensatedFactor_eq (q V W D E t u : F)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    compensatedFactor q V W D E t u =
      (t - u) * normalizedFactor q V W D E - t * (1 - V * W) / (1 - D) := by
  have hb := unmarkedPart_normalization V W hV hW
  unfold compensatedFactor markedPart normalizedFactor
  field_simp
  linear_combination -(t - u) * hb

/-- The principal compensated error numerator. Division by H_p is deferred. -/
theorem principal_compensation_error (q D E t : F)
    (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) (htD : t * D = 1) :
    compensatedFactor q q⁻¹ q⁻¹ D E t q⁻¹ +
        normalizedFactor q q⁻¹ q⁻¹ D E =
      (1 - q⁻¹ ^ 2) * (1 - q⁻¹) *
        (E * (t - q⁻¹) - D * (1 - q⁻¹)) / ((1 - E) * (1 - D)) := by
  have hqi : 1 - q⁻¹ ≠ 0 := by
    intro h
    have hi : q⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply hq1
    calc
      q = (q⁻¹)⁻¹ := (inv_inv q).symm
      _ = 1 := by rw [hi, inv_one]
  have hD0 : D ≠ 0 := by
    intro h
    simp [h] at htD
  have ht : t = 1 / D := (eq_div_iff hD0).2 htD
  rw [compensatedFactor_eq q q⁻¹ q⁻¹ D E t q⁻¹ hqi hqi hD,
    normalizedFactor_principal q D E hq hq1 hD hE, ht]
  field_simp
  ring

/-- Exact principal H_p - 1 numerator, exposing the norm-decay terms. -/
theorem principal_normalization_error (q D E : F)
    (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    normalizedFactor q q⁻¹ q⁻¹ D E - 1 =
      (-(q⁻¹ ^ 2) + E * (1 - q⁻¹ + q⁻¹ ^ 3) +
        D * (q⁻¹ + q⁻¹ ^ 2 - q⁻¹ ^ 3) - E * D) /
        ((1 - E) * (1 - D)) := by
  rw [normalizedFactor_principal q D E hq hq1 hD hE]
  field_simp
  ring

/-- The exact phase cancellation at the principal row for an arbitrary unit phase. -/
theorem unit_phase_cancellation (ψ A : ℂ) (hψ : ‖ψ‖ = 1) (hA : A ≠ 0) :
    (conj ψ * A) * (ψ * A⁻¹) = 1 := by
  calc
    (conj ψ * A) * (ψ * A⁻¹) = (conj ψ * ψ) * (A * A⁻¹) := by ring
    _ = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        hψ, mul_inv_cancel₀ hA]
      norm_num

/-- Real prime norm q > 1 supplies the algebraic principal denominator conditions. -/
theorem principal_norm_denominators (q : ℝ) (hq : 1 < q) :
    (q : ℂ) ≠ 0 ∧ (q : ℂ) ≠ 1 ∧ 1 - (q : ℂ)⁻¹ ≠ 0 := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hq1 : q ≠ 1 := ne_of_gt hq
  have hc0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0
  have hc1 : (q : ℂ) ≠ 1 := by
    intro h
    apply hq1
    exact Complex.ofReal_injective (by simpa using h)
  refine ⟨hc0, hc1, ?_⟩
  intro h
  have hi : (q : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
  apply hc1
  calc
    (q : ℂ) = ((q : ℂ)⁻¹)⁻¹ := (inv_inv _).symm
    _ = 1 := by rw [hi, inv_one]

/-- Half-size Euler perturbations give a fixed lower bound for the product denominator. -/
theorem principal_denominator_norm (D E : ℂ)
    (hD : ‖D‖ ≤ 1 / 2) (hE : ‖E‖ ≤ 1 / 2) :
    1 / 4 ≤ ‖(1 - E) * (1 - D)‖ := by
  have hd := norm_sub_norm_le (1 : ℂ) D
  have he := norm_sub_norm_le (1 : ℂ) E
  rw [norm_one] at hd he
  rw [norm_mul]
  nlinarith [norm_nonneg (1 - D), norm_nonneg (1 - E)]

/-- A concrete principal error bound, independent of the number field and target phase.

For the manuscript E has size q^(3-6 Re(s)) and D size q^(-Re(s)).
The statement here only uses their actual complex norms.
-/
theorem principal_normalization_norm_bound (q : ℝ) (D E : ℂ)
    (hq : 1 < q) (hD : ‖D‖ ≤ 1 / 2) (hE : ‖E‖ ≤ 1 / 2) :
    ‖normalizedFactor (q : ℂ) (q : ℂ)⁻¹ (q : ℂ)⁻¹ D E - 1‖ ≤
      8 * (q⁻¹ ^ 2 + q⁻¹ * ‖D‖ + ‖E‖) := by
  obtain ⟨hc0, hc1, _⟩ := principal_norm_denominators q hq
  have hden := principal_denominator_norm D E hD hE
  have hd : 1 - D ≠ 0 := by
    intro h
    have hh := norm_sub_norm_le (1 : ℂ) D
    rw [h, norm_zero, norm_one] at hh
    linarith
  have he : 1 - E ≠ 0 := by
    intro h
    have hh := norm_sub_norm_le (1 : ℂ) E
    rw [h, norm_zero, norm_one] at hh
    linarith
  let a : ℝ := q⁻¹
  have ha0 : 0 ≤ a := inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hq))
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact inv_le_one_of_one_le₀ (le_of_lt hq)
  have hasq : a ^ 2 ≤ a := by nlinarith
  have hacube : a ^ 3 ≤ a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hasq ha0]
  have ce0 : 0 ≤ 1 - a + a ^ 3 := by positivity
  have ce1 : 1 - a + a ^ 3 ≤ 1 := by nlinarith
  have cd0 : 0 ≤ a + a ^ 2 - a ^ 3 := by nlinarith
  have cd1 : a + a ^ 2 - a ^ 3 ≤ 2 * a := by nlinarith
  have hnum :
      ‖-((a : ℂ) ^ 2) + E * (1 - (a : ℂ) + (a : ℂ) ^ 3) +
          D * ((a : ℂ) + (a : ℂ) ^ 2 - (a : ℂ) ^ 3) - E * D‖ ≤
        2 * (a ^ 2 + a * ‖D‖ + ‖E‖) := by
    have hn := norm_sub_le
      (-((a : ℂ) ^ 2) + E * (1 - (a : ℂ) + (a : ℂ) ^ 3) +
        D * ((a : ℂ) + (a : ℂ) ^ 2 - (a : ℂ) ^ 3)) (E * D)
    have hn2 := norm_add_le
      (-((a : ℂ) ^ 2) + E * (1 - (a : ℂ) + (a : ℂ) ^ 3))
      (D * ((a : ℂ) + (a : ℂ) ^ 2 - (a : ℂ) ^ 3))
    have hn3 := norm_add_le (-((a : ℂ) ^ 2))
      (E * (1 - (a : ℂ) + (a : ℂ) ^ 3))
    have hec : ‖(1 : ℂ) - (a : ℂ) + (a : ℂ) ^ 3‖ = 1 - a + a ^ 3 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
        ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ce0]
    have hdc : ‖(a : ℂ) + (a : ℂ) ^ 2 - (a : ℂ) ^ 3‖ = a + a ^ 2 - a ^ 3 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_pow,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg cd0]
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha0, hec, hdc] at hn hn2 hn3
    nlinarith [norm_nonneg D, norm_nonneg E, sq_nonneg a,
      mul_le_mul_of_nonneg_left ce1 (norm_nonneg E),
      mul_le_mul_of_nonneg_left cd1 (norm_nonneg D)]
  rw [principal_normalization_error (q : ℂ) D E hc0 hc1 hd he, norm_div]
  have hqi : (q : ℂ)⁻¹ = (a : ℂ) := by simp [a]
  rw [hqi]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden)).2
  have hsum : 0 ≤ a ^ 2 + a * ‖D‖ + ‖E‖ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hsum)
  dsimp [a] at hnum hmul
  nlinarith

/-- A quantitative local cutoff makes division by H_p legitimate. -/
theorem principal_normalization_norm_lower (q : ℝ) (D E : ℂ)
    (hq : 1 < q) (hD : ‖D‖ ≤ 1 / 2) (hE : ‖E‖ ≤ 1 / 2)
    (hsmall : q⁻¹ ^ 2 + q⁻¹ * ‖D‖ + ‖E‖ ≤ 1 / 16) :
    1 / 2 ≤ ‖normalizedFactor (q : ℂ) (q : ℂ)⁻¹ (q : ℂ)⁻¹ D E‖ := by
  have hb := principal_normalization_norm_bound q D E hq hD hE
  have hr := norm_sub_norm_le (1 : ℂ)
    (normalizedFactor (q : ℂ) (q : ℂ)⁻¹ (q : ℂ)⁻¹ D E)
  rw [norm_one, norm_sub_rev] at hr
  linarith

/-- The local normalized factor is nonzero under the explicit cutoff. -/
theorem principal_normalization_ne_zero (q : ℝ) (D E : ℂ)
    (hq : 1 < q) (hD : ‖D‖ ≤ 1 / 2) (hE : ‖E‖ ≤ 1 / 2)
    (hsmall : q⁻¹ ^ 2 + q⁻¹ * ‖D‖ + ‖E‖ ≤ 1 / 16) :
    normalizedFactor (q : ℂ) (q : ℂ)⁻¹ (q : ℂ)⁻¹ D E ≠ 0 := by
  intro h
  have hb := principal_normalization_norm_lower q D E hq hD hE hsmall
  rw [h, norm_zero] at hb
  norm_num at hb

end HeckeGeneral.Arithmetic.LocalCorrection
