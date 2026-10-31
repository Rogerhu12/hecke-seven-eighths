import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual three-height truncation from rapid decay

A bound with two spare powers in each height implies joint absolute
integrability and bounds the literal integral outside the retained cube.
The fixed height mass is independent of every arithmetic row, scale and
cutoff.  The full-minus-cube identity is proved by the measurable partition,
not used to define the tail.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalRapidTruncation

open MeasureTheory Set
open scoped BigOperators

abbrev Heights := ℝ × ℝ × ℝ

def heightWeight (n : ℕ) (t : Heights) : ℝ :=
  (1 + |t.1|) ^ n * (1 + |t.2.1|) ^ n * (1 + |t.2.2|) ^ n

def heightCube (H : ℝ) : Set Heights := Icc (-H) H ×ˢ (Icc (-H) H ×ˢ Icc (-H) H)

def heightEnvelope (t : Heights) : ℝ :=
  ((1 + |t.1|) ^ 2)⁻¹ * ((1 + |t.2.1|) ^ 2)⁻¹ * ((1 + |t.2.2|) ^ 2)⁻¹

def heightMass : ℝ := ∫ t : Heights, heightEnvelope t

theorem measurableSet_heightCube (H : ℝ) : MeasurableSet (heightCube H) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem mem_heightCube_iff (H : ℝ) (t : Heights) :
    t ∈ heightCube H ↔ |t.1| ≤ H ∧ |t.2.1| ≤ H ∧ |t.2.2| ≤ H := by
  simp only [heightCube, mem_prod, mem_Icc, abs_le]

theorem heightWeight_pos (n : ℕ) (t : Heights) : 0 < heightWeight n t := by
  unfold heightWeight
  positivity

theorem one_le_heightWeight (n : ℕ) (t : Heights) : 1 ≤ heightWeight n t := by
  have h1 : 1 ≤ (1 + |t.1|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.1])
  have h2 : 1 ≤ (1 + |t.2.1|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.2.1])
  have h3 : 1 ≤ (1 + |t.2.2|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.2.2])
  exact one_le_mul (one_le_mul h1 h2) h3

theorem heightWeight_add (m n : ℕ) (t : Heights) :
    heightWeight (m + n) t = heightWeight m t * heightWeight n t := by
  simp only [heightWeight, pow_add]
  ring

theorem heightEnvelope_eq_inv (t : Heights) : heightEnvelope t = (heightWeight 2 t)⁻¹ := by
  simp only [heightEnvelope, heightWeight, mul_inv]

theorem heightEnvelope_nonneg (t : Heights) : 0 ≤ heightEnvelope t := by
  rw [heightEnvelope_eq_inv]
  exact inv_nonneg.mpr (heightWeight_pos 2 t).le

theorem integrable_heightEnvelope : Integrable heightEnvelope := by
  have h : Integrable (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) := by
    have hi := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
    convert hi using 1
    funext t
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
  simpa only [heightEnvelope, Measure.volume_eq_prod, mul_assoc] using h.mul_prod (h.mul_prod h)

theorem heightMass_nonneg : 0 ≤ heightMass := integral_nonneg heightEnvelope_nonneg

theorem heightWeight_lower_outside (n : ℕ) {H : ℝ} (hH : 0 ≤ H)
    {t : Heights} (ht : t ∉ heightCube H) : (1 + H) ^ n ≤ heightWeight n t := by
  have h1 : 1 ≤ (1 + |t.1|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.1])
  have h2 : 1 ≤ (1 + |t.2.1|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.2.1])
  have h3 : 1 ≤ (1 + |t.2.2|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t.2.2])
  have hp1 : (1 + |t.1|) ^ n ≤ heightWeight n t := by
    change _ ≤ (1 + |t.1|) ^ n * (1 + |t.2.1|) ^ n * (1 + |t.2.2|) ^ n
    calc
      _ = (1 + |t.1|) ^ n * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hp2 : (1 + |t.2.1|) ^ n ≤ heightWeight n t := by
    change _ ≤ (1 + |t.1|) ^ n * (1 + |t.2.1|) ^ n * (1 + |t.2.2|) ^ n
    calc
      _ = 1 * (1 + |t.2.1|) ^ n * 1 := by ring
      _ ≤ _ := by gcongr
  have hp3 : (1 + |t.2.2|) ^ n ≤ heightWeight n t := by
    change _ ≤ (1 + |t.1|) ^ n * (1 + |t.2.1|) ^ n * (1 + |t.2.2|) ^ n
    calc
      _ = 1 * 1 * (1 + |t.2.2|) ^ n := by ring
      _ ≤ _ := by gcongr
  have hlarge : H < |t.1| ∨ H < |t.2.1| ∨ H < |t.2.2| := by
    simpa only [mem_heightCube_iff, not_and_or, not_le] using ht
  rcases hlarge with h | h | h
  · exact (pow_le_pow_left₀ (by linarith) (by linarith : 1 + H ≤ 1 + |t.1|) n).trans hp1
  · exact (pow_le_pow_left₀ (by linarith) (by linarith : 1 + H ≤ 1 + |t.2.1|) n).trans hp2
  · exact (pow_le_pow_left₀ (by linarith) (by linarith : 1 + H ≤ 1 + |t.2.2|) n).trans hp3

theorem norm_le_envelope_of_rapid {f : Heights → ℂ} (n : ℕ) (M : ℝ)
    (hb : ∀ t : Heights, heightWeight (n + 2) t * ‖f t‖ ≤ M)
    (t : Heights) {L : ℝ} (hL : 0 < L) (hLt : L ≤ heightWeight n t) :
    ‖f t‖ ≤ (M / L) * heightEnvelope t := by
  have hW := heightWeight_pos 2 t
  have hmul : ‖f t‖ * (L * heightWeight 2 t) ≤ M := by
    calc
      _ = L * (heightWeight 2 t * ‖f t‖) := by ring
      _ ≤ heightWeight n t * (heightWeight 2 t * ‖f t‖) :=
        mul_le_mul_of_nonneg_right hLt (mul_nonneg hW.le (norm_nonneg _))
      _ = heightWeight (n + 2) t * ‖f t‖ := by rw [heightWeight_add]; ring
      _ ≤ M := hb t
  calc
    ‖f t‖ ≤ M / (L * heightWeight 2 t) := (le_div_iff₀ (mul_pos hL hW)).mpr hmul
    _ = (M / L) * heightEnvelope t := by
      rw [heightEnvelope_eq_inv]
      simp only [div_eq_mul_inv, mul_inv, mul_assoc]

theorem integrable_of_rapid {f : Heights → ℂ} (hf : AEStronglyMeasurable f)
    (n : ℕ) (M : ℝ) (hb : ∀ t : Heights, heightWeight (n + 2) t * ‖f t‖ ≤ M) :
    Integrable f := by
  apply (integrable_heightEnvelope.const_mul M).mono' hf
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [div_one] using norm_le_envelope_of_rapid n M hb t zero_lt_one (one_le_heightWeight n t))

theorem norm_tail_integral_le {f : Heights → ℂ} (hf : AEStronglyMeasurable f)
    (n : ℕ) (M : ℝ) (hb : ∀ t : Heights, heightWeight (n + 2) t * ‖f t‖ ≤ M)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖∫ t in (heightCube H)ᶜ, f t‖ ≤ M * heightMass / (1 + H) ^ n := by
  have hi := integrable_of_rapid hf n M hb
  have hM : 0 ≤ M :=
    (mul_nonneg (heightWeight_pos (n + 2) (0, 0, 0)).le (norm_nonneg _)).trans (hb (0, 0, 0))
  have hp : 0 < (1 + H) ^ n := pow_pos (by linarith) n
  have hdom := (integrable_heightEnvelope.const_mul (M / (1 + H) ^ n)).integrableOn
  calc
    _ ≤ ∫ t in (heightCube H)ᶜ, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in (heightCube H)ᶜ, (M / (1 + H) ^ n) * heightEnvelope t :=
      setIntegral_mono_on hi.norm.integrableOn hdom (measurableSet_heightCube H).compl
        (fun t ht => norm_le_envelope_of_rapid n M hb t hp
          (heightWeight_lower_outside n hH ht))
    _ = (M / (1 + H) ^ n) * ∫ t in (heightCube H)ᶜ, heightEnvelope t := integral_const_mul _ _
    _ ≤ (M / (1 + H) ^ n) * heightMass :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral integrable_heightEnvelope
          (Filter.Eventually.of_forall heightEnvelope_nonneg)) (div_nonneg hM hp.le)
    _ = _ := by ring

theorem norm_full_sub_cube_le {f : Heights → ℂ} (hf : AEStronglyMeasurable f)
    (n : ℕ) (M : ℝ) (hb : ∀ t : Heights, heightWeight (n + 2) t * ‖f t‖ ≤ M)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖(∫ t : Heights, f t) - ∫ t in heightCube H, f t‖ ≤ M * heightMass / (1 + H) ^ n := by
  have hi := integrable_of_rapid hf n M hb
  rw [← integral_add_compl (measurableSet_heightCube H) hi, add_sub_cancel_left]
  exact norm_tail_integral_le hf n M hb hH

/-- Continuous kernel version for the actual analytic row applications. -/
theorem continuous_rapid_truncation {f : Heights → ℂ} (hf : Continuous f)
    (n : ℕ) (M : ℝ) (hb : ∀ t : Heights, heightWeight (n + 2) t * ‖f t‖ ≤ M)
    {H : ℝ} (hH : 0 ≤ H) :
    Integrable f ∧ ‖(∫ t : Heights, f t) - ∫ t in heightCube H, f t‖ ≤
      M * heightMass / (1 + H) ^ n :=
  ⟨integrable_of_rapid hf.aestronglyMeasurable n M hb,
    norm_full_sub_cube_le hf.aestronglyMeasurable n M hb hH⟩

end Expansion.PhysicalRapidTruncation

#print axioms Expansion.PhysicalRapidTruncation.continuous_rapid_truncation
