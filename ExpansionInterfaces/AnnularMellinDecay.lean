import ExpansionInterfaces.AnnularMellinProfile
import HeckeSkeleton.ExpansionModels.LogTwistedProfiles
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Uniform Mellin-strip decay and arbitrary finite-height tail orders

The constants are derived from the smooth physical annular profile.  The
only Fourier input is the independently proved compact exponential-twist
seminorm theorem, not an assumed Mellin decay estimate.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open ExpansionRecipe.LogProfile
open scoped Classical BigOperators FourierTransform SchwartzMap ContDiff

namespace AnnularProfile

def logRadius (W : AnnularProfile) : ℝ := |Real.log W.lower| + |Real.log W.upper|

theorem logRadius_nonneg (W : AnnularProfile) : 0 ≤ W.logRadius :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem baseLog_tsupport (W : AnnularProfile) :
    tsupport (W.logProfileFun 0) ⊆ Icc (-W.logRadius) W.logRadius := by
  apply closure_minimal ?_ isClosed_Icc
  intro u hu
  have hW : W.function (Real.exp (-u)) ≠ 0 := by
    intro hz
    exact hu (by simp [AnnularProfile.logProfileFun, hz])
  have hb := W.supported hW
  have hlo := Real.log_le_log W.lower_pos hb.1
  have hhi := Real.log_le_log (Real.exp_pos (-u)) hb.2
  rw [Real.log_exp] at hlo hhi
  unfold logRadius
  constructor <;> linarith [le_abs_self (Real.log W.upper), neg_le_abs (Real.log W.lower),
    abs_nonneg (Real.log W.lower), abs_nonneg (Real.log W.upper)]

theorem compactExpTwist_eq_logProfile (W : AnnularProfile) (σ : ℝ) :
    compactExpTwist (W.logProfileFun 0) (W.logProfile_compact 0)
      (W.logProfile_smooth 0) ((-σ : ℝ) : ℂ) = W.logProfile σ := by
  ext u
  change W.logProfileFun 0 u * linearExp ((-σ : ℝ) : ℂ) u = W.logProfileFun σ u
  simp only [AnnularProfile.logProfileFun, neg_zero, zero_mul, Real.exp_zero, one_smul]
  change W.function (Real.exp (-u)) * Complex.exp (((-σ : ℝ) : ℂ) * (u : ℂ)) =
    (Real.exp (-σ * u) : ℂ) * W.function (Real.exp (-u))
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  exact mul_comm _ _

/-- Uniform for every real part in one fixed compact strip. -/
theorem uniform_strip_decay (W : AnnularProfile) (lo hi : ℝ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ J * ‖mellin W.function (vertical σ t)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_real_exp_twist_uniform_fourier_decay
    (W.logProfileFun 0) (W.logProfile_compact 0) (W.logProfile_smooth 0)
    (|lo| + |hi|) W.logRadius (by positivity) W.logRadius_nonneg W.baseLog_tsupport J
  refine ⟨(1 + 2 * Real.pi) ^ J * C, mul_nonneg (by positivity) hC, ?_⟩
  intro σ hσ t
  have hσabs : |σ| ≤ |lo| + |hi| := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, neg_le_abs lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
  have htw := hb (-σ) (by simpa only [abs_neg] using hσabs) (t / (2 * Real.pi))
  rw [W.compactExpTwist_eq_logProfile σ] at htw
  change (1 + ‖t / (2 * Real.pi)‖) ^ J *
    ‖𝓕 (W.logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖ ≤ C at htw
  rw [W.mellin_vertical_eq_fourier σ t]
  have hπ : 0 < 2 * Real.pi := by positivity
  have ht : |t| = (2 * Real.pi) * ‖t / (2 * Real.pi)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hπ]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + ‖t / (2 * Real.pi)‖) := by
    nlinarith [norm_nonneg (t / (2 * Real.pi))]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|) hbase J
  calc
    _ ≤ ((1 + 2 * Real.pi) ^ J * (1 + ‖t / (2 * Real.pi)‖) ^ J) *
        ‖𝓕 (W.logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (by simpa only [mul_pow] using hp) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ J *
        ((1 + ‖t / (2 * Real.pi)‖) ^ J *
          ‖𝓕 (W.logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htw (by positivity)

theorem weighted_le_of_decay {v C t : ℝ} (hv : 0 ≤ v) (N : ℕ)
    (hb : (1 + |t|) ^ (N + 2) * v ≤ C) :
    |t| ^ N * v ≤ C * (1 + |t|) ^ (-2 : ℝ) := by
  have hpos : 0 < 1 + |t| := by positivity
  have hpow : |t| ^ N ≤ (1 + |t|) ^ N :=
    pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
  have hh : (1 + |t|) ^ 2 * (|t| ^ N * v) ≤ C := by
    calc
      _ ≤ (1 + |t|) ^ 2 * ((1 + |t|) ^ N * v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hv) (by positivity)
      _ = (1 + |t|) ^ (N + 2) * v := by rw [pow_add]; ring
      _ ≤ C := hb
  rw [Real.rpow_neg hpos.le, Real.rpow_two, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hpos 2)).mpr (by nlinarith [hh])

theorem decayWeight_integrable :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp))

/-- Every polynomial Mellin moment is integrable and bounded uniformly
throughout the chosen compact strip. -/
theorem uniform_weighted_moment (W : AnnularProfile) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc lo hi,
      Integrable (fun t : ℝ => |t| ^ N * ‖mellin W.function (vertical σ t)‖) ∧
      (∫ t : ℝ, |t| ^ N * ‖mellin W.function (vertical σ t)‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := W.uniform_strip_decay lo hi (N + 2)
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hI : 0 ≤ I := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨C * I, mul_nonneg hC hI, ?_⟩
  intro σ hσ
  have hpoint (t : ℝ) : |t| ^ N * ‖mellin W.function (vertical σ t)‖ ≤
      C * (1 + |t|) ^ (-2 : ℝ) := weighted_le_of_decay (norm_nonneg _) N (hb σ hσ t)
  have hcont : Continuous (fun t : ℝ => |t| ^ N * ‖mellin W.function (vertical σ t)‖) :=
    (continuous_abs.pow N).mul
      (W.mellin_differentiable.continuous.comp (by unfold vertical; fun_prop)).norm
  have hm := decayWeight_integrable.const_mul C
  have hi : Integrable (fun t : ℝ => |t| ^ N * ‖mellin W.function (vertical σ t)‖) := by
    apply hm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |t| ^ N * ‖mellin W.function (vertical σ t)‖)] using hpoint t
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hm hpoint
  simpa only [integral_const_mul, I] using hh

theorem uniform_tail (W : AnnularProfile) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc lo hi, ∀ H : ℝ, 0 < H →
      (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical σ t)‖) ≤ C / H ^ N := by
  obtain ⟨C, hC, hb⟩ := W.uniform_weighted_moment lo hi N
  refine ⟨C, hC, ?_⟩
  intro σ hσ H hH
  have hm : MeasurableSet {t : ℝ | H < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  apply (le_div_iff₀ (pow_pos hH N)).mpr
  calc
    _ = ∫ t : ℝ in {t | H < |t|}, H ^ N * ‖mellin W.function (vertical σ t)‖ := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t : ℝ in {t | H < |t|}, |t| ^ N * ‖mellin W.function (vertical σ t)‖ :=
      setIntegral_mono_on ((W.vertical_norm_integrable σ).const_mul (H ^ N)).integrableOn
        (hb σ hσ).1.integrableOn hm (fun t ht =>
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH.le ht.le N) (norm_nonneg _))
    _ ≤ ∫ t : ℝ, |t| ^ N * ‖mellin W.function (vertical σ t)‖ :=
      setIntegral_le_integral (hb σ hσ).1 (ae_of_all _ fun t => by positivity)
    _ ≤ C := (hb σ hσ).2

end AnnularProfile
end ExpansionInterfaces.Mellin
