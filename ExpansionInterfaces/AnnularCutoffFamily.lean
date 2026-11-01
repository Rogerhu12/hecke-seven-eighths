import ExpansionInterfaces.AnnularContourUniform
import HeckeSkeleton.ExpansionModels.CutoffLogProfile

/-!
# A common Mellin constant for the actual scaled cutoff family

The inverse detector uses `W(x) V(R x)`, with a scale `R` that changes
between blocks.  This file chooses its Mellin constant before `R`, all
real parts in a fixed strip, and all contour heights.  The proof works for
every nonnegative `R`: the original one-sided cutoff is replaced by its
Schwartz extension only at nonnegative arguments, where the values agree.
-/

set_option autoImplicit false
noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open ExpansionRecipe.LogProfile
open scoped Classical BigOperators FourierTransform SchwartzMap ContDiff

namespace AnnularProfile

/-- The unchanged physical cutoff profile in the inverse detector. -/
def cutoffFamily (W : AnnularProfile) (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (R : ℝ) : AnnularProfile where
  function x := W.function x * V (R * x)
  lower := W.lower
  upper := W.upper
  lower_pos := W.lower_pos
  lower_le_upper := W.lower_le_upper
  smooth := W.smooth.mul (hV.comp (contDiff_const.mul contDiff_id))
  supported := fun _ hx => W.supported (mul_ne_zero_iff.mp hx).1

@[simp] theorem cutoffFamily_apply (W : AnnularProfile) (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V) (R x : ℝ) :
    (W.cutoffFamily V hV R).function x = W.function x * V (R * x) := rfl

theorem scaled_cutoff_reflected_derivatives (V : ℝ → ℂ)
    (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ j (fun z => V (R * Real.exp (-z))) y‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := scaled_schwartz_derivatives (cutoffSchwartz V hV hzero) K
  refine ⟨C, hC, ?_⟩
  intro R hR j hj y
  have heq : (fun z : ℝ => V (R * Real.exp (-z))) =
      fun z : ℝ => cutoffSchwartz V hV hzero (R * Real.exp (-z)) := by
    funext z
    exact (cutoffSchwartzFun_eq_nonneg V hone
      (mul_nonneg hR (Real.exp_pos (-z)).le)).symm
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv j
    (fun z => (fun u => cutoffSchwartz V hV hzero (R * Real.exp u)) (-z)) y‖ ≤ C
  rw [iteratedDeriv_comp_neg j
    (fun u : ℝ => cutoffSchwartz V hV hzero (R * Real.exp u)) y, norm_smul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb R hR j hj (-y)

theorem cutoffFamily_baseLog_uniform_derivatives (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ j ((W.cutoffFamily V hV R).logProfileFun 0) y‖ ≤ C := by
  obtain ⟨CW, hCW, hbW⟩ := (W.logProfile_compact 0).exists_bound_iteratedFDeriv
    (W.logProfile_smooth 0) K
  obtain ⟨CV, hCV, hbV⟩ := scaled_cutoff_reflected_derivatives V hV hone hzero K
  refine ⟨(2 : ℝ) ^ K * CW * CV, by positivity, ?_⟩
  intro R hR j hj y
  have hv : ContDiff ℝ ∞ (fun z => V (R * Real.exp (-z))) :=
    hV.comp (by fun_prop)
  have hp := product_derivative_bound (W.logProfileFun 0)
    (fun z => V (R * Real.exp (-z))) (W.logProfile_smooth 0) hv
    CW CV hCW hCV K j hj y (fun i hi => hbW i hi y) (fun i hi => hbV R hR i hi y)
  have heq : (W.cutoffFamily V hV R).logProfileFun 0 =
      fun z => W.logProfileFun 0 z * V (R * Real.exp (-z)) := by
    funext z
    simp only [AnnularProfile.logProfileFun, cutoffFamily_apply, neg_zero,
      zero_mul, Real.exp_zero, one_smul]
  rw [heq]
  exact hp

/-- Every logarithmic Schwartz seminorm has a single bound for the whole
scaled cutoff family and all real exponential twists in a fixed interval. -/
theorem cutoffFamily_uniform_seminorm (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (H : ℝ) (hH : 0 ≤ H) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ : ℝ, |σ| ≤ H →
      ∀ k j : ℕ, j ≤ K →
        SchwartzMap.seminorm ℝ k j ((W.cutoffFamily V hV R).logProfile σ) ≤
          W.logRadius ^ k * C := by
  obtain ⟨CΩ, hCΩ, hbΩ⟩ := W.cutoffFamily_baseLog_uniform_derivatives
    V hV hone hzero K
  have hlogRadius : 0 ≤ W.logRadius := W.logRadius_nonneg
  let CE := (1 + H) ^ K * Real.exp (H * W.logRadius)
  refine ⟨(2 : ℝ) ^ K * CΩ * CE, by dsimp [CE]; positivity, ?_⟩
  intro R hR σ hσ k j hj
  let WR := W.cutoffFamily V hV R
  rw [← WR.compactExpTwist_eq_logProfile σ]
  apply SchwartzMap.seminorm_le_bound ℝ k j _ (by dsimp [CE]; positivity)
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ j
    (fun y => WR.logProfileFun 0 y * linearExp ((-σ : ℝ) : ℂ) y) y‖ ≤ _
  by_cases hzero' : ‖iteratedFDeriv ℝ j
      (fun y => WR.logProfileFun 0 y * linearExp ((-σ : ℝ) : ℂ) y) y‖ = 0
  · rw [hzero', mul_zero]
    dsimp [CE]
    positivity
  have hs : y ∈ tsupport (WR.logProfileFun 0) := tsupport_mul_subset_left
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hzero'))
  have hy : |y| ≤ W.logRadius := abs_le.mpr (WR.baseLog_tsupport hs)
  have he (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (linearExp ((-σ : ℝ) : ℂ)) y‖ ≤ CE := by
    have hh := linearExp_window_derivative_le H W.logRadius hH W.logRadius_nonneg
      K i hi ((-σ : ℝ) : ℂ) (by simpa using hσ) y hy
    simpa only [Complex.ofReal_im, abs_zero, add_zero, one_pow, mul_one] using hh
  have hb := product_derivative_bound (WR.logProfileFun 0)
    (linearExp ((-σ : ℝ) : ℂ)) (WR.logProfile_smooth 0)
    (linearExp_smooth ((-σ : ℝ) : ℂ)) CΩ CE hCΩ (by dsimp [CE]; positivity)
    K j hj y (fun i hi => hbΩ R hR i hi y) he
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using
    (pow_le_pow_left₀ (abs_nonneg y) hy k)) hb (norm_nonneg _)
    (pow_nonneg W.logRadius_nonneg k)

theorem cutoffFamily_uniform_fourier_decay (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (H : ℝ) (hH : 0 ≤ H) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ : ℝ, |σ| ≤ H → ∀ t : ℝ,
      (1 + ‖t‖) ^ J * ‖𝓕 ((W.cutoffFamily V hV R).logProfile σ) t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := W.cutoffFamily_uniform_seminorm V hV hone hzero H hH J
  have hlogRadius : 0 ≤ W.logRadius := W.logRadius_nonneg
  let C' := (1 + W.logRadius ^ integrationPower) * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ) ^ J * (fourierSeminormConstant 0 C' + fourierSeminormConstant J C'),
    mul_nonneg (by positivity) (add_nonneg (fourierSeminormConstant_nonneg 0 C' hC')
      (fourierSeminormConstant_nonneg J C' hC')), ?_⟩
  intro R hR σ hσ t
  let g := (W.cutoffFamily V hV R).logProfile σ
  have hseminorm (i : ℕ) (hi : i ≤ J) :
      SchwartzMap.seminorm ℝ 0 i g + SchwartzMap.seminorm ℝ integrationPower i g ≤ C' := by
    have h0 := hb R hR σ hσ 0 i hi
    have hp := hb R hR σ hσ integrationPower i hi
    simp only [pow_zero, one_mul] at h0
    dsimp [C']
    linarith
  have h0 : ‖(𝓕 g) t‖ ≤ fourierSeminormConstant 0 C' := by
    have he := SchwartzMap.le_seminorm ℝ 0 0 (𝓕 g) t
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le g 0 C' hC' (fun i hi => hseminorm i (by omega)))
  have hJ : ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤ fourierSeminormConstant J C' := by
    have he := SchwartzMap.le_seminorm ℝ J 0 (𝓕 g) t
    simp only [norm_iteratedFDeriv_zero] at he
    exact he.trans (fourier_seminorm_le g J C' hC' hseminorm)
  calc
    _ ≤ ((2 : ℝ) ^ J * (1 + ‖t‖ ^ J)) * ‖(𝓕 g) t‖ :=
      mul_le_mul_of_nonneg_right (one_add_norm_pow_le t J) (norm_nonneg _)
    _ = (2 : ℝ) ^ J * (‖(𝓕 g) t‖ + ‖t‖ ^ J * ‖(𝓕 g) t‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hJ) (by positivity)

/-- A Mellin-strip bound chosen before the cutoff scale `R`. -/
theorem cutoffFamily_uniform_strip_decay (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ J * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := W.cutoffFamily_uniform_fourier_decay
    V hV hone hzero (|lo| + |hi|) (by positivity) J
  refine ⟨(1 + 2 * Real.pi) ^ J * C, mul_nonneg (by positivity) hC, ?_⟩
  intro R hR σ hσ t
  have hσabs : |σ| ≤ |lo| + |hi| := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, neg_le_abs lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
  have htw := hb R hR σ hσabs (t / (2 * Real.pi))
  change (1 + ‖t / (2 * Real.pi)‖) ^ J *
    ‖𝓕 ((W.cutoffFamily V hV R).logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖ ≤ C at htw
  rw [(W.cutoffFamily V hV R).mellin_vertical_eq_fourier σ t]
  have hπ : 0 < 2 * Real.pi := by positivity
  have ht : |t| = (2 * Real.pi) * ‖t / (2 * Real.pi)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hπ]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + ‖t / (2 * Real.pi)‖) := by
    nlinarith [norm_nonneg (t / (2 * Real.pi))]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|) hbase J
  calc
    _ ≤ ((1 + 2 * Real.pi) ^ J * (1 + ‖t / (2 * Real.pi)‖) ^ J) *
        ‖𝓕 ((W.cutoffFamily V hV R).logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (by simpa only [mul_pow] using hp) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ J *
        ((1 + ‖t / (2 * Real.pi)‖) ^ J *
          ‖𝓕 ((W.cutoffFamily V hV R).logProfile σ : ℝ → ℂ) (t / (2 * Real.pi))‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htw (by positivity)

theorem cutoffFamily_uniform_weighted_moment (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ ∈ Icc lo hi,
      Integrable (fun t : ℝ => |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ∧
      (∫ t : ℝ, |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := W.cutoffFamily_uniform_strip_decay V hV hone hzero lo hi (N + 2)
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hI : 0 ≤ I := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨C * I, mul_nonneg hC hI, ?_⟩
  intro R hR σ hσ
  have hpoint (t : ℝ) : |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ ≤
      C * (1 + |t|) ^ (-2 : ℝ) := weighted_le_of_decay (norm_nonneg _) N (hb R hR σ hσ t)
  have hcont : Continuous (fun t : ℝ => |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) :=
    (continuous_abs.pow N).mul
      ((W.cutoffFamily V hV R).mellin_differentiable.continuous.comp (by unfold vertical; fun_prop)).norm
  have hm := decayWeight_integrable.const_mul C
  have hi : Integrable (fun t : ℝ => |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) := by
    apply hm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖)] using hpoint t
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hm hpoint
  simpa only [integral_const_mul, I] using hh

theorem cutoffFamily_uniform_tail (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ ∈ Icc lo hi, ∀ H : ℝ, 0 < H →
      (∫ t : ℝ in {t | H < |t|}, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ C / H ^ N := by
  obtain ⟨C, hC, hb⟩ := W.cutoffFamily_uniform_weighted_moment V hV hone hzero lo hi N
  refine ⟨C, hC, ?_⟩
  intro R hR σ hσ H hH
  have hm : MeasurableSet {t : ℝ | H < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  apply (le_div_iff₀ (pow_pos hH N)).mpr
  calc
    _ = ∫ t : ℝ in {t | H < |t|}, H ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t : ℝ in {t | H < |t|}, |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ :=
      setIntegral_mono_on (((W.cutoffFamily V hV R).vertical_norm_integrable σ).const_mul (H ^ N)).integrableOn
        (hb R hR σ hσ).1.integrableOn hm (fun t ht =>
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH.le ht.le N) (norm_nonneg _))
    _ ≤ ∫ t : ℝ, |t| ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ :=
      setIntegral_le_integral (hb R hR σ hσ).1 (ae_of_all _ fun t => by positivity)
    _ ≤ C := (hb R hR σ hσ).2


theorem cutoffFamily_uniform_contour_data (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ C ∧
      (∀ t : ℝ, (1 + |t|) ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ ≤ C) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|}, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ C / H ^ N := by
  obtain ⟨C₀, hC₀, h₀⟩ := W.cutoffFamily_uniform_weighted_moment V hV hone hzero lo hi 0
  obtain ⟨Cd, hCd, hd⟩ := W.cutoffFamily_uniform_strip_decay V hV hone hzero lo hi N
  obtain ⟨Ct, hCt, ht⟩ := W.cutoffFamily_uniform_tail V hV hone hzero lo hi N
  refine ⟨max C₀ (max Cd Ct), hC₀.trans (le_max_left _ _), ?_⟩
  intro R hR σ hσ
  refine ⟨?_, (fun t => (hd R hR σ hσ t).trans ((le_max_left Cd Ct).trans (le_max_right _ _))), ?_⟩
  · have hh : (∫ t : ℝ, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ C₀ := by
      simpa only [pow_zero, one_mul] using (h₀ R hR σ hσ).2
    exact hh.trans (le_max_left _ _)
  · intro H hH
    exact (ht R hR σ hσ H hH).trans (div_le_div_of_nonneg_right
      ((le_max_right Cd Ct).trans (le_max_right _ _)) (pow_nonneg hH.le N))

def cutoffContourConstant (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (N : ℕ) : ℝ :=
  Classical.choose (W.cutoffFamily_uniform_contour_data V hV hone hzero lo hi N)

theorem cutoffContourConstant_spec (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (N : ℕ) :
    0 ≤ W.cutoffContourConstant V hV hone hzero lo hi N ∧ ∀ R : ℝ, 0 ≤ R → ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤ W.cutoffContourConstant V hV hone hzero lo hi N ∧
      (∀ t : ℝ, (1 + |t|) ^ N * ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖ ≤ W.cutoffContourConstant V hV hone hzero lo hi N) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|}, ‖mellin (W.cutoffFamily V hV R).function (vertical σ t)‖) ≤
          W.cutoffContourConstant V hV hone hzero lo hi N / H ^ N :=
  Classical.choose_spec (W.cutoffFamily_uniform_contour_data V hV hone hzero lo hi N)


end AnnularProfile
/-- The same finite contour estimate with one constant shared by every scaled cutoff. -/
theorem annular_cutoff_polynomial_uniform_upper {ι : Type*} [Countable ι]
    (W : AnnularProfile)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (lo hi : ℝ) (order : ℕ)
    (R : ℝ) (hR : 0 ≤ R)
    (c : ι → ℂ) (norm : ι → ℝ) (hnorm : ∀ i, 0 < norm i)
    (L : ℂ → ℂ) (s : ℂ) {X a b H Mleft M : ℝ}
    (hX : 1 ≤ X) (hlo : lo ≤ a) (hab : a ≤ b) (hhi : b ≤ hi) (hH : 0 < H)
    (hMleft : 0 ≤ Mleft) (hM : 0 ≤ M)
    (hsum : Summable (fun i => ‖c i‖ * norm i ^ (-(s.re + b))))
    (hline : ∀ t, L (s + vertical b t) = dirichletSeries c norm (s + vertical b t))
    (hLdiff : DifferentiableOn ℂ (fun z => L (s + z)) (closedRectangle a b H))
    (hLrect : ∀ z ∈ closedRectangle a b H, ‖L (s + z)‖ ≤ M)
    (hLleft : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ Mleft)
    (S : Finset ι) (hS : ∀ i, norm i ≤ W.upper * X → i ∈ S) :
    let C := W.cutoffContourConstant V hV hone hzero lo hi order
    let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
    ‖∑ i ∈ S, smoothedTerm (W.cutoffFamily V hV R) c norm s X i‖ ≤ (1 / (2 * Real.pi)) *
      ((Mleft * X ^ a) * C +
        2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
          (A * X ^ b) * (C / H ^ order)) := by
  let C := W.cutoffContourConstant V hV hone hzero lo hi order
  let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
  have hc := W.cutoffContourConstant_spec V hV hone hzero lo hi order
  have hC : 0 ≤ C := hc.1
  have hA : 0 ≤ A := tsum_nonneg (fun i =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hnorm i).le _))
  have ha : a ∈ Icc lo hi := ⟨hlo, hab.trans hhi⟩
  have hb : b ∈ Icc lo hi := ⟨hlo.trans hab, hhi⟩
  have hpoint : ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖mellin (W.cutoffFamily V hV R).function (vertical x t)‖ ≤ C / (1 + |t|) ^ order := by
    intro x hx t
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + |t|) order)).mpr
    simpa only [mul_comm] using (hc.2 R hR x ⟨hlo.trans hx.1, hx.2.trans hhi⟩).2.1 t
  have hWbot : ∀ x ∈ Icc a b,
      ‖mellin (W.cutoffFamily V hV R).function (vertical x (-H))‖ ≤ C / (1 + H) ^ order := by
    intro x hx
    simpa only [abs_neg, abs_of_nonneg hH.le] using hpoint x hx (-H)
  have hWtop : ∀ x ∈ Icc a b,
      ‖mellin (W.cutoffFamily V hV R).function (vertical x H)‖ ≤ C / (1 + H) ^ order := by
    intro x hx
    simpa only [abs_of_nonneg hH.le] using hpoint x hx H
  have hraw := annular_polynomial_upper_from_dirichlet_rectangle (W.cutoffFamily V hV R) c norm hnorm L s
    hX hab hH.le hMleft hM (div_nonneg hC (by positivity)) hsum hline hLdiff hLrect hLleft
    hWbot hWtop S hS
  have hfirst := mul_le_mul_of_nonneg_left (hc.2 R hR a ha).1
    (mul_nonneg hMleft (Real.rpow_nonneg (zero_le_one.trans hX) a))
  have htail := mul_le_mul_of_nonneg_left ((hc.2 R hR b hb).2.2 H hH)
    (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hX) b))
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  change (Mleft * X ^ a) * (∫ t : ℝ, ‖mellin (W.cutoffFamily V hV R).function (vertical a t)‖) +
      2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
      (A * X ^ b) * (∫ t : ℝ in {t | H < |t|}, ‖mellin (W.cutoffFamily V hV R).function (vertical b t)‖) ≤ _
  linarith


end ExpansionInterfaces.Mellin

#print axioms ExpansionInterfaces.Mellin.AnnularProfile.cutoffFamily_uniform_strip_decay
#print axioms ExpansionInterfaces.Mellin.AnnularProfile.cutoffFamily_uniform_contour_data
#print axioms ExpansionInterfaces.Mellin.annular_cutoff_polynomial_uniform_upper
