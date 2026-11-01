import HeckeSkeleton.LowEnergy.EulerLog
import HeckeSkeleton.LowEnergy.GaussianReconstruction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The actual Gaussian annuli have summable Euler seminorms

The seminorm below has exactly the definition used by `GlobalThetaData`.
Its annular majorant is derived from the explicit cutoff and Gaussian
derivative bounds, with no annular seminorm assumption.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GaussianSeminorm

open HeckeGeneral.Analysis HeckeSkeleton.LowEnergy.Gaussian
open HeckeSkeleton.LowEnergy.EulerLog MeasureTheory Set
open scoped BigOperators ContDiff

def logAnnulus (k : ℤ) (u : ℝ) : ℂ :=
  logGaussianNormalization * (cutoffGaussianAnnulus fixedIntegerCutoff k u : ℂ)

def integralSeminorm (k : ℤ) (j : ℕ) (A : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ‖eulerOrder j (annulus k) y‖ *
    (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y

def seminorm (k : ℤ) (J : ℕ) (A : ℝ) : ℝ :=
  (Finset.range (J + 1)).sup' (by simp) (fun j => max 0 (integralSeminorm k j A))

theorem smooth_cutoffGaussianAnnulus (k : ℤ) :
    ContDiff ℝ ∞ (cutoffGaussianAnnulus fixedIntegerCutoff k) :=
  (contDiff_realLogGaussian.comp (contDiff_const.add contDiff_id)).mul
    contDiff_fixedIntegerCutoff

theorem smooth_logAnnulus (k : ℤ) : ContDiff ℝ ∞ (logAnnulus k) :=
  contDiff_const.mul ((Complex.ofRealCLM.contDiff (𝕜 := ℝ)).comp
    (smooth_cutoffGaussianAnnulus k))

theorem annulus_eq_logAnnulus (k : ℤ) {x : ℝ} (hx : 0 < x) :
    annulus k x = logAnnulus k (Real.log x) := by
  simp [annulus, logAnnulus, hx]

theorem iteratedDeriv_logAnnulus (k : ℤ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (logAnnulus k) u = logGaussianNormalization *
      ((iteratedDeriv j (cutoffGaussianAnnulus fixedIntegerCutoff k) u : ℝ) : ℂ) := by
  unfold logAnnulus
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_ofReal _ (smooth_cutoffGaussianAnnulus k)]

theorem logAnnulus_deriv_zero_outside (k : ℤ) (j : ℕ) {u : ℝ} (hu : 1 < |u|) :
    iteratedDeriv j (logAnnulus k) u = 0 := by
  rw [iteratedDeriv_logAnnulus]
  have hs : tsupport (cutoffGaussianAnnulus fixedIntegerCutoff k) ⊆ Icc (-1) 1 :=
    tsupport_mul_subset_right.trans tsupport_fixedIntegerCutoff
  rw [iteratedDeriv_cutoff_zero_outside hs j hu, Complex.ofReal_zero, mul_zero]

theorem integralSeminorm_log (k : ℤ) (j : ℕ) (A : ℝ) :
    integralSeminorm k j A = ∫ u : ℝ, ‖iteratedDeriv j (logAnnulus k) u‖ *
      (Real.exp (u / 4) + Real.exp (-A * u)) :=
  testIntegral_log _ _ (smooth_logAnnulus k)
    (fun y hy => annulus_eq_logAnnulus k hy) j A

theorem log_weight_le (A u : ℝ) (hu : |u| ≤ 1) :
    Real.exp (u / 4) + Real.exp (-A * u) ≤
      Real.exp (1 / 4 : ℝ) + Real.exp |A| := by
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    linarith [(le_abs_self u).trans hu]
  · apply Real.exp_le_exp.mpr
    calc
      -A * u ≤ |-A * u| := le_abs_self _
      _ = |A| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ = |A| := mul_one _

def seminormConstant (A : ℝ) : ℝ :=
  2 * (Real.exp (1 / 4 : ℝ) + Real.exp |A|) * ‖logGaussianNormalization‖

theorem seminormConstant_nonneg (A : ℝ) : 0 ≤ seminormConstant A := by
  unfold seminormConstant
  positivity

theorem integralSeminorm_nonneg (k : ℤ) (j : ℕ) (A : ℝ) :
    0 ≤ integralSeminorm k j A := by
  rw [integralSeminorm_log]
  exact integral_nonneg (fun _ => by positivity)

theorem integralSeminorm_le (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j u, |iteratedDeriv j fixedIntegerCutoff u| ≤ B j)
    (k : ℤ) (j : ℕ) (A : ℝ) :
    integralSeminorm k j A ≤ seminormConstant A * cutoffAnnulusMajorant B j 1 k := by
  rw [integralSeminorm_log]
  let f : ℝ → ℝ := fun u => ‖iteratedDeriv j (logAnnulus k) u‖ *
    (Real.exp (u / 4) + Real.exp (-A * u))
  have hzero (u : ℝ) (hu : u ∉ Icc (-1 : ℝ) 1) : f u = 0 := by
    have hu' : 1 < |u| := lt_of_not_ge (fun h => hu (abs_le.mp h))
    simp [f, logAnnulus_deriv_zero_outside k j hu']
  have heq : (∫ u : ℝ, f u) = ∫ u in Icc (-1 : ℝ) 1, f u :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  change (∫ u : ℝ, f u) ≤ _
  rw [heq]
  have hM : 0 ≤ cutoffAnnulusMajorant B j 1 k :=
    cutoffAnnulusMajorant_nonneg B hB j 1 zero_le_one k
  have hbnd (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      ‖f u‖ ≤ (‖logGaussianNormalization‖ * cutoffAnnulusMajorant B j 1 k) *
        (Real.exp (1 / 4 : ℝ) + Real.exp |A|) := by
    have hf0 : 0 ≤ f u := by dsimp [f]; positivity
    rw [Real.norm_of_nonneg hf0]
    apply mul_le_mul
    · rw [iteratedDeriv_logAnnulus, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact abs_cutoffGaussianAnnulus_deriv_le _ contDiff_fixedIntegerCutoff
        B hB hb j 1 zero_le_one tsupport_fixedIntegerCutoff k u
    · exact log_weight_le A u (abs_le.mpr hu)
    · positivity
    · positivity
  have hbnd' := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (-1 : ℝ) 1) < ⊤ by simp [Real.volume_Icc]) hbnd
  apply (le_abs_self _).trans
  apply hbnd'.trans_eq
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add]
  norm_num
  unfold seminormConstant
  ring

theorem seminorm_nonneg (k : ℤ) (J : ℕ) (A : ℝ) : 0 ≤ seminorm k J A := by
  unfold seminorm
  exact (le_max_left 0 (integralSeminorm k 0 A)).trans
    (Finset.le_sup' (fun j => max 0 (integralSeminorm k j A))
      (show 0 ∈ Finset.range (J + 1) by simp))

theorem seminorm_le (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j u, |iteratedDeriv j fixedIntegerCutoff u| ≤ B j)
    (k : ℤ) (J : ℕ) (A : ℝ) :
    seminorm k J A ≤ seminormConstant A *
      ∑ j ∈ Finset.range (J + 1), cutoffAnnulusMajorant B j 1 k := by
  unfold seminorm
  apply Finset.sup'_le
  intro j hj
  apply max_le
  · apply mul_nonneg (seminormConstant_nonneg _)
    exact Finset.sum_nonneg (fun j _ =>
      cutoffAnnulusMajorant_nonneg B hB j 1 zero_le_one k)
  · apply (integralSeminorm_le B hB hb k j A).trans
    apply mul_le_mul_of_nonneg_left _ (seminormConstant_nonneg _)
    exact Finset.single_le_sum (fun j _ =>
      cutoffAnnulusMajorant_nonneg B hB j 1 zero_le_one k) hj

/-- Every fixed exponential weight is allowed, with the constants chosen
before the annular index.  This is stronger than mere Gaussian truncation. -/
theorem summable_exp_mul_seminorm (J : ℕ) (A E : ℝ) :
    Summable (fun k : ℤ => Real.exp (E * |(k : ℝ)|) * seminorm k J A) := by
  obtain ⟨B, hB, hb⟩ := exists_compact_derivative_bounds
    contDiff_fixedIntegerCutoff hasCompactSupport_fixedIntegerCutoff
  have hs : Summable (fun k : ℤ => Real.exp (E * |(k : ℝ)|) *
      (seminormConstant A * ∑ j ∈ Finset.range (J + 1), cutoffAnnulusMajorant B j 1 k)) := by
    have h : Summable (fun k : ℤ => ∑ j ∈ Finset.range (J + 1),
        Real.exp (E * |(k : ℝ)|) * cutoffAnnulusMajorant B j 1 k) :=
      summable_sum (fun j _ => summable_cutoffAnnulusMajorant B j 1 E zero_le_one)
    convert h.mul_left (seminormConstant A) using 1
    funext k
    rw [← Finset.mul_sum]
    ring
  exact hs.of_nonneg_of_le (fun k => mul_nonneg (Real.exp_pos _).le
    (seminorm_nonneg k J A)) (fun k => mul_le_mul_of_nonneg_left
      (seminorm_le B hB hb k J A) (Real.exp_pos _).le)

/-- The tail is estimated at the level of its linear amplitude. -/
theorem exponential_tail_bound (J : ℕ) (A E T r : ℝ) (hr : 0 ≤ r) :
    (∑' k : ℤ, if T < |(k : ℝ)| then
      Real.exp (E * |(k : ℝ)|) * seminorm k J A else 0) ≤
    Real.exp (-r * T) *
      ∑' k : ℤ, Real.exp ((E + r) * |(k : ℝ)|) * seminorm k J A := by
  classical
  have hs := summable_exp_mul_seminorm J A E
  have htail : Summable (fun k : ℤ => if T < |(k : ℝ)| then
      Real.exp (E * |(k : ℝ)|) * seminorm k J A else 0) :=
    hs.of_nonneg_of_le
      (fun k => by split_ifs <;> positivity [seminorm_nonneg k J A])
      (fun k => by split_ifs <;> simp [mul_nonneg (Real.exp_pos _).le (seminorm_nonneg k J A)])
  have hb (k : ℤ) : (if T < |(k : ℝ)| then
      Real.exp (E * |(k : ℝ)|) * seminorm k J A else 0) ≤
      Real.exp (-r * T) *
        (Real.exp ((E + r) * |(k : ℝ)|) * seminorm k J A) := by
    split_ifs with hk
    · rw [← mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (seminorm_nonneg k J A)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hk.le)]
    · positivity [seminorm_nonneg k J A]
  have ht := htail.tsum_le_tsum hb
    ((summable_exp_mul_seminorm J A (E + r)).mul_left (Real.exp (-r * T)))
  simpa only [tsum_mul_left] using ht

/-- The prescribed polynomial loss is paid before the positive row bound.
The displayed constant is independent of the physical height Z. -/
theorem logarithmic_tail_bound (J : ℕ) (A E b M kap Z : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hkap : 0 < kap) (hZ : 0 < Z) :
    Z ^ b * (∑' k : ℤ, if kap * Real.log Z < |(k : ℝ)| then
      Real.exp (E * |(k : ℝ)|) * seminorm k J A else 0) ≤
    (∑' k : ℤ, Real.exp ((E + (b + M) / kap) * |(k : ℝ)|) * seminorm k J A) *
      Z ^ (-M) := by
  let r := (b + M) / kap
  have hr : 0 ≤ r := div_nonneg (add_nonneg hb hM) hkap.le
  have he : Z ^ b * Real.exp (-r * (kap * Real.log Z)) = Z ^ (-M) := by
    rw [Real.rpow_def_of_pos hZ, Real.rpow_def_of_pos hZ, ← Real.exp_add]
    congr 1
    dsimp [r]
    field_simp
    ring
  have ht := mul_le_mul_of_nonneg_left
    (exponential_tail_bound J A E (kap * Real.log Z) r hr) (Real.rpow_pos_of_pos hZ b).le
  apply ht.trans_eq
  rw [← mul_assoc, he, mul_comm]

#print axioms integralSeminorm_le
#print axioms summable_exp_mul_seminorm
#print axioms logarithmic_tail_bound

end HeckeSkeleton.LowEnergy.GaussianSeminorm
