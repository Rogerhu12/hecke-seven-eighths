module

public import HeckeSkeleton.Moments.MOM_INV_STEP.MellinWeightedTests

/-!
# Mellin separation by genuine Fourier inversion

The logarithmic lift is the actual function s ↦ W(exp s).  A fixed
continuous linear extension on Schwartz space supplies uniform bounds
on its Fourier density.  The finite Hecke background is untouched.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation

open MeasureTheory
open MellinSchwartz MellinWeightedTests CommonKernel
open scoped Classical ContDiff BigOperators FourierTransform

def liftBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def expBump : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def expCorrection (s : ℝ) : ℝ := expBump s * (Real.exp s - s)

theorem expCorrection_contDiff : ContDiff ℝ ∞ expCorrection := by
  unfold expCorrection
  exact expBump.contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem expCorrection_compact : HasCompactSupport expCorrection :=
  expBump.hasCompactSupport.mul_right

def expCorrectionSchwartz : SchwartzMap ℝ ℝ :=
  expCorrection_compact.toSchwartzMap expCorrection_contDiff

@[simp] theorem expCorrectionSchwartz_apply (s : ℝ) :
    expCorrectionSchwartz s = expCorrection s := rfl

def expExtension (s : ℝ) : ℝ := s + expCorrection s

theorem expExtension_temperate : Function.HasTemperateGrowth expExtension := by
  have h : Function.HasTemperateGrowth expCorrection := expCorrectionSchwartz.hasTemperateGrowth
  unfold expExtension
  fun_prop

theorem expExtension_proper :
    ∃ k : ℕ, ∃ C : ℝ, ∀ s : ℝ, ‖s‖ ≤ C * (1 + ‖expExtension s‖) ^ k := by
  let C := SchwartzMap.seminorm ℝ 0 0 expCorrectionSchwartz
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb (s : ℝ) : ‖expCorrection s‖ ≤ C := by
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, expCorrectionSchwartz_apply] using
      SchwartzMap.le_seminorm ℝ 0 0 expCorrectionSchwartz s
  refine ⟨1, C + 1, fun s => ?_⟩
  have hs : s = expExtension s - expCorrection s := by
    unfold expExtension
    ring
  calc
    ‖s‖ = ‖expExtension s - expCorrection s‖ := congrArg norm hs
    _ ≤ ‖expExtension s‖ + ‖expCorrection s‖ := norm_sub_le _ _
    _ ≤ ‖expExtension s‖ + C := add_le_add_right (hb s) _
    _ ≤ (C + 1) * (1 + ‖expExtension s‖) ^ 1 := by
      rw [pow_one]
      nlinarith [norm_nonneg (expExtension s), mul_nonneg hC (norm_nonneg (expExtension s))]

theorem expExtension_eq_exp {s : ℝ} (hs : |s| ≤ 2) :
    expExtension s = Real.exp s := by
  have hm : s ∈ Metric.closedBall (0 : ℝ) expBump.rIn := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, expBump] using hs
  unfold expExtension expCorrection
  rw [expBump.one_of_mem_closedBall hm]
  ring

theorem liftBump_temperate : Function.HasTemperateGrowth (fun s : ℝ => liftBump s) :=
  liftBump.hasCompactSupport.hasTemperateGrowth liftBump.contDiff

/-- The extension is fixed before W and supplies the seminorm bounds. -/
def logLiftCLM : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => liftBump s)).comp
    (SchwartzMap.compCLM ℝ expExtension_temperate expExtension_proper)

theorem logLiftCLM_apply (W : SchwartzMap ℝ ℂ) (s : ℝ) :
    logLiftCLM W s = (liftBump s : ℂ) * W (Real.exp s) := by
  change (SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => liftBump s)
    (SchwartzMap.compCLM ℝ expExtension_temperate expExtension_proper W)) s = _
  rw [SchwartzMap.smulLeftCLM_apply_apply liftBump_temperate,
    SchwartzMap.compCLM_apply]
  change (liftBump s : ℂ) * W (expExtension s) = _
  by_cases hs : liftBump s = 0
  · rw [hs, Complex.ofReal_zero, zero_mul, zero_mul]
  · have ht : s ∈ tsupport liftBump := subset_closure (Function.mem_support.mpr hs)
    rw [liftBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    rw [expExtension_eq_exp ht]

def logLiftFunction (W : SchwartzMap ℝ ℂ) (s : ℝ) : ℂ := W (Real.exp s)

theorem live_log_bounds (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) {s : ℝ} (hs : W (Real.exp s) ≠ 0) :
    0 ≤ s ∧ s ≤ Real.log 2 := by
  have hb := hW (subset_closure (Function.mem_support.mpr hs))
  constructor
  · simpa only [Real.log_one, Real.log_exp] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 1) hb.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos s) hb.2

theorem logLiftCLM_eq (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (s : ℝ) :
    logLiftCLM W s = logLiftFunction W s := by
  rw [logLiftCLM_apply]
  change (liftBump s : ℂ) * W (Real.exp s) = W (Real.exp s)
  by_cases hs : W (Real.exp s) = 0
  · rw [hs, mul_zero]
  · obtain ⟨hl, hu⟩ := live_log_bounds W hW hs
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hm : s ∈ Metric.closedBall (0 : ℝ) liftBump.rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hl]
      exact hu.trans hlog
    rw [liftBump.one_of_mem_closedBall hm, Complex.ofReal_one, one_mul]

def logLift (W : SchwartzMap ℝ ℂ)
    (_hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : SchwartzMap ℝ ℂ := logLiftCLM W

@[simp] theorem logLift_apply (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (s : ℝ) :
    logLift W hW s = W (Real.exp s) := logLiftCLM_eq W hW s

theorem logLift_support (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    tsupport (logLift W hW) ⊆ Set.Icc (0 : ℝ) (Real.log 2) := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  exact live_log_bounds W hW (by simpa only [Function.mem_support, logLift_apply] using hs)

def density (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : SchwartzMap ℝ ℂ :=
  𝓕 (logLift W hW)

theorem weighted_fourier_bound (q : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SchwartzMap ℝ ℂ, ∀ hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2, ∀ t : ℝ,
        (1 + |t|) ^ q * ‖density W hW t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let T : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
    (SchwartzMap.fourierTransformCLM ℝ).comp logLiftCLM
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    ((Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have hc : Continuous (fun F : SchwartzMap ℝ ℂ =>
      (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) F) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  have hp : Continuous p := hc.comp T.continuous
  obtain ⟨s, C, _hC, hb⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) p hp
  refine ⟨s, (2 : ℝ) ^ q * (C : ℝ), by positivity, fun W hW t => ?_⟩
  have hF := Seminorm.le_def.mp hb W
  change (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (density W hW) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W at hF
  have hpoint := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (q, 0)) (k := q) (n := 0) le_rfl le_rfl (density W hW) t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hF (by positivity)).trans_eq (by ring))

theorem moment_integrable (F : SchwartzMap ℝ ℂ) (m : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ m * ‖F t‖) := by
  have hi : Integrable (fun t : ℝ =>
      (2 : ℝ) ^ (m - 1) * (‖F t‖ + ‖t‖ ^ m * ‖F t‖)) :=
    (F.integrable.norm.add (F.integrable_pow_mul volume m)).const_mul _
  apply hi.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (by positivity)]
    have hp := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg t) m
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg (F t))).trans_eq (by
      simp only [one_pow, Real.norm_eq_abs]
      ring)

theorem density_moment_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (m : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ m * ‖density W hW t‖) :=
  moment_integrable (density W hW) m

/-- Every weighted L¹ moment has a uniform finite original-test
seminorm bound.  No frequency or outer arithmetic parameter occurs in
the chosen seminorm family. -/
theorem density_moment_bound (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SchwartzMap ℝ ℂ, ∀ hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2,
        (∫ t : ℝ, (1 + |t|) ^ m * ‖density W hW t‖) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let p := (volume : Measure ℝ).integrablePower
  let E : ℝ → ℝ := fun t => (1 + ‖t‖) ^ (-(p : ℝ))
  have hE : Integrable E := Measure.integrable_pow_neg_integrablePower (volume : Measure ℝ)
  have hE0 : ∀ t, 0 ≤ E t := fun t => Real.rpow_nonneg (by positivity) _
  obtain ⟨s, C, hC, hb⟩ := weighted_fourier_bound (m + p)
  refine ⟨s, C * ∫ t, E t, mul_nonneg hC (integral_nonneg hE0), fun W hW => ?_⟩
  have hp (t : ℝ) : (1 + |t|) ^ m * ‖density W hW t‖ ≤
      (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * E t := by
    have hd : (1 + |t|) ^ m * ‖density W hW t‖ ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + |t|) ^ p := by
      apply (le_div_iff₀ (by positivity)).mpr
      convert hb W hW t using 1 <;> rw [pow_add] <;> ring
    dsimp only [E]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖t‖), Real.rpow_natCast,
      Real.norm_eq_abs]
    simpa only [div_eq_mul_inv] using hd
  calc
    _ ≤ ∫ t : ℝ, (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * E t :=
      integral_mono (density_moment_integrable W hW m) (hE.const_mul _) hp
    _ = _ := by rw [integral_const_mul]; ring

theorem integrable_inverse (F : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t : ℝ => (𝓕 F) t * columnPhase t x) := by
  have hd : Integrable (fun t : ℝ => ‖(𝓕 F) t‖) :=
    ((𝓕 F).integrable (μ := (volume : Measure ℝ))).norm
  apply hd.mono'
    (((𝓕 F).continuous.mul (continuous_columnPhase x)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [norm_mul, norm_columnPhase, mul_one]
    exact le_rfl

theorem fourier_inverse (F : SchwartzMap ℝ ℂ) (x : ℝ) :
    F x = ∫ t : ℝ, (𝓕 F) t * columnPhase t x := by
  have hi := congrArg (fun f : SchwartzMap ℝ ℂ => f x)
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) F)
  symm
  calc
    _ = ∫ t : ℝ, Complex.exp ((2 * Real.pi * inner ℝ t x : ℝ) * Complex.I) * (𝓕 F) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [columnPhase, Real.fourierChar_apply]
        ring
    _ = (𝓕⁻ (𝓕 F) : SchwartzMap ℝ ℂ) x := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      simp only [smul_eq_mul]
    _ = F x := hi

theorem mellin_inverse (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (x : ℝ) (hx : 0 < x) :
    W x = ∫ t : ℝ, density W hW t * columnPhase t (Real.log x) := by
  simpa only [logLift_apply, Real.exp_log hx, density] using
    fourier_inverse (logLift W hW) (Real.log x)

theorem source_inverse (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (v u X : ℝ) (hv : 0 < v) (hu : 0 < u) (hX : 0 < X) :
    W (v * u / X) = ∫ t : ℝ, density W hW t *
      columnPhase t (Real.log v) * columnPhase t (Real.log u) *
        columnPhase t (-Real.log X) := by
  rw [mellin_inverse W hW _ (div_pos (mul_pos hv hu) hX)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [Real.log_div (mul_ne_zero hv.ne' hu.ne') hX.ne',
      Real.log_mul hv.ne' hu.ne', sub_eq_add_neg, columnPhase_add, columnPhase_add]
    ring

theorem integrable_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (v u X : ℝ) :
    Integrable (fun t : ℝ => density W hW t * columnPhase t (Real.log v) *
      columnPhase t (Real.log u) * columnPhase t (-Real.log X)) := by
  apply (density W hW).integrable.norm.mono' (by
    exact (((density W hW).continuous.mul (continuous_columnPhase _)).mul
      (continuous_columnPhase _)).mul (continuous_columnPhase _) |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => by
    simp only [norm_mul, norm_columnPhase, mul_one]
    exact le_rfl

theorem separated_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (a τ v u X U : ℝ)
    (hv : 0 < v) (hu : 0 < u) (hX : 0 < X) (hU : 0 < U)
    (hlo : 1 ≤ u / U) (hhi : u / U ≤ 2) :
    W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
          weightedTest a (t + τ) (u / U)) := by
  rw [source_inverse W hW v u X hv hu hX, ← integral_mul_const, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    have hs := scaled_weighted_phase a (t + τ) u U hu hU hlo hhi
    rw [← hs, ← columnPhase_frequency_add]
    ring

end HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation

end
