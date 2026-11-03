module

public import HeckeSkeleton.Moments.MOM_INV_STEP.WideMellinTests

/-! Mellin inversion on a fixed positive compact interval. -/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PositiveIntervalMellin

open MeasureTheory CommonKernel MellinWeightedTests
open scoped Classical ContDiff BigOperators FourierTransform

def liftWidth (lo hi : ℝ) : ℝ := |Real.log lo| + |Real.log hi| + 1

theorem liftWidth_pos (lo hi : ℝ) : 0 < liftWidth lo hi := by
  unfold liftWidth
  positivity

def liftBump (lo hi : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := liftWidth lo hi
  rOut := liftWidth lo hi + 1
  rIn_pos := liftWidth_pos lo hi
  rIn_lt_rOut := by linarith

def expBump (lo hi : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := liftWidth lo hi + 1
  rOut := liftWidth lo hi + 2
  rIn_pos := by linarith [liftWidth_pos lo hi]
  rIn_lt_rOut := by linarith

def expCorrection (lo hi s : ℝ) : ℝ := expBump lo hi s * (Real.exp s - s)

theorem expCorrection_contDiff (lo hi : ℝ) : ContDiff ℝ ∞ (expCorrection lo hi) :=
  (expBump lo hi).contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem expCorrection_compact (lo hi : ℝ) : HasCompactSupport (expCorrection lo hi) :=
  (expBump lo hi).hasCompactSupport.mul_right

def expCorrectionSchwartz (lo hi : ℝ) : SchwartzMap ℝ ℝ :=
  (expCorrection_compact lo hi).toSchwartzMap (expCorrection_contDiff lo hi)

@[simp] theorem expCorrectionSchwartz_apply (lo hi s : ℝ) :
    expCorrectionSchwartz lo hi s = expCorrection lo hi s := rfl

def expExtension (lo hi s : ℝ) : ℝ := s + expCorrection lo hi s

theorem expExtension_temperate (lo hi : ℝ) :
    Function.HasTemperateGrowth (expExtension lo hi) := by
  have h : Function.HasTemperateGrowth (expCorrection lo hi) :=
    (expCorrectionSchwartz lo hi).hasTemperateGrowth
  unfold expExtension
  fun_prop

theorem expExtension_proper (lo hi : ℝ) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ s : ℝ, ‖s‖ ≤ C * (1 + ‖expExtension lo hi s‖) ^ k := by
  let C := SchwartzMap.seminorm ℝ 0 0 (expCorrectionSchwartz lo hi)
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb (s : ℝ) : ‖expCorrection lo hi s‖ ≤ C :=
    SchwartzMap.norm_le_seminorm ℝ (expCorrectionSchwartz lo hi) s
  refine ⟨1, C + 1, fun s => ?_⟩
  have hs : s = expExtension lo hi s - expCorrection lo hi s := by
    unfold expExtension
    ring
  calc
    ‖s‖ = ‖expExtension lo hi s - expCorrection lo hi s‖ := congrArg norm hs
    _ ≤ ‖expExtension lo hi s‖ + ‖expCorrection lo hi s‖ := norm_sub_le _ _
    _ ≤ ‖expExtension lo hi s‖ + C := add_le_add_right (hb s) _
    _ ≤ (C + 1) * (1 + ‖expExtension lo hi s‖) ^ 1 := by
      rw [pow_one]
      nlinarith [norm_nonneg (expExtension lo hi s),
        mul_nonneg hC (norm_nonneg (expExtension lo hi s))]

theorem expExtension_eq_exp (lo hi : ℝ) {s : ℝ}
    (hs : |s| ≤ liftWidth lo hi + 1) : expExtension lo hi s = Real.exp s := by
  have hm : s ∈ Metric.closedBall (0 : ℝ) (expBump lo hi).rIn := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, expBump] using hs
  unfold expExtension expCorrection
  rw [(expBump lo hi).one_of_mem_closedBall hm]
  ring

theorem liftBump_temperate (lo hi : ℝ) :
    Function.HasTemperateGrowth (fun s : ℝ => liftBump lo hi s) :=
  (liftBump lo hi).hasCompactSupport.hasTemperateGrowth (liftBump lo hi).contDiff

def logLiftCLM (lo hi : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => liftBump lo hi s)).comp
    (SchwartzMap.compCLM ℝ (expExtension_temperate lo hi) (expExtension_proper lo hi))

theorem logLiftCLM_apply (lo hi : ℝ) (W : SchwartzMap ℝ ℂ) (s : ℝ) :
    logLiftCLM lo hi W s = (liftBump lo hi s : ℂ) * W (Real.exp s) := by
  change (SchwartzMap.smulLeftCLM ℂ (fun s : ℝ => liftBump lo hi s)
    (SchwartzMap.compCLM ℝ (expExtension_temperate lo hi)
      (expExtension_proper lo hi) W)) s = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (liftBump_temperate lo hi),
    SchwartzMap.compCLM_apply]
  change (liftBump lo hi s : ℂ) * W (expExtension lo hi s) = _
  by_cases hs : liftBump lo hi s = 0
  · rw [hs, Complex.ofReal_zero, zero_mul, zero_mul]
  · have ht : s ∈ tsupport (liftBump lo hi) := subset_closure (Function.mem_support.mpr hs)
    rw [(liftBump lo hi).tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    rw [expExtension_eq_exp lo hi ht]

theorem live_log_bounds (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi)
    {s : ℝ} (hs : W (Real.exp s) ≠ 0) :
    Real.log lo ≤ s ∧ s ≤ Real.log hi := by
  have hb := hW (subset_closure (Function.mem_support.mpr hs))
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log hlo hb.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos s) hb.2

theorem logLiftCLM_eq (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) (s : ℝ) :
    logLiftCLM lo hi W s = W (Real.exp s) := by
  rw [logLiftCLM_apply]
  by_cases hs : W (Real.exp s) = 0
  · rw [hs, mul_zero]
  · obtain ⟨hl, hu⟩ := live_log_bounds lo hi hlo hhi W hW hs
    have hm : s ∈ Metric.closedBall (0 : ℝ) (liftBump lo hi).rIn := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      change |s| ≤ |Real.log lo| + |Real.log hi| + 1
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (Real.log lo), abs_nonneg (Real.log hi)]
      · linarith [le_abs_self (Real.log hi), abs_nonneg (Real.log lo)]
    rw [(liftBump lo hi).one_of_mem_closedBall hm, Complex.ofReal_one, one_mul]

def logLift (lo hi : ℝ) (_hlo : 0 < lo) (_hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (_hW : tsupport W ⊆ Set.Icc lo hi) : SchwartzMap ℝ ℂ :=
  logLiftCLM lo hi W

@[simp] theorem logLift_apply (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) (s : ℝ) :
    logLift lo hi hlo hhi W hW s = W (Real.exp s) :=
  logLiftCLM_eq lo hi hlo hhi W hW s

theorem logLift_support (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) :
    tsupport (logLift lo hi hlo hhi W hW) ⊆ Set.Icc (Real.log lo) (Real.log hi) := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  exact live_log_bounds lo hi hlo hhi W hW
    (by simpa only [Function.mem_support, logLift_apply] using hs)

def density (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) : SchwartzMap ℝ ℂ :=
  𝓕 (logLift lo hi hlo hhi W hW)

theorem weighted_fourier_bound (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (q : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SchwartzMap ℝ ℂ, ∀ hW : tsupport W ⊆ Set.Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ q * ‖density lo hi hlo hhi W hW t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let T : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
    (SchwartzMap.fourierTransformCLM ℝ).comp (logLiftCLM lo hi)
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    ((Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have hc : Continuous (fun F : SchwartzMap ℝ ℂ =>
      (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) F) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s, C, _hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hc.comp T.continuous)
  refine ⟨s, (2 : ℝ) ^ q * (C : ℝ), by positivity, fun W hW t => ?_⟩
  have hF := Seminorm.le_def.mp hb W
  change (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (density lo hi hlo hhi W hW) ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W at hF
  have hpoint := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (q, 0)) (k := q) (n := 0) le_rfl le_rfl
    (density lo hi hlo hhi W hW) t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hF (by positivity)).trans_eq (by ring))

theorem density_moment_integrable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) (m : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ m * ‖density lo hi hlo hhi W hW t‖) :=
  MellinSeparation.moment_integrable _ m

theorem density_moment_bound (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SchwartzMap ℝ ℂ, ∀ hW : tsupport W ⊆ Set.Icc lo hi,
        (∫ t : ℝ, (1 + |t|) ^ m * ‖density lo hi hlo hhi W hW t‖) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let p := (volume : Measure ℝ).integrablePower
  let E : ℝ → ℝ := fun t => (1 + ‖t‖) ^ (-(p : ℝ))
  have hE : Integrable E := Measure.integrable_pow_neg_integrablePower (volume : Measure ℝ)
  have hE0 : ∀ t, 0 ≤ E t := fun t => Real.rpow_nonneg (by positivity) _
  obtain ⟨s, C, hC, hb⟩ := weighted_fourier_bound lo hi hlo hhi (m + p)
  refine ⟨s, C * ∫ t, E t, mul_nonneg hC (integral_nonneg hE0), fun W hW => ?_⟩
  have hp (t : ℝ) : (1 + |t|) ^ m * ‖density lo hi hlo hhi W hW t‖ ≤
      (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * E t := by
    have hd : (1 + |t|) ^ m * ‖density lo hi hlo hhi W hW t‖ ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + |t|) ^ p := by
      apply (le_div_iff₀ (by positivity)).mpr
      convert hb W hW t using 1 <;> rw [pow_add] <;> ring
    dsimp only [E]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖t‖), Real.rpow_natCast,
      Real.norm_eq_abs]
    simpa only [div_eq_mul_inv] using hd
  calc
    _ ≤ ∫ t : ℝ, (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * E t :=
      integral_mono (density_moment_integrable lo hi hlo hhi W hW m) (hE.const_mul _) hp
    _ = _ := by rw [integral_const_mul]; ring

theorem mellin_inverse (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi) (x : ℝ) (hx : 0 < x) :
    W x = ∫ t : ℝ, density lo hi hlo hhi W hW t * columnPhase t (Real.log x) := by
  simpa only [logLift_apply, Real.exp_log hx, density] using
    MellinSeparation.fourier_inverse (logLift lo hi hlo hhi W hW) (Real.log x)

theorem source_inverse (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi)
    (v u X : ℝ) (hv : 0 < v) (hu : 0 < u) (hX : 0 < X) :
    W (v * u / X) = ∫ t : ℝ, density lo hi hlo hhi W hW t *
      columnPhase t (Real.log v) * columnPhase t (Real.log u) *
        columnPhase t (-Real.log X) := by
  rw [mellin_inverse lo hi hlo hhi W hW _ (div_pos (mul_pos hv hu) hX)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [Real.log_div (mul_ne_zero hv.ne' hu.ne') hX.ne',
      Real.log_mul hv.ne' hu.ne', sub_eq_add_neg, columnPhase_add, columnPhase_add]
    ring

/-- Complete residual pools are permitted: off the original test support
the added terms cancel in this actual Mellin integral. -/
theorem wide_separated_source (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc lo hi)
    (a τ v u X U : ℝ) (hv : 0 < v) (hu : 0 < u) (hX : 0 < X) (hU : 0 < U)
    (hcut : W (v * u / X) ≠ 0 → WideMellinTests.cutoff (u / U) = 1) :
    W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u) =
      ∫ t : ℝ, density lo hi hlo hhi W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
          WideMellinTests.weightedTest a (t + τ) (u / U)) := by
  have he : (∫ t : ℝ, density lo hi hlo hhi W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U) *
          WideMellinTests.weightedTest a (t + τ) (u / U))) =
      WideMellinTests.cutoff (u / U) *
        (W (v * u / X) * ((u ^ a : ℝ) : ℂ) * columnPhase τ (Real.log u)) := by
    rw [source_inverse lo hi hlo hhi W hW v u X hv hu hX,
      ← integral_mul_const, ← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [WideMellinTests.scaled_weighted_phase_all _ _ _ _ hu hU,
        ← columnPhase_frequency_add]
      ring
  rw [he]
  by_cases hw : W (v * u / X) = 0
  · simp only [hw, zero_mul, mul_zero]
  · rw [hcut hw, one_mul]

theorem wide_window_of_dyadic_outer (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (g v V X u : ℝ) (hg : 0 < g) (hv : 0 < v) (hV : 0 < V)
    (hX : 0 < X) (hu : 0 < u) (hvlo : V ≤ v) (hvhi : v ≤ 2 * V)
    (hw : W (g * v * u / X) ≠ 0) :
    1 / 4 ≤ u / (X / (g * V)) ∧ u / (X / (g * V)) ≤ 5 / 2 := by
  have hb := hW (subset_closure (Function.mem_support.mpr hw))
  let z := g * u / X
  have hz : 0 ≤ z := (div_pos (mul_pos hg hu) hX).le
  have he : g * v * u / X = z * v := by dsimp only [z]; ring
  have he' : u / (X / (g * V)) = z * V := by
    dsimp only [z]
    field_simp
    <;> ring
  rw [he] at hb
  rw [he']
  have hl := mul_le_mul_of_nonneg_left hvlo hz
  have hh := mul_le_mul_of_nonneg_left hvhi hz
  constructor <;> nlinarith [hb.1, hb.2]

theorem wide_cutoff_of_dyadic_outer (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2))
    (g v V X u : ℝ) (hg : 0 < g) (hv : 0 < v) (hV : 0 < V)
    (hX : 0 < X) (hu : 0 < u) (hvlo : V ≤ v) (hvhi : v ≤ 2 * V)
    (hw : W (g * v * u / X) ≠ 0) :
    WideMellinTests.cutoff (u / (X / (g * V))) = 1 := by
  obtain ⟨hl, hh⟩ := wide_window_of_dyadic_outer W hW g v V X u hg hv hV hX hu hvlo hvhi hw
  exact WideMellinTests.cutoff_one hl hh

end HeckeSkeleton.Moments.MOM_INV_STEP.PositiveIntervalMellin

end

