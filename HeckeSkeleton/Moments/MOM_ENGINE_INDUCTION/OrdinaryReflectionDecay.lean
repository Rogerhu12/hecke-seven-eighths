import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryGamma

/-!
# Arbitrary power decay of the actual ordinary reflected profile

The reflected norm profile is shifted along its actual holomorphic
Gamma/Mellin integrand.  Its arbitrary power tail is controlled by a
finite Euler seminorm of the original test.  The derivative order and
constant are chosen before the moving test and its positive argument.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

private def ordinaryMellinMultiplier (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (s : ℂ) : ℂ := mellin V.toFun s * ordinaryGammaRatio K χ s

private theorem ordinaryMultiplier_strip_seminorm_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (A : ℝ) (hA : 0 ≤ A) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest),
      ∀ σ ∈ Icc (-A) 0, ∀ t : ℝ,
      ‖ordinaryMellinMultiplier K χ V (idealVerticalPoint σ t)‖ ≤
        C * testSeminorm V.toFun J A * (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨G, hG, hGb⟩ := ordinaryGammaRatio_strip_bound K hcomplex χ A hA
  let k : ℕ := (2 * Nat.ceil A + 2) * Fintype.card (InfinitePlace K)
  let J : ℕ := k + 2
  refine ⟨J, 4 * 2 ^ J * G, by positivity, ?_⟩
  intro V σ hσ t
  let S : ℝ := testSeminorm V.toFun J A
  let T : ℝ := 1 + |t|
  have hT : 0 < T := by dsimp [T]; positivity
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hi (j : ℕ) (hj : j ≤ J) : Iint V j (-σ) ≤ 2 * S := by
    have h := Iint_strip_le V j (σ1 := -1 / 4) (σ2 := A)
      (by linarith [hσ.2]) (by linarith [hσ.1])
    have hl := Iint_left_le V j J hj A
    have hr := Iint_right_le V j J hj A
    linarith
  have hMB : 2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ)) ≤ (4 * 2 ^ J) * S := by
    calc
      _ ≤ 2 ^ J * (2 * S + 2 * S) :=
        mul_le_mul_of_nonneg_left (add_le_add (hi 0 (Nat.zero_le _)) (hi J le_rfl))
          (by positivity)
      _ = _ := by ring
  have hM : ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      ((4 * 2 ^ J) * S) * T ^ (-(J : ℝ)) :=
    (smoothAnnular_mellin_vertical_decay V J σ t).trans
      (mul_le_mul_of_nonneg_right hMB (Real.rpow_nonneg hT.le _))
  have hgamma : ‖ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ ≤ G * T ^ k := by
    simpa only [idealVerticalPoint_re, idealVerticalPoint_im, T, k] using
      hGb (idealVerticalPoint σ t) (by simpa only [idealVerticalPoint_re] using hσ.1)
        (by simpa only [idealVerticalPoint_re] using hσ.2)
  have he : T ^ (-(J : ℝ)) * T ^ k = T ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hT]
    congr 1
    dsimp [J]
    push_cast
    ring
  calc
    ‖ordinaryMellinMultiplier K χ V (idealVerticalPoint σ t)‖ =
        ‖mellin V.toFun (idealVerticalPoint σ t)‖ *
          ‖ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ := norm_mul _ _
    _ ≤ (((4 * 2 ^ J) * S) * T ^ (-(J : ℝ))) * (G * T ^ k) :=
      mul_le_mul hM hgamma (norm_nonneg _) (by positivity)
    _ = (4 * 2 ^ J * G) * S * (1 + |t|) ^ (-(2 : ℝ)) := by
      calc
        _ = (4 * 2 ^ J * G) * S * (T ^ (-(J : ℝ)) * T ^ k) := by ring
        _ = _ := by rw [he]

private theorem differentiableAt_ordinaryMellinMultiplier
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (ordinaryMellinMultiplier K χ V) s := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  exact (hM s).mul (differentiableAt_ordinaryGammaRatio K χ hs)

private theorem integrable_ordinaryMellinMultiplier
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {A σ : ℝ}
    (hA : 0 ≤ A) (hσ : σ ∈ Icc (-A) 0) :
    Integrable (fun t : ℝ => ordinaryMellinMultiplier K χ V (idealVerticalPoint σ t)) := by
  obtain ⟨J, C, _, hC⟩ := ordinaryMultiplier_strip_seminorm_bound K hcomplex χ A hA
  have hc : Continuous (fun t : ℝ => ordinaryMellinMultiplier K χ V (idealVerticalPoint σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_ordinaryMellinMultiplier K χ V (by
      simp only [idealVerticalPoint_re]; linarith [hσ.2])).continuousAt.comp
        (continuous_idealVerticalPoint σ).continuousAt
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul
    (C * testSeminorm V.toFun J A)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (hC V σ hσ)

private def ordinaryProfileIntegrand (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (y : ℝ) (s : ℂ) : ℂ := ordinaryMellinMultiplier K χ V s * (y : ℂ) ^ (s - 1)

private theorem differentiableAt_ordinaryProfileIntegrand
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (ordinaryProfileIntegrand K χ V y) s := by
  exact (differentiableAt_ordinaryMellinMultiplier K χ V hs).mul
    ((differentiableAt_id.sub_const (1 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))

/-- The reciprocal sign and Jacobian of the real height substitution
identify the defined profile with its actual negative-line contour. -/
theorem ordinaryReflectedProfile_eq_negative_line
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) (δ y : ℝ) :
    ordinaryReflectedProfile K χ V δ y = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t : ℝ, (mellin V.toFun (idealVerticalPoint (-δ) t) *
        ordinaryGammaRatio K χ (idealVerticalPoint (-δ) t)) *
          (y : ℂ) ^ (idealVerticalPoint (-δ) t - 1) := by
  unfold ordinaryReflectedProfile
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, (y : ℂ) ^ (-idealVerticalPoint (1 + δ) (-t)) *
          ordinaryReflectionKernel K χ V δ (-t) := by
      congr 1
      exact (integral_neg_eq_self _ volume).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hs : 1 - idealVerticalPoint (1 + δ) (-t) = idealVerticalPoint (-δ) t := by
        unfold idealVerticalPoint
        push_cast
        ring
      have he : -idealVerticalPoint (1 + δ) (-t) = idealVerticalPoint (-δ) t - 1 := by
        unfold idealVerticalPoint
        push_cast
        ring
      dsimp only [ordinaryReflectionKernel]
      rw [hs, he]
      unfold ordinaryGammaRatio
      ring

/-- The positive dual frequency line may be moved arbitrarily far right;
the original annular test and actual character are unchanged. -/
theorem ordinaryReflectedProfile_line_independent
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ A y : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hy : 0 < y) :
    ordinaryReflectedProfile K χ V δ y = ordinaryReflectedProfile K χ V A y := by
  have hA : 0 ≤ A := hδ.le.trans hδA
  obtain ⟨J, C, hC0, hC⟩ := ordinaryMultiplier_strip_seminorm_bound K hcomplex χ A hA
  let R : ℝ := y ^ (-A - 1) + y ^ (-1 : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ testSeminorm V.toFun J A :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hbound : ∀ σ ∈ Icc (-A) (-δ), ∀ t : ℝ,
      ‖ordinaryProfileIntegrand K χ V y (idealVerticalPoint σ t)‖ ≤
        (C * testSeminorm V.toFun J A * R) * (1 + |t|) ^ (-(2 : ℝ)) := by
    intro σ hσ t
    have hm := hC V σ ⟨hσ.1, hσ.2.trans (by linarith)⟩ t
    have hp : y ^ (σ - 1) ≤ R := by
      rcases le_or_gt 1 y with h | h
      · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith [hσ.2])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hy.le _))
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h.le (by linarith [hσ.1])).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
    rw [ordinaryProfileIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
    exact (mul_le_mul hm hp (Real.rpow_nonneg hy.le _) (by positivity)).trans_eq (by ring)
  have hshift := verticalIntegral_eq_of_poly_strip
    (f := ordinaryProfileIntegrand K χ V y) (a := -A) (b := -δ)
    (C := C * testSeminorm V.toFun J A * R) (e := 2)
    (by linarith) (by norm_num)
    (fun z _ hz => differentiableAt_ordinaryProfileIntegrand K χ V hy (by linarith)) hbound
  rw [ordinaryReflectedProfile_eq_negative_line, ordinaryReflectedProfile_eq_negative_line]
  exact congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z) hshift.symm

/-- The actual kernel remains integrable on every farther positive line. -/
theorem integrable_ordinaryReflectionKernel_any
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {A : ℝ} (hA : 0 ≤ A) :
    Integrable (ordinaryReflectionKernel K χ V A) := by
  have h := (integrable_ordinaryMellinMultiplier K hcomplex χ V hA
    (σ := -A) ⟨le_rfl, by linarith⟩).comp_neg
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  have he : idealVerticalPoint (-A) (-t) = 1 - idealVerticalPoint (1 + A) t := by
    unfold idealVerticalPoint
    push_cast
    ring
  simp only [ordinaryMellinMultiplier, ordinaryReflectionKernel, ordinaryGammaRatio, he]

/-- The decay constant and the finite original Euler order are selected
before V and y.  This is the uniform analytic input needed for actual
finite dual-ideal truncation, not a separate reflected-profile assumption. -/
theorem ordinaryReflectedProfile_decay_seminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest), ∀ y : ℝ, 0 < y →
      ‖ordinaryReflectedProfile K χ V δ y‖ ≤
        C * testSeminorm V.toFun J A * y ^ (-(1 + A)) := by
  have hA : 0 ≤ A := hδ.le.trans hδA
  obtain ⟨J, C, hC0, hC⟩ := ordinaryMultiplier_strip_seminorm_bound K hcomplex χ A hA
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))
  have hI : 0 ≤ I := integral_nonneg (fun t => Real.rpow_nonneg (by positivity) _)
  refine ⟨J, ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * I, by positivity, ?_⟩
  intro V y hy
  have hS : 0 ≤ testSeminorm V.toFun J A :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hint : (∫ t : ℝ, ‖ordinaryMellinMultiplier K χ V (idealVerticalPoint (-A) t)‖) ≤
      C * testSeminorm V.toFun J A * I := by
    rw [I, ← integral_const_mul]
    apply integral_mono
      (integrable_ordinaryMellinMultiplier K hcomplex χ V hA ⟨le_rfl, by linarith⟩).norm
      ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul _)
    intro t
    exact hC V (-A) ⟨le_rfl, by linarith⟩ t
  rw [ordinaryReflectedProfile_line_independent K hcomplex χ V hδ hδA hy,
    ordinaryReflectedProfile_eq_negative_line, norm_mul]
  have he (t : ℝ) :
      ‖(mellin V.toFun (idealVerticalPoint (-A) t) *
          ordinaryGammaRatio K χ (idealVerticalPoint (-A) t)) *
        (y : ℂ) ^ (idealVerticalPoint (-A) t - 1)‖ =
      ‖ordinaryMellinMultiplier K χ V (idealVerticalPoint (-A) t)‖ * y ^ (-(1 + A)) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
    rw [show -A - 1 = -(1 + A) by ring]
    rfl
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t : ℝ, ‖(mellin V.toFun (idealVerticalPoint (-A) t) *
          ordinaryGammaRatio K χ (idealVerticalPoint (-A) t)) *
            (y : ℂ) ^ (idealVerticalPoint (-A) t - 1)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = (‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t : ℝ, ‖ordinaryMellinMultiplier K χ V (idealVerticalPoint (-A) t)‖) *
          y ^ (-(1 + A)) := by simp_rw [he]; rw [integral_mul_const]; ring
    _ ≤ (‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * testSeminorm V.toFun J A * I)) *
        y ^ (-(1 + A)) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hint (norm_nonneg _)) (Real.rpow_nonneg hy.le _)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineInduction
