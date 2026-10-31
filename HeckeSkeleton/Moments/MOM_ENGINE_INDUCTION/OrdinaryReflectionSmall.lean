import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionUniformity
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryGammaRight

/-!
# The actual reflected profile at small norm ratios

Move the original-variable contour from Re(s)=-δ to Re(s)=3/4.
The dual variable then has real part 1/4.  No poles are crossed: the
remaining Gamma factor has positive real argument throughout.  A fixed
upper bound on the original compact support converts the additional
positive Mellin moment to the original Euler seminorm.  Consequently
short annular windows have the summable normalized size r^(1/4).
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

private theorem Iint_three_quarters_le (V : SmoothAnnularTest)
    {B : ℝ} (hB : 0 < B) (hupper : V.upper ≤ B) (j : ℕ) :
    Iint V j (-3 / 4) ≤ B ^ (1 / 2 : ℝ) * Iint V j (-1 / 4) := by
  unfold Iint
  rw [← integral_const_mul]
  apply setIntegral_mono_on (integrableOn_Iint V j (-3 / 4))
    ((integrableOn_Iint V j (-1 / 4)).const_mul _) measurableSet_Ioi
  intro y hy
  by_cases hmem : y ∈ Icc V.lower V.upper
  · have hypos : 0 < y := hy
    have hp : y ^ (-(-(3 : ℝ) / 4) - 1) =
        y ^ (1 / 2 : ℝ) * y ^ (-(-(1 : ℝ) / 4) - 1) := by
      rw [← Real.rpow_add hypos]
      congr 1
      norm_num
    have hpow : y ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hypos.le (hmem.2.trans hupper) (by norm_num)
    calc
      _ = y ^ (1 / 2 : ℝ) * (‖eul V j y‖ * y ^ (-(-(1 : ℝ) / 4) - 1)) := by
        rw [hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
  · rw [(good_eul V j).zero y hmem, norm_zero]
    simp only [zero_mul, mul_zero]

private def ordinaryShortMultiplier (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) (s : ℂ) : ℂ :=
  mellin V.toFun s * ordinaryGammaRatio K χ s

private theorem ordinaryShortMultiplier_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ σ ∈ Icc (-δ) (3 / 4), ∀ t : ℝ,
      ‖ordinaryShortMultiplier K χ V (idealVerticalPoint σ t)‖ ≤
        C * testSeminorm V.toFun J δ * (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨G, hG, hGb⟩ := ordinaryGammaRatio_leftOfOne_strip_bound K hcomplex χ
    δ (3 / 4) hδ.le (by norm_num) (by norm_num)
  let k : ℕ := (2 * Nat.ceil δ + 2) * Fintype.card (InfinitePlace K)
  let J : ℕ := k + 2
  let D : ℝ := B ^ (1 / 2 : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨J, (2 * 2 ^ J * D) * G, by positivity, ?_⟩
  intro V hupper σ hσ t
  let S : ℝ := testSeminorm V.toFun J δ
  let T : ℝ := 1 + |t|
  have hT : 0 < T := by dsimp [T]; positivity
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 J (Nat.zero_le _) δ)
  have hi (j : ℕ) (hj : j ≤ J) : Iint V j (-σ) ≤ D * S := by
    have h := Iint_strip_le V j (σ1 := -3 / 4) (σ2 := δ)
      (by linarith [hσ.2]) (by linarith [hσ.1])
    have hl := (Iint_three_quarters_le V hB hupper j).trans
      (mul_le_mul_of_nonneg_left (Iint_left_le V j J hj δ)
        (Real.rpow_nonneg hB.le _))
    have hr := Iint_right_le V j J hj δ
    dsimp [D, S]
    nlinarith
  have hMB : 2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ)) ≤
      (2 * 2 ^ J * D) * S := by
    calc
      _ ≤ 2 ^ J * (D * S + D * S) :=
        mul_le_mul_of_nonneg_left (add_le_add (hi 0 (Nat.zero_le _)) (hi J le_rfl))
          (by positivity)
      _ = _ := by ring
  have hM : ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      ((2 * 2 ^ J * D) * S) * T ^ (-(J : ℝ)) :=
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
    ‖ordinaryShortMultiplier K χ V (idealVerticalPoint σ t)‖ =
        ‖mellin V.toFun (idealVerticalPoint σ t)‖ *
          ‖ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ := norm_mul _ _
    _ ≤ (((2 * 2 ^ J * D) * S) * T ^ (-(J : ℝ))) * (G * T ^ k) :=
      mul_le_mul hM hgamma (norm_nonneg _) (by positivity)
    _ = ((2 * 2 ^ J * D) * G) * S * (1 + |t|) ^ (-(2 : ℝ)) := by
      calc
        _ = ((2 * 2 ^ J * D) * G) * S * (T ^ (-(J : ℝ)) * T ^ k) := by ring
        _ = _ := by rw [he]

private theorem differentiableAt_ordinaryShortMultiplier
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (ordinaryShortMultiplier K χ V) s := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  exact (hM s).mul (differentiableAt_ordinaryGammaRatio K χ hs)

private theorem integrable_ordinaryShortMultiplier
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ B σ : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hupper : V.upper ≤ B)
    (hσ : σ ∈ Icc (-δ) (3 / 4)) :
    Integrable (fun t : ℝ => ordinaryShortMultiplier K χ V (idealVerticalPoint σ t)) := by
  obtain ⟨J, C, _, hC⟩ := ordinaryShortMultiplier_strip_bound K hcomplex χ hδ hB
  have hc : Continuous (fun t : ℝ => ordinaryShortMultiplier K χ V (idealVerticalPoint σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_ordinaryShortMultiplier K χ V (by
      simp only [idealVerticalPoint_re]; linarith [hσ.2])).continuousAt.comp
        (continuous_idealVerticalPoint σ).continuousAt
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul
    (C * testSeminorm V.toFun J δ)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (hC V hupper σ hσ)

/-- A genuine contour shift to dual real part 1/4.  The original annular
support provides every Mellin moment needed for the horizontal decay. -/
theorem ordinaryReflectedProfile_eq_quarter_line
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ y : ℝ}
    (hδ : 0 < δ) (hy : 0 < y) :
    ordinaryReflectedProfile K χ V δ y = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t : ℝ, (mellin V.toFun (idealVerticalPoint (3 / 4) t) *
        ordinaryGammaRatio K χ (idealVerticalPoint (3 / 4) t)) *
          (y : ℂ) ^ (idealVerticalPoint (3 / 4) t - 1) := by
  have hB : 0 < V.upper := V.lower_pos.trans_le V.upper_ge
  obtain ⟨J, C, hC0, hC⟩ := ordinaryShortMultiplier_strip_bound K hcomplex χ hδ hB
  let F : ℂ → ℂ := fun s => ordinaryShortMultiplier K χ V s * (y : ℂ) ^ (s - 1)
  let R : ℝ := y ^ (-δ - 1) + y ^ (-(1 / 4 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ testSeminorm V.toFun J δ :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) δ)
  have hbound : ∀ σ ∈ Icc (-δ) (3 / 4), ∀ t : ℝ,
      ‖F (idealVerticalPoint σ t)‖ ≤
        (C * testSeminorm V.toFun J δ * R) * (1 + |t|) ^ (-(2 : ℝ)) := by
    intro σ hσ t
    have hm := hC V le_rfl σ hσ t
    have hp : y ^ (σ - 1) ≤ R := by
      rcases le_or_gt 1 y with h | h
      · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith [hσ.2])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hy.le _))
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h.le (by linarith [hσ.1])).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
    rw [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
    exact (mul_le_mul hm hp (Real.rpow_nonneg hy.le _) (by positivity)).trans_eq (by ring)
  have hshift := verticalIntegral_eq_of_poly_strip
    (f := F) (a := -δ) (b := 3 / 4)
    (C := C * testSeminorm V.toFun J δ * R) (e := 2)
    (by linarith) (by norm_num)
    (fun z _ hz => (differentiableAt_ordinaryShortMultiplier K χ V (by linarith)).mul
      ((differentiableAt_id.sub_const (1 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))) hbound
  rw [ordinaryReflectedProfile_eq_negative_line]
  exact congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z) hshift

/-- The common support bound is chosen before V.  This bound makes the
normalized short-window factor r^(1/2) genuinely summable near zero. -/
theorem ordinaryReflectedProfile_small_seminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ y : ℝ, 0 < y →
      ‖ordinaryReflectedProfile K χ V δ y‖ ≤
        C * testSeminorm V.toFun J δ * y ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨J, C, hC0, hC⟩ := ordinaryShortMultiplier_strip_bound K hcomplex χ hδ hB
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))
  have hI : 0 ≤ I := integral_nonneg (fun t => Real.rpow_nonneg (by positivity) _)
  refine ⟨J, ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * I, by positivity, ?_⟩
  intro V hupper y hy
  have hσ : (3 / 4 : ℝ) ∈ Icc (-δ) (3 / 4) := ⟨by linarith, le_rfl⟩
  have hint : (∫ t : ℝ, ‖ordinaryShortMultiplier K χ V (idealVerticalPoint (3 / 4) t)‖) ≤
      C * testSeminorm V.toFun J δ * I := by
    rw [I, ← integral_const_mul]
    apply integral_mono
      (integrable_ordinaryShortMultiplier K hcomplex χ V hδ hB hupper hσ).norm
      ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul _)
    intro t
    exact hC V hupper (3 / 4) hσ t
  rw [ordinaryReflectedProfile_eq_quarter_line K hcomplex χ V hδ hy, norm_mul]
  have he (t : ℝ) :
      ‖(mellin V.toFun (idealVerticalPoint (3 / 4) t) *
          ordinaryGammaRatio K χ (idealVerticalPoint (3 / 4) t)) *
        (y : ℂ) ^ (idealVerticalPoint (3 / 4) t - 1)‖ =
      ‖ordinaryShortMultiplier K χ V (idealVerticalPoint (3 / 4) t)‖ *
        y ^ (-(1 / 4 : ℝ)) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
    rw [show (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) by norm_num]
    rfl
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t : ℝ, ‖(mellin V.toFun (idealVerticalPoint (3 / 4) t) *
          ordinaryGammaRatio K χ (idealVerticalPoint (3 / 4) t)) *
            (y : ℂ) ^ (idealVerticalPoint (3 / 4) t - 1)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = (‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t : ℝ, ‖ordinaryShortMultiplier K χ V (idealVerticalPoint (3 / 4) t)‖) *
          y ^ (-(1 / 4 : ℝ)) := by simp_rw [he]; rw [integral_mul_const]; ring
    _ ≤ (‖(2 * (Real.pi : ℂ))⁻¹‖ * (C * testSeminorm V.toFun J δ * I)) *
        y ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hint (norm_nonneg _)) (Real.rpow_nonneg hy.le _)
    _ = _ := by ring

/-- Actual finite-order row twists preserve this small-ratio bound with
one common constant and Euler order, selected before the row and test. -/
theorem ordinaryReflectedProfile_finiteRows_small
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (χ : HeckeCharacter K), FiniteOrder χ →
      ∀ (V : SmoothAnnularTest), V.upper ≤ B → ∀ y : ℝ, 0 < y →
        ‖ordinaryReflectedProfile K (β * χ) V δ y‖ ≤
          C * testSeminorm V.toFun J δ * y ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨J, C, hC, hbound⟩ := ordinaryReflectedProfile_small_seminorm K hcomplex β hδ hB
  refine ⟨J, C, hC, ?_⟩
  intro χ hχ V hupper y hy
  rw [ordinaryReflectedProfile_mul_finiteOrder K hcomplex β χ hχ]
  exact hbound V hupper y hy


/-- A common polynomially weighted Mellin/Gamma envelope, and its actual
L1 property.  Its Euler order and constant precede every original test,
line and frequency.  This permits frequency seminorm costs to be charged
to a genuine common reflection kernel instead of being bounded uniformly
in the unbounded Fourier parameter. -/
theorem ordinaryMellinGamma_weighted_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) (n : ℕ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ σ ∈ Icc (-δ) (3 / 4),
      (∀ t : ℝ, (1 + |t|) ^ n *
        ‖mellin V.toFun (idealVerticalPoint σ t) *
          ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ ≤
          C * testSeminorm V.toFun J δ * (1 + |t|) ^ (-(2 : ℝ))) ∧
      Integrable (fun t : ℝ => (1 + |t|) ^ n *
        ‖mellin V.toFun (idealVerticalPoint σ t) *
          ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖) ∧
      (∫ t : ℝ, (1 + |t|) ^ n *
        ‖mellin V.toFun (idealVerticalPoint σ t) *
          ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖) ≤
          C * testSeminorm V.toFun J δ *
            ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨G, hG, hGb⟩ := ordinaryGammaRatio_leftOfOne_strip_bound K hcomplex χ
    δ (3 / 4) hδ.le (by norm_num) (by norm_num)
  let k : ℕ := (2 * Nat.ceil δ + 2) * Fintype.card (InfinitePlace K)
  let J : ℕ := k + n + 2
  let D : ℝ := B ^ (1 / 2 : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := (2 * 2 ^ J * D) * G
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨J, C, hC, ?_⟩
  intro V hupper σ hσ
  let S : ℝ := testSeminorm V.toFun J δ
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 J (Nat.zero_le _) δ)
  have hi (j : ℕ) (hj : j ≤ J) : Iint V j (-σ) ≤ D * S := by
    have h := Iint_strip_le V j (σ1 := -3 / 4) (σ2 := δ)
      (by linarith [hσ.2]) (by linarith [hσ.1])
    have hl := (Iint_three_quarters_le V hB hupper j).trans
      (mul_le_mul_of_nonneg_left (Iint_left_le V j J hj δ)
        (Real.rpow_nonneg hB.le _))
    have hr := Iint_right_le V j J hj δ
    dsimp [D, S]
    nlinarith
  have hMB : 2 ^ J * (Iint V 0 (-σ) + Iint V J (-σ)) ≤
      (2 * 2 ^ J * D) * S := by
    calc
      _ ≤ 2 ^ J * (D * S + D * S) :=
        mul_le_mul_of_nonneg_left (add_le_add (hi 0 (Nat.zero_le _)) (hi J le_rfl))
          (by positivity)
      _ = _ := by ring
  have hpoint (t : ℝ) : (1 + |t|) ^ n *
      ‖mellin V.toFun (idealVerticalPoint σ t) *
        ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ ≤
        C * S * (1 + |t|) ^ (-(2 : ℝ)) := by
    let T : ℝ := 1 + |t|
    have hT : 0 < T := by dsimp [T]; positivity
    have hM : ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
        ((2 * 2 ^ J * D) * S) * T ^ (-(J : ℝ)) :=
      (smoothAnnular_mellin_vertical_decay V J σ t).trans
        (mul_le_mul_of_nonneg_right hMB (Real.rpow_nonneg hT.le _))
    have hgamma : ‖ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖ ≤ G * T ^ k := by
      simpa only [idealVerticalPoint_re, idealVerticalPoint_im, T, k] using
        hGb (idealVerticalPoint σ t) (by simpa only [idealVerticalPoint_re] using hσ.1)
          (by simpa only [idealVerticalPoint_re] using hσ.2)
    have he : T ^ n * T ^ (-(J : ℝ)) * T ^ k = T ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast T n, ← Real.rpow_natCast T k,
        ← Real.rpow_add hT, ← Real.rpow_add hT]
      congr 1
      dsimp [J]
      push_cast
      ring
    rw [norm_mul]
    calc
      _ ≤ T ^ n * ((((2 * 2 ^ J * D) * S) * T ^ (-(J : ℝ))) * (G * T ^ k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM hgamma (norm_nonneg _) (by positivity))
          (pow_nonneg hT.le _)
      _ = C * S * (1 + |t|) ^ (-(2 : ℝ)) := by
        calc
          _ = C * S * (T ^ n * T ^ (-(J : ℝ)) * T ^ k) := by dsimp [C]; ring
          _ = _ := by rw [he]
  have hc : Continuous (fun t : ℝ => ordinaryShortMultiplier K χ V (idealVerticalPoint σ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_ordinaryShortMultiplier K χ V (by
      simp only [idealVerticalPoint_re]; linarith [hσ.2])).continuousAt.comp
        (continuous_idealVerticalPoint σ).continuousAt
  have hint : Integrable (fun t : ℝ => (1 + |t|) ^ n *
      ‖mellin V.toFun (idealVerticalPoint σ t) *
        ordinaryGammaRatio K χ (idealVerticalPoint σ t)‖) := by
    apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul (C * S)).mono'
      (((continuous_const.add continuous_abs).pow n).mul hc.norm).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    exact hpoint t
  refine ⟨hpoint, hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint
    ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul (C * S)) hpoint

end HeckeSkeleton.Moments.EngineInduction
