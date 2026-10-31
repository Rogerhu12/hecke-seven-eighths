import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionSmall

/-!
# Both common frequency lines for ordinary reflection

The identity below moves the genuine reflected Mellin integral to every
line in the closed strip [-δ,3/4].  In particular the two original-variable
lines 1/4 and 3/4 are available with the same original test.  Integrability
is deduced from the proved weighted Mellin/Gamma envelope, not supplied
as a hypothesis on a reflected profile.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

/-- The actual Mellin/Gamma density, before any norm scale is inserted. -/
def ordinaryMellinGamma (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (σ t : ℝ) : ℂ :=
  mellin V.toFun (idealVerticalPoint σ t) *
    ordinaryGammaRatio K χ (idealVerticalPoint σ t)

theorem continuous_ordinaryMellinGamma (χ : HeckeCharacter K)
    (V : SmoothAnnularTest) {σ : ℝ} (hσ : σ < 1) :
    Continuous (ordinaryMellinGamma K χ V σ) := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((hM _).mul (differentiableAt_ordinaryGammaRatio K χ
    (by simpa only [idealVerticalPoint_re] using hσ))).continuousAt.comp
      (continuous_idealVerticalPoint σ).continuousAt

/-- The genuine complex density is L1 on either common frequency line. -/
theorem integrable_ordinaryMellinGamma
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ σ : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) :
    Integrable (ordinaryMellinGamma K χ V σ) := by
  obtain ⟨J, C, hC, hbound⟩ := ordinaryMellinGamma_weighted_uniform K
    hcomplex χ hδ (V.lower_pos.trans_le V.upper_ge) 0
  have hn := (hbound V le_rfl σ hσ).2.1
  have hnorm : Integrable (fun t : ℝ => ‖ordinaryMellinGamma K χ V σ t‖) := by
    simpa only [ordinaryMellinGamma, pow_zero, one_mul] using hn
  exact hnorm.mono' (continuous_ordinaryMellinGamma K χ V
    (by linarith [hσ.2])).aestronglyMeasurable (Eventually.of_forall (fun _ => le_rfl))

/-- Inserting any positive norm ratio preserves L1 on a fixed line. -/
theorem integrable_ordinaryMellinGamma_ratio
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ σ y : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) (hy : 0 < y) :
    Integrable (fun t : ℝ => ordinaryMellinGamma K χ V σ t *
      (y : ℂ) ^ (idealVerticalPoint σ t - 1)) := by
  have hc : Continuous (fun t : ℝ => ordinaryMellinGamma K χ V σ t *
      (y : ℂ) ^ (idealVerticalPoint σ t - 1)) :=
    (continuous_ordinaryMellinGamma K χ V (by linarith [hσ.2])).mul
      (((differentiable_id.sub_const (1 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).continuous.comp
          (continuous_idealVerticalPoint σ))
  apply ((integrable_ordinaryMellinGamma K hcomplex χ V hδ hσ).norm.mul_const
    (y ^ (σ - 1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.sub_re, Complex.one_re, idealVerticalPoint_re]

/-- True contour transport to any line needed by the shared-frequency
operator.  The endpoint may equal -δ; no strict contour width is assumed. -/
theorem ordinaryReflectedProfile_eq_line
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ σ y : ℝ}
    (hδ : 0 < δ) (hσ : σ ∈ Icc (-δ) (3 / 4)) (hy : 0 < y) :
    ordinaryReflectedProfile K χ V δ y = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ t : ℝ, ordinaryMellinGamma K χ V σ t *
        (y : ℂ) ^ (idealVerticalPoint σ t - 1) := by
  obtain ⟨J, C, hC0, hC⟩ := ordinaryMellinGamma_weighted_uniform K
    hcomplex χ hδ (V.lower_pos.trans_le V.upper_ge) 0
  let F : ℂ → ℂ := fun s =>
    (mellin V.toFun s * ordinaryGammaRatio K χ s) * (y : ℂ) ^ (s - 1)
  let R : ℝ := y ^ (-δ - 1) + y ^ (-(1 / 4 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ testSeminorm V.toFun J δ :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) δ)
  have hbound : ∀ a ∈ Icc (-δ) σ, ∀ t : ℝ,
      ‖F (idealVerticalPoint a t)‖ ≤
        (C * testSeminorm V.toFun J δ * R) * (1 + |t|) ^ (-(2 : ℝ)) := by
    intro a ha t
    have ha' : a ∈ Icc (-δ) (3 / 4) := ⟨ha.1, ha.2.trans hσ.2⟩
    have hm : ‖mellin V.toFun (idealVerticalPoint a t) *
        ordinaryGammaRatio K χ (idealVerticalPoint a t)‖ ≤
        C * testSeminorm V.toFun J δ * (1 + |t|) ^ (-(2 : ℝ)) := by
      simpa only [pow_zero, one_mul] using (hC V le_rfl a ha').1 t
    have hp : y ^ (a - 1) ≤ R := by
      rcases le_or_gt 1 y with h | h
      · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith [ha'.2])).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg hy.le _))
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h.le (by linarith [ha'.1])).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.sub_re, Complex.one_re, idealVerticalPoint_re]
    exact (mul_le_mul hm hp (Real.rpow_nonneg hy.le _) (by positivity)).trans_eq (by ring)
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  have hshift := verticalIntegral_eq_of_poly_strip
    (f := F) (a := -δ) (b := σ)
    (C := C * testSeminorm V.toFun J δ * R) (e := 2) hσ.1 (by norm_num)
    (fun z _ hz => ((hM z).mul (differentiableAt_ordinaryGammaRatio K χ
      (by linarith [hσ.2]))).mul
        ((differentiableAt_id.sub_const (1 : ℂ)).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))) hbound
  rw [ordinaryReflectedProfile_eq_negative_line]
  exact congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z) hshift

end HeckeSkeleton.Moments.EngineInduction
