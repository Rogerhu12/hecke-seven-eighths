import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularMellin
import HeckeSkeleton.HeckeUniformStripGrowth

/-!
# The genuine ordinary Hecke contour shift for compact annular tests

The right-hand Mellin expansion is proved in `AnnularMellin`.  Here the
actual non-norm Hecke continuation and its already proved explicit-scale
functional equation move that contour to a negative line.  Polynomial
strip growth is combined with the test's Euler decay; no contour transfer
or final reflection estimate is an input.

The last statement retains the actual discriminant-conductor scale, both
ordinary Gamma profiles and the dual absolutely convergent Hecke series.
Turning this contour into uniformly truncated recursive ideal profiles,
and restoring finite deleted Euler factors, are subsequent operations.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.HeckeUniformStripGrowth
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- The literal ordinary Hecke Mellin integrand. -/
def annularHeckeContour (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (X : ℝ) (s : ℂ) : ℂ :=
  (mellin V.toFun s * (X : ℂ) ^ s) * heckeContinuation K χ s

private theorem differentiable_annularHeckeContour (χ : HeckeCharacter K)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) (V : SmoothAnnularTest)
    {X : ℝ} (hX : 0 < X) : Differentiable ℂ (annularHeckeContour K χ V X) := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  exact (hM.mul (differentiable_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')))).mul
      (differentiable_heckeContinuation_of_nonNorm K χ hχ)

/-- The required strip domination follows from proved Hecke growth and
Euler decay.  In particular the constant is independent of strip height. -/
theorem annularHeckeContour_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (V : SmoothAnnularTest) {X δ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (-δ) (1 + δ), ∀ t : ℝ,
      ‖annularHeckeContour K χ V X (idealVerticalPoint σ t)‖ ≤
        C * (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨E, hEpos, hE⟩ := exists_uniform_fixedType_strip_bound K hcomplex
    (fun v => heckeRadialParameter K v χ) (heckeArchWeight K χ) δ hδ hδsmall
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  let B : ℝ := 2 ^ (k + 2) *
    ((Iint V 0 (-(1 + δ)) + Iint V 0 δ) +
      (Iint V (k + 2) (-(1 + δ)) + Iint V (k + 2) δ))
  let R : ℝ := X ^ (-δ) + X ^ (1 + δ)
  let L : ℝ := E * heckeConductorScale K χ ^ (1 / 2 + δ)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _))
        (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _)))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ heckeConductorScale K χ := by
    unfold heckeConductorScale
    positivity
  have hL : 0 ≤ L := mul_nonneg hEpos.le (Real.rpow_nonneg hQ _)
  refine ⟨B * R * (L * 2 ^ k), by positivity, ?_⟩
  intro σ hσ t
  let T : ℝ := 1 + |t|
  have hT : 0 < T := by dsimp [T]; positivity
  have hi0 : Iint V 0 (-σ) ≤ Iint V 0 (-(1 + δ)) + Iint V 0 δ :=
    Iint_strip_le V 0 (by linarith [hσ.2]) (by linarith [hσ.1])
  have hij : Iint V (k + 2) (-σ) ≤
      Iint V (k + 2) (-(1 + δ)) + Iint V (k + 2) δ :=
    Iint_strip_le V (k + 2) (by linarith [hσ.2]) (by linarith [hσ.1])
  have hMB : 2 ^ (k + 2) * (Iint V 0 (-σ) + Iint V (k + 2) (-σ)) ≤ B :=
    mul_le_mul_of_nonneg_left (add_le_add hi0 hij) (by positivity)
  have hMdiv : ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      (2 ^ (k + 2) * (Iint V 0 (-σ) + Iint V (k + 2) (-σ))) / T ^ (k + 2) := by
    simpa only [T, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
      Real.rpow_natCast, div_eq_mul_inv] using
        smoothAnnular_mellin_vertical_decay V (k + 2) σ t
  have hMsmall : T ^ (k + 2) * ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤
      2 ^ (k + 2) * (Iint V 0 (-σ) + Iint V (k + 2) (-σ)) := by
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hT (k + 2))).mp hMdiv
  have hM : T ^ (k + 2) * ‖mellin V.toFun (idealVerticalPoint σ t)‖ ≤ B :=
    hMsmall.trans hMB
  have hscale : X ^ σ ≤ R := by
    rcases le_or_gt 1 X with h | h
    · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hX.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hX h.le hσ.1).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hX.le _))
  have hhecke : ‖heckeContinuation K χ (idealVerticalPoint σ t)‖ ≤ L * (2 + |t|) ^ k := by
    simpa only [idealVerticalPoint_re, idealVerticalPoint_im, L, k] using
      hE χ hχ rfl rfl (idealVerticalPoint σ t)
        (by simpa only [idealVerticalPoint_re] using hσ)
  have hpower : (2 + |t|) ^ k ≤ 2 ^ k * T ^ k := by
    calc
      _ ≤ (2 * T) ^ k := pow_le_pow_left₀ (by positivity)
        (by dsimp [T]; linarith [abs_nonneg t]) k
      _ = _ := mul_pow _ _ _
  have hhecke' : ‖heckeContinuation K χ (idealVerticalPoint σ t)‖ ≤
      (L * 2 ^ k) * T ^ k := by
    exact (hhecke.trans (mul_le_mul_of_nonneg_left hpower hL)).trans_eq (by ring)
  have hnorm : ‖annularHeckeContour K χ V X (idealVerticalPoint σ t)‖ =
      (‖mellin V.toFun (idealVerticalPoint σ t)‖ * X ^ σ) *
        ‖heckeContinuation K χ (idealVerticalPoint σ t)‖ := by
    rw [annularHeckeContour, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hX, idealVerticalPoint_re]
  have hweighted : T ^ 2 * ‖annularHeckeContour K χ V X (idealVerticalPoint σ t)‖ ≤
      B * R * (L * 2 ^ k) := by
    rw [hnorm]
    calc
      _ ≤ T ^ 2 * ((‖mellin V.toFun (idealVerticalPoint σ t)‖ * R) *
          ((L * 2 ^ k) * T ^ k)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg T)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hscale (norm_nonneg _)) hhecke'
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hR)
      _ = (T ^ (k + 2) * ‖mellin V.toFun (idealVerticalPoint σ t)‖) * R *
          (L * 2 ^ k) := by rw [pow_add]; ring
      _ ≤ B * R * (L * 2 ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR) (by positivity)
  have hdiv : ‖annularHeckeContour K χ V X (idealVerticalPoint σ t)‖ ≤
      (B * R * (L * 2 ^ k)) / T ^ 2 :=
    (le_div_iff₀ (pow_pos hT 2)).2 (by simpa only [mul_comm] using hweighted)
  simpa only [T, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    Real.rpow_ofNat, div_eq_mul_inv] using hdiv

/-- Every intermediate contour is absolutely integrable. -/
theorem integrable_annularHeckeContour
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (V : SmoothAnnularTest) {X δ σ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hσ : σ ∈ Icc (-δ) (1 + δ)) :
    Integrable (fun t : ℝ => annularHeckeContour K χ V X (idealVerticalPoint σ t)) := by
  obtain ⟨C, _, hC⟩ := annularHeckeContour_strip_bound K hcomplex χ hχ V hX hδ hδsmall
  have hc := (differentiable_annularHeckeContour K χ hχ V hX).continuous.comp
    (continuous_idealVerticalPoint σ)
  apply ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul C).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (hC σ hσ)

/-- The actual finite ideal polynomial admits the negative ordinary
Hecke contour, proved by analyticity and a decaying rectangle argument. -/
theorem annularHeckeSum_shift
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (V : SmoothAnnularTest) {X δ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    annularIdealSum K (heckeIdealCoefficient K χ) V X =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (-δ) t) := by
  obtain ⟨C, _, hC⟩ := annularHeckeContour_strip_bound K hcomplex χ hχ V hX hδ hδsmall
  have hshift := verticalIntegral_eq_of_poly_strip
    (f := annularHeckeContour K χ V X) (a := -δ) (b := 1 + δ) (C := C) (e := 2)
    (by linarith) (by norm_num)
    (fun z _ _ => differentiable_annularHeckeContour K χ hχ V hX z) hC
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (1 + δ) t) := by
      rw [annularHeckeSum_mellin K χ V (show 1 < 1 + δ by linarith) hX]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [annularHeckeContour, heckeContinuation_eq_series K χ (by
        simp only [idealVerticalPoint_re]; linarith)]
    _ = _ := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z) hshift.symm

/-- The genuine explicit-conductor FE transforms the negative contour
into an ordinary dual-series contour.  The integral is proved convergent,
and the unit scalar is the root number supplied by that actual FE. -/
theorem annularHeckeSum_reflectedContour
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (V : SmoothAnnularTest) {X δ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      let f : ℝ → ℂ := fun t =>
        let s := idealVerticalPoint (-δ) t
        (mellin V.toFun s * (X : ℂ) ^ s) *
          (((canonicalHeckeGammaProfile K χ s)⁻¹ *
            canonicalHeckeGammaProfile K χ⁻¹ (1 - s) * heckeLSeries K χ⁻¹ (1 - s)) /
              (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)))
      Integrable f ∧ annularIdealSum K (heckeIdealCoefficient K χ) V X =
        (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, f t := by
  obtain ⟨ε, hε, _, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  refine ⟨ε, hε, ?_⟩
  let f : ℝ → ℂ := fun t =>
    let s := idealVerticalPoint (-δ) t
    (mellin V.toFun s * (X : ℂ) ^ s) *
      (((canonicalHeckeGammaProfile K χ s)⁻¹ *
        canonicalHeckeGammaProfile K χ⁻¹ (1 - s) * heckeLSeries K χ⁻¹ (1 - s)) /
          (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)))
  have he (t : ℝ) : annularHeckeContour K χ V X (idealVerticalPoint (-δ) t) = f t := by
    dsimp [annularHeckeContour, f]
    rw [hFE _ (by simp only [idealVerticalPoint_re]; linarith),
      heckeContinuation_eq_series K χ⁻¹ (by
        simp only [Complex.sub_re, Complex.one_re, idealVerticalPoint_re]; linarith)]
  constructor
  · exact (integrable_annularHeckeContour K hcomplex χ hχ V hX hδ hδsmall
      ⟨le_rfl, by linarith⟩).congr (Filter.Eventually.of_forall he)
  · rw [annularHeckeSum_shift K hcomplex χ hχ V hX hδ hδsmall]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall he)

end HeckeSkeleton.Moments.EngineInduction
