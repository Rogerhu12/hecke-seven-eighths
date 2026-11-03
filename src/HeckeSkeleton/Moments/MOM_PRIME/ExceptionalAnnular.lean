import HeckeSkeleton.Moments.MOM_PRIME.AnnularMellin
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalContinuation
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalSmooth
import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift

/-!
# Actual annular exceptional sums

The contour crosses the actual principal pole and ends on Re(s)=0.
Consequently the remainder is uniform at every positive physical length.
The norm phase is moved onto the Mellin argument, so its polynomial loss
is obtained by translation of a fixed integrable envelope.  No ideal-sum
asymptotic or volume functional is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckePort.Moments.Twist
open scoped BigOperators Classical Topology

/-- Multiplication by the norm phase preserves the actual annulus. -/
def phaseAnnularTest (V : SmoothAnnularTest) (t : ℝ) : SmoothAnnularTest where
  toFun y := (y : ℂ) ^ (Complex.I * t) * V.toFun y
  smooth := contDiff_normPowerWeight V.toFun V.lower V.upper V.lower_pos V.support V.smooth t
  lower := V.lower
  upper := V.upper
  lower_pos := V.lower_pos
  upper_ge := V.upper_ge
  support := by
    intro y hy
    apply V.support
    intro hz
    exact hy (by simp only [hz, mul_zero])

@[simp] theorem phaseAnnularTest_apply (V : SmoothAnnularTest) (t y : ℝ) :
    (phaseAnnularTest V t).toFun y = (y : ℂ) ^ (Complex.I * t) * V.toFun y := rfl

/-- The exact Mellin translation removes derivatives of the oscillating
phase from the quantitative estimate. -/
theorem mellin_phaseAnnularTest (V : SmoothAnnularTest) (t : ℝ) (s : ℂ) :
    mellin (phaseAnnularTest V t).toFun s = mellin V.toFun (s + Complex.I * t) := by
  simpa only [phaseAnnularTest, smul_eq_mul] using
    mellin_cpow_smul V.toFun s (Complex.I * t)

theorem mellin_phaseAnnularTest_vertical (V : SmoothAnnularTest) (t σ u : ℝ) :
    mellin (phaseAnnularTest V t).toFun (idealVerticalPoint σ u) =
      mellin V.toFun (idealVerticalPoint σ (u + t)) := by
  rw [mellin_phaseAnnularTest]
  congr 1
  dsimp [idealVerticalPoint]
  push_cast
  ring

variable (K : Type) [Field K] [NumberField K]

def exceptionalHeckeContour (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (X : ℝ) (s : ℂ) : ℂ :=
  (mellin V.toFun s * (X : ℂ) ^ s) * heckeContinuation K χ s

theorem differentiableAt_exceptionalHeckeContour
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (exceptionalHeckeContour K χ V X) s := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  exact ((hM s).mul (differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')))).mul
      (actualExceptionalContinuation_differentiableAt K χ hχ s hs)

theorem exceptionalHeckeContour_residue
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun s : ℂ => (s - 1) * exceptionalHeckeContour K χ V X s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 ((X : ℂ) * actualExceptionalResidue K χ * mellin V.toFun 1)) := by
  have hM : Differentiable ℂ (mellin V.toFun) := by
    simpa only [Function.comp_def, neg_neg] using
      (differentiable_mellin_neg V).comp differentiable_neg
  have hP : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have h := (((hM.continuous.tendsto 1).mul (hP.continuous.tendsto 1)).mono_left
    nhdsWithin_le_nhds).mul (actualExceptionalContinuation_residue K χ hχ)
  convert h using 1
  · funext s
    dsimp [exceptionalHeckeContour]
    ring
  · rw [Complex.cpow_one]
    congr 1
    ring

/-- Polynomial continuation control and Euler decay supply the horizontal
edge domination required by the residue theorem. -/
theorem exceptionalHeckeContour_strip_bound
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 11 / 10 → 1 ≤ |s.im| →
      ‖heckeContinuation K χ s‖ ≤ C * (1 + |s.im|) ^ n) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ σ ∈ Icc (0 : ℝ) (11 / 10), ∀ u : ℝ,
      1 ≤ |u| → ‖exceptionalHeckeContour K χ V X (idealVerticalPoint σ u)‖ ≤
        E * (1 + |u|) ^ (-(2 : ℝ)) := by
  let B : ℝ := 2 ^ (n + 2) *
    ((Iint V 0 (-(11 / 10)) + Iint V 0 0) +
      (Iint V (n + 2) (-(11 / 10)) + Iint V (n + 2) 0))
  let R : ℝ := 1 + X ^ (11 / 10 : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _))
        (add_nonneg (Iint_nonneg V _ _) (Iint_nonneg V _ _)))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨B * R * C, by positivity, ?_⟩
  intro σ hσ u hu
  let T : ℝ := 1 + |u|
  have hT : 0 < T := by dsimp [T]; positivity
  have hi0 : Iint V 0 (-σ) ≤ Iint V 0 (-(11 / 10)) + Iint V 0 0 :=
    Iint_strip_le V 0 (by linarith [hσ.2]) (by linarith [hσ.1])
  have hij : Iint V (n + 2) (-σ) ≤
      Iint V (n + 2) (-(11 / 10)) + Iint V (n + 2) 0 :=
    Iint_strip_le V (n + 2) (by linarith [hσ.2]) (by linarith [hσ.1])
  have hMB : 2 ^ (n + 2) * (Iint V 0 (-σ) + Iint V (n + 2) (-σ)) ≤ B :=
    mul_le_mul_of_nonneg_left (add_le_add hi0 hij) (by positivity)
  have hMdiv : ‖mellin V.toFun (idealVerticalPoint σ u)‖ ≤
      (2 ^ (n + 2) * (Iint V 0 (-σ) + Iint V (n + 2) (-σ))) / T ^ (n + 2) := by
    simpa only [T, Real.rpow_neg (by positivity : 0 ≤ 1 + |u|),
      Real.rpow_natCast, div_eq_mul_inv] using
        smoothAnnular_mellin_vertical_decay V (n + 2) σ u
  have hM : T ^ (n + 2) * ‖mellin V.toFun (idealVerticalPoint σ u)‖ ≤ B := by
    apply le_trans _ hMB
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hT (n + 2))).mp hMdiv
  have hscale : X ^ σ ≤ R := by
    rcases le_or_gt 1 X with h | h
    · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans
        (le_add_of_nonneg_left (by norm_num))
    · have hh : X ^ σ ≤ 1 := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_ge hX h.le hσ.1
      exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg hX.le _))
  have hhecke : ‖heckeContinuation K χ (idealVerticalPoint σ u)‖ ≤ C * T ^ n := by
    simpa only [idealVerticalPoint_re, idealVerticalPoint_im, T] using
      hL (idealVerticalPoint σ u)
        (by simpa only [idealVerticalPoint_re] using hσ.1)
        (by simpa only [idealVerticalPoint_re] using hσ.2)
        (by simpa only [idealVerticalPoint_im] using hu)
  have hnorm : ‖exceptionalHeckeContour K χ V X (idealVerticalPoint σ u)‖ =
      (‖mellin V.toFun (idealVerticalPoint σ u)‖ * X ^ σ) *
        ‖heckeContinuation K χ (idealVerticalPoint σ u)‖ := by
    rw [exceptionalHeckeContour, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hX, idealVerticalPoint_re]
  have hweighted : T ^ 2 * ‖exceptionalHeckeContour K χ V X (idealVerticalPoint σ u)‖ ≤
      B * R * C := by
    rw [hnorm]
    calc
      _ ≤ T ^ 2 * ((‖mellin V.toFun (idealVerticalPoint σ u)‖ * R) *
          (C * T ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg T)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hscale (norm_nonneg _)) hhecke
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hR)
      _ = (T ^ (n + 2) * ‖mellin V.toFun (idealVerticalPoint σ u)‖) * R * C := by
        rw [pow_add]
        ring
      _ ≤ B * R * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hM hR) hC
  have hdiv : ‖exceptionalHeckeContour K χ V X (idealVerticalPoint σ u)‖ ≤
      (B * R * C) / T ^ 2 :=
    (le_div_iff₀ (pow_pos hT 2)).2 (by simpa only [mul_comm] using hweighted)
  simpa only [T, Real.rpow_neg (by positivity : 0 ≤ 1 + |u|),
    Real.rpow_ofNat, div_eq_mul_inv] using hdiv

/-- The actual principal residue and the actual non-norm continuation
give one exact zero-line identity, valid for every positive scale. -/
theorem annularHeckeSum_sub_residue
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    annularIdealSum K (heckeIdealCoefficient K χ) V X -
      (X : ℂ) * actualExceptionalResidue K χ * mellin V.toFun 1 =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ u : ℝ, exceptionalHeckeContour K χ V X (idealVerticalPoint 0 u) := by
  obtain ⟨n, C, hC, _, hL⟩ :=
    exists_actualExceptionalContinuation_control K hcomplex χ hχ
  obtain ⟨E, _, hE⟩ := exceptionalHeckeContour_strip_bound K χ V hX n C hC.le hL
  have hshift :=
    DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift.verticalIntegral_sub_eq_residue_of_decay
      (a := 0) (b := 11 / 10) (p := (1 : ℂ))
      (f := exceptionalHeckeContour K χ V X)
      (by norm_num) (by norm_num)
      (fun s hs =>
        (differentiableAt_exceptionalHeckeContour K χ hχ V hX
          (by simpa only [Set.mem_singleton_iff] using hs.2)).differentiableWithinAt)
      (exceptionalHeckeContour_residue K χ hχ V hX) E 1 hE
  have hright : annularIdealSum K (heckeIdealCoefficient K χ) V X =
      DedekindZetaZeroFree.comparisonVerticalIntegral (11 / 10)
        (exceptionalHeckeContour K χ V X) := by
    rw [annularHeckeSum_mellin K χ V (by norm_num : (1 : ℝ) < 11 / 10) hX]
    unfold DedekindZetaZeroFree.comparisonVerticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with u
    rw [exceptionalHeckeContour, heckeContinuation_eq_series K χ (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num)]
    rfl
  rw [← hright] at hshift
  change _ - _ = _ at hshift
  change _ = DedekindZetaZeroFree.comparisonVerticalIntegral 0
    (exceptionalHeckeContour K χ V X)
  linear_combination hshift

end HeckeSkeleton.Moments.MOM_PRIME
