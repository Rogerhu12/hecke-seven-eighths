import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnular
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalHecke

/-!
# The genuine all-scale exceptional volume estimate

The error is bounded by a fixed Euler seminorm of the original annular
test.  The only height loss is a polynomial whose order and constant are
chosen before the test, the norm phase and the physical scale.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Expansion.SmallRows
open HeckePort.CenteredMoment HeckePort.Moments.Twist
open scoped BigOperators Classical Topology nonZeroDivisors

/-- Two explicit Euler seminorms suffice for one fixed continuation order.
This is a seminorm of the original test, before any norm phase is applied. -/
def annularErrorSeminorm (V : SmoothAnnularTest) (n : ℕ) : ℝ :=
  Iint V 0 0 + Iint V (n + 2) 0

theorem annularErrorSeminorm_nonneg (V : SmoothAnnularTest) (n : ℕ) :
    0 ≤ annularErrorSeminorm V n :=
  add_nonneg (Iint_nonneg V 0 0) (Iint_nonneg V (n + 2) 0)

/-- The error functional is controlled by the repository's literal Euler
test seminorm.  Increasing the order allows a finite background family
to use one common seminorm. -/
theorem annularErrorSeminorm_le_testSeminorm (V : SmoothAnnularTest)
    (n J : ℕ) (hJ : n + 2 ≤ J) :
    annularErrorSeminorm V n ≤ 2 * testSeminorm V.toFun J 0 := by
  have h0 := Iint_right_le V 0 J (Nat.zero_le J) 0
  have hn := Iint_right_le V (n + 2) J hJ 0
  dsimp [annularErrorSeminorm]
  linarith

/-- The universal integrable envelope contributes only this numerical
constant; its exact value is irrelevant to uniformity. -/
def annularContourMass : ℝ :=
  ‖(2 * (Real.pi : ℂ))⁻¹‖ * ∫ u : ℝ, (1 + |u|) ^ (-(2 : ℝ))

theorem annularContourMass_nonneg : 0 ≤ annularContourMass := by
  apply mul_nonneg (norm_nonneg _)
  exact integral_nonneg (fun u => Real.rpow_nonneg (by positivity) _)

/-- Mellin inversion also controls the pointwise norm of the test by the
same explicit Euler integrals.  Thus the absolute ideal-counting estimate
needs no additional profile-norm premise. -/
theorem smoothAnnular_norm_le_errorSeminorm (V : SmoothAnnularTest) (y : ℝ) :
    ‖V.toFun y‖ ≤ 4 * annularContourMass * annularErrorSeminorm V 0 := by
  by_cases hy : 0 < y
  · rw [← smoothAnnular_mellin_inversion V 0 hy, norm_mul]
    have hi : Integrable (fun u : ℝ =>
        (4 * annularErrorSeminorm V 0) * (1 + |u|) ^ (-(2 : ℝ))) :=
      (integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul _
    have hb : ‖∫ u : ℝ, (y : ℂ) ^ (-idealVerticalPoint 0 u) *
        mellin V.toFun (idealVerticalPoint 0 u)‖ ≤
        ∫ u : ℝ, (4 * annularErrorSeminorm V 0) * (1 + |u|) ^ (-(2 : ℝ)) := by
      apply norm_integral_le_of_norm_le hi
      apply Eventually.of_forall
      intro u
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
        Complex.neg_re, idealVerticalPoint_re, neg_zero, Real.rpow_zero, one_mul]
      simpa only [annularErrorSeminorm, zero_add, neg_zero,
        show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
          smoothAnnular_mellin_vertical_decay V 2 0 u
    rw [integral_const_mul] at hb
    calc
      _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
          ((4 * annularErrorSeminorm V 0) *
            ∫ u : ℝ, (1 + |u|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by dsimp [annularContourMass]; ring
  · have hz : V.toFun y = 0 := by
      by_contra h
      exact hy (V.lower_pos.trans_le (V.support h).1)
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) annularContourMass_nonneg)
      (annularErrorSeminorm_nonneg V 0)

theorem smoothAnnular_norm_le_testSeminorm (V : SmoothAnnularTest)
    (J : ℕ) (hJ : 2 ≤ J) (y : ℝ) :
    ‖V.toFun y‖ ≤ 8 * annularContourMass * testSeminorm V.toFun J 0 := by
  calc
    _ ≤ 4 * annularContourMass * annularErrorSeminorm V 0 :=
      smoothAnnular_norm_le_errorSeminorm V y
    _ ≤ 4 * annularContourMass * (2 * testSeminorm V.toFun J 0) :=
      mul_le_mul_of_nonneg_left (annularErrorSeminorm_le_testSeminorm V 0 J hJ)
        (mul_nonneg (by norm_num) annularContourMass_nonneg)
    _ = _ := by ring

variable (K : Type) [Field K] [NumberField K]

/-- The zero-line envelope has no dependence on the physical length.
Its translation in `u` has the same integral for every norm phase `t`. -/
theorem exceptionalHeckeContour_phase_zero_bound
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s : ℂ, s.re = 0 →
      ‖heckeContinuation K χ s‖ ≤ C * (1 + |s.im|) ^ n)
    (t u : ℝ) :
    ‖exceptionalHeckeContour K χ (phaseAnnularTest V t) X (idealVerticalPoint 0 u)‖ ≤
      (2 ^ (n + 2) * annularErrorSeminorm V n * C * (1 + |t|) ^ n) *
        (1 + |u + t|) ^ (-(2 : ℝ)) := by
  let T : ℝ := 1 + |u + t|
  let H : ℝ := 1 + |t|
  let B : ℝ := 2 ^ (n + 2) * annularErrorSeminorm V n
  have hT : 0 < T := by dsimp [T]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hB : 0 ≤ B := mul_nonneg (by positivity) (annularErrorSeminorm_nonneg V n)
  have hheight : 1 + |u| ≤ T * H := by
    have hh : |u| ≤ |u + t| + |t| := by
      simpa only [add_sub_cancel_right] using abs_sub (u + t) t
    dsimp [T, H]
    nlinarith [mul_nonneg (abs_nonneg (u + t)) (abs_nonneg t)]
  have hheightpow : (1 + |u|) ^ n ≤ T ^ n * H ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hheight n
  have hMdiv : ‖mellin V.toFun (idealVerticalPoint 0 (u + t))‖ ≤ B / T ^ (n + 2) := by
    simpa only [B, T, annularErrorSeminorm, neg_zero,
      Real.rpow_neg (by positivity : 0 ≤ 1 + |u + t|), Real.rpow_natCast,
      div_eq_mul_inv] using smoothAnnular_mellin_vertical_decay V (n + 2) 0 (u + t)
  have hM : T ^ (n + 2) * ‖mellin V.toFun (idealVerticalPoint 0 (u + t))‖ ≤ B := by
    simpa only [mul_comm] using (le_div_iff₀ (pow_pos hT (n + 2))).mp hMdiv
  have hhecke : ‖heckeContinuation K χ (idealVerticalPoint 0 u)‖ ≤
      C * (T ^ n * H ^ n) := by
    have hh := hL (idealVerticalPoint 0 u) (by simp only [idealVerticalPoint_re])
    simp only [idealVerticalPoint_im] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hheightpow hC)
  have hnorm :
      ‖exceptionalHeckeContour K χ (phaseAnnularTest V t) X (idealVerticalPoint 0 u)‖ =
        ‖mellin V.toFun (idealVerticalPoint 0 (u + t))‖ *
          ‖heckeContinuation K χ (idealVerticalPoint 0 u)‖ := by
    rw [exceptionalHeckeContour, norm_mul, norm_mul, mellin_phaseAnnularTest_vertical,
      Complex.norm_cpow_eq_rpow_re_of_pos hX, idealVerticalPoint_re,
      Real.rpow_zero, mul_one]
  have hweighted :
      T ^ 2 * ‖exceptionalHeckeContour K χ (phaseAnnularTest V t) X
        (idealVerticalPoint 0 u)‖ ≤ B * C * H ^ n := by
    rw [hnorm]
    calc
      _ ≤ T ^ 2 * (‖mellin V.toFun (idealVerticalPoint 0 (u + t))‖ *
          (C * (T ^ n * H ^ n))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hhecke (norm_nonneg _)) (sq_nonneg T)
      _ = (T ^ (n + 2) * ‖mellin V.toFun (idealVerticalPoint 0 (u + t))‖) *
          C * H ^ n := by rw [pow_add]; ring
      _ ≤ B * C * H ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hC) (pow_nonneg hH n)
  have hdiv :
      ‖exceptionalHeckeContour K χ (phaseAnnularTest V t) X (idealVerticalPoint 0 u)‖ ≤
        (B * C * H ^ n) / T ^ 2 :=
    (le_div_iff₀ (pow_pos hT 2)).2 (by simpa only [mul_comm] using hweighted)
  simpa only [B, T, H, Real.rpow_neg (by positivity : 0 ≤ 1 + |u + t|),
    Real.rpow_ofNat, div_eq_mul_inv] using hdiv

/-- Integration of the translated envelope gives the actual annular
remainder, uniformly over all positive scales and all phases. -/
theorem annularHeckeSum_phase_error
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s : ℂ, s.re = 0 →
      ‖heckeContinuation K χ s‖ ≤ C * (1 + |s.im|) ^ n)
    (V : SmoothAnnularTest) (t : ℝ) {X : ℝ} (hX : 0 < X) :
    ‖annularIdealSum K (heckeIdealCoefficient K χ) (phaseAnnularTest V t) X -
      (X : ℂ) * actualExceptionalResidue K χ * mellin (phaseAnnularTest V t).toFun 1‖ ≤
        (2 ^ (n + 2) * C * annularContourMass) *
          annularErrorSeminorm V n * (1 + |t|) ^ n := by
  rw [annularHeckeSum_sub_residue K hcomplex χ hχ (phaseAnnularTest V t) hX, norm_mul]
  let A : ℝ := 2 ^ (n + 2) * annularErrorSeminorm V n * C * (1 + |t|) ^ n
  have hi : Integrable (fun u : ℝ => A * (1 + |u + t|) ^ (-(2 : ℝ))) :=
    ((integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).comp_add_right t).const_mul A
  have hb : ‖∫ u : ℝ, exceptionalHeckeContour K χ (phaseAnnularTest V t) X
      (idealVerticalPoint 0 u)‖ ≤ ∫ u : ℝ, A * (1 + |u + t|) ^ (-(2 : ℝ)) :=
    norm_integral_le_of_norm_le hi (Eventually.of_forall
      (exceptionalHeckeContour_phase_zero_bound K χ V hX n C hC hL t))
  have hv : (∫ u : ℝ, A * (1 + |u + t|) ^ (-(2 : ℝ))) =
      A * ∫ u : ℝ, (1 + |u|) ^ (-(2 : ℝ)) := by
    rw [integral_const_mul, integral_add_right_eq_self]
  rw [hv] at hb
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        (A * ∫ u : ℝ, (1 + |u|) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by dsimp [A, annularContourMass]; ring

theorem mellin_phaseAnnularTest_one (V : SmoothAnnularTest) (t : ℝ) :
    mellin (phaseAnnularTest V t).toFun 1 = exceptionalProfileIntegral V.toFun t := by
  simp only [mellin, sub_self, Complex.cpow_zero, one_smul, phaseAnnularTest_apply,
    exceptionalProfileIntegral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  ring

/-- Removing the zero ideal and extracting its literal norm phase yields
the finite annular polynomial used in the Mellin calculation. -/
theorem actualUnmaskedSum_phase_identity
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) (t : ℝ) {X : ℝ} (hX : 0 < X) :
    (∑' I : Ideal (𝓞 K), heckeExceptionalCharacter K χ I *
        (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * V.toFun ((Ideal.absNorm I : ℝ) / X)) =
      (X : ℂ) ^ (Complex.I * t) *
        annularIdealSum K (heckeIdealCoefficient K χ) (phaseAnnularTest V t) X := by
  let f : Ideal (𝓞 K) → ℂ := fun I => heckeExceptionalCharacter K χ I *
    (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * V.toFun ((Ideal.absNorm I : ℝ) / X)
  have hv : Function.Injective (fun I : NonzeroIdeal K => I.val) := Subtype.val_injective
  have hs : Function.support f ⊆ Set.range (fun I : NonzeroIdeal K => I.val) := by
    intro I hI
    have hI0 : I ≠ ⊥ := by
      intro he
      exact hI (by simp only [f, he, heckeExceptionalCharacter_zero, zero_mul])
    exact ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, rfl⟩
  rw [annularIdealSum_eq_tsum K _ _ hX, ← tsum_mul_left]
  calc
    _ = ∑' I : NonzeroIdeal K, f I.val := (hv.tsum_eq hs).symm
    _ = _ := by
      apply tsum_congr
      intro I
      have hphase : (idealNorm K I : ℂ) ^ (Complex.I * t) =
          (X : ℂ) ^ (Complex.I * t) *
            ((idealNorm K I / X : ℝ) : ℂ) ^ (Complex.I * t) := by
        have hh := Complex.mul_cpow_ofReal_nonneg hX.le
          (div_nonneg (idealNorm_pos K I).le hX.le) (Complex.I * t)
        rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hX.ne'] at hh
        exact hh
      simp only [f, heckeExceptionalCharacter_nonzero, phaseAnnularTest_apply,
        idealNorm, Complex.ofReal_natCast] at hphase ⊢
      rw [hphase]
      ring

/-- The residue in the principal branch is the actual Dedekind residue,
proved by the one-sided zeta limit and uniqueness of limits. -/
theorem normPoleNumerator_zero_one_eq :
    normPoleNumerator K 0 1 = (dedekindZeta_residue K : ℂ) := by
  have hlim : Tendsto (fun x : ℝ => normPoleNumerator K 0 (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (normPoleNumerator K 0 1)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      ((normPoleNumerator_differentiable K 0).continuous.tendsto 1).comp
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply tendsto_nhds_unique hlim
  apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  rw [normPoleNumerator_right K 0 (x : ℂ) hx']
  simp only [heckeNormTwist, normTwist_zero, heckeNormPole, Complex.ofReal_zero,
    zero_mul, add_zero]
  rw [heckeLSeries_trivial_eq_dedekindZeta K hx']

theorem actualExceptionalResidue_eq_poleCoefficient (χ : HeckeCharacter K) :
    actualExceptionalResidue K χ = heckeExceptionalPoleCoefficient K χ := by
  unfold actualExceptionalResidue heckeExceptionalPoleCoefficient
  rw [normPoleNumerator_zero_one_eq]

/-- The unmasked Lemma 4.11 estimate is produced from the actual analytic
continuation.  The order and constant precede every test, phase and scale;
there is no volume or error hypothesis. -/
theorem exists_actualUnmaskedExceptional_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ) :
    ∃ (n : ℕ) (D : ℝ), 0 < D ∧ ∀ (V : SmoothAnnularTest) (t X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 K), heckeExceptionalCharacter K χ I *
          (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
            V.toFun ((Ideal.absNorm I : ℝ) / X)) -
        volumeTerm (heckeExceptionalPoleCoefficient K χ)
          (exceptionalProfileIntegral V.toFun t) t X‖ ≤
        D * annularErrorSeminorm V n * (1 + |t|) ^ n := by
  obtain ⟨n, C, hC, hL, _⟩ :=
    exists_actualExceptionalContinuation_control K hcomplex χ hχ
  let D : ℝ := 2 ^ (n + 2) * C * annularContourMass
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (by positivity) hC.le) annularContourMass_nonneg
  refine ⟨n, 1 + D, by linarith, ?_⟩
  intro V t X hX
  have hmain : volumeTerm (heckeExceptionalPoleCoefficient K χ)
      (exceptionalProfileIntegral V.toFun t) t X =
      (X : ℂ) ^ (Complex.I * t) *
        ((X : ℂ) * actualExceptionalResidue K χ * mellin (phaseAnnularTest V t).toFun 1) := by
    rw [mellin_phaseAnnularTest_one, actualExceptionalResidue_eq_poleCoefficient,
      volumeTerm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'),
      Complex.cpow_one]
    ring
  rw [actualUnmaskedSum_phase_identity K χ V t hX, hmain, ← mul_sub, norm_mul,
    norm_real_imaginary_power X t hX, one_mul]
  calc
    _ ≤ D * annularErrorSeminorm V n * (1 + |t|) ^ n :=
      annularHeckeSum_phase_error K hcomplex χ hχ n C hC.le hL V t hX
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (annularErrorSeminorm_nonneg V n))
        (by positivity)

end HeckeSkeleton.Moments.MOM_PRIME
