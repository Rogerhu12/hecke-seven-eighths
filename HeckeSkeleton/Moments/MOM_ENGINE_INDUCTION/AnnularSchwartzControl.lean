import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileSupremum
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PowerWindowSeminorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The literal annular profile has uniform Schwartz control

On a fixed positive annulus, the Euler integral seminorm controls each
Euler derivative pointwise by the already proved fundamental theorem of
calculus.  In logarithmic coordinates those are ordinary derivatives.
The quantitative composition theorem, applied to the fixed logarithm
on the annulus, then bounds ordinary derivatives of the original test.

Thus every prescribed finite set of Schwartz seminorms is controlled by
one finite Euler integral seminorm, with the order and coefficient chosen
before the test, height or row.  The Schwartz function is literally the
original smooth compactly supported function.  No varying test-dependent
constant, source dictionary or completed moment estimate is an input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators ContDiff Topology

private theorem annular_compactSupport (V : SmoothAnnularTest) :
    HasCompactSupport V.toFun :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal V.support isClosed_Icc)

/-- The actual test, with no change to any of its values. -/
def annularSchwartz (V : SmoothAnnularTest) : SchwartzMap ℝ ℂ :=
  (annular_compactSupport V).toSchwartzMap V.smooth

@[simp] theorem annularSchwartz_apply (V : SmoothAnnularTest) (y : ℝ) :
    annularSchwartz V y = V.toFun y := rfl

private def annularEulerTest (V : SmoothAnnularTest) (i : ℕ) : SmoothAnnularTest where
  toFun := eulerDerivativeOrder i V.toFun
  smooth := (good_eul V i).smooth
  lower := V.lower
  upper := V.upper
  lower_pos := V.lower_pos
  upper_ge := V.upper_ge
  support := by
    intro y hy
    by_contra hn
    exact hy ((good_eul V i).zero y hn)

/-- One more genuine Euler integral gives a uniform pointwise bound for
each Euler derivative.  There is no independently assumed supremum. -/
theorem smoothAnnular_euler_norm_le_testSeminorm (V : SmoothAnnularTest)
    (i J : ℕ) (hJ : i + 1 ≤ J) (y : ℝ) :
    ‖eulerDerivativeOrder i V.toFun y‖ ≤ testSeminorm V.toFun J 0 := by
  let Vi := annularEulerTest V i
  have he : eulerDerivativeOrder 1 Vi.toFun = eulerDerivativeOrder (i + 1) V.toFun := by
    change eulerDerivativeOrder 1 (eulerDerivativeOrder i V.toFun) = _
    rw [eulerDerivativeOrder_succ V.toFun i]
    rfl
  have hIntegral : testIntegral Vi.toFun 1 0 = testIntegral V.toFun (i + 1) 0 := by
    simp only [testIntegral, he]
  have h := smoothAnnular_norm_le_testIntegral Vi y
  rw [hIntegral] at h
  exact h.trans (HeckeSkeleton.ThetaKernel.testIntegral_le_seminorm V (i + 1) J hJ 0)

private theorem annular_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

private theorem annular_iteratedDeriv_zero {a b : ℝ} (V : SmoothAnnularTest)
    (hsupport : Function.support V.toFun ⊆ Icc a b) (n : ℕ) {y : ℝ}
    (hy : y ∉ Icc a b) : iteratedDeriv n V.toFun y = 0 := by
  apply Function.notMem_support.mp
  intro hn
  exact hy ((closure_minimal hsupport isClosed_Icc)
    ((annular_iteratedDeriv_tsupport V.toFun n)
      (subset_tsupport (iteratedDeriv n V.toFun) hn)))

private theorem log_derivatives_on_annulus (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ y ∈ Icc a b, ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i Real.log (Ioi 0) y‖ ≤ D ^ i := by
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)
  have hcontinuous (i : ℕ) :
      ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ i Real.log (Ioi 0) y‖) (Icc a b) :=
    (hlog.continuousOn_iteratedFDerivWithin (by simp) isOpen_Ioi.uniqueDiffOn).norm.mono
      (fun _ hy => lt_of_lt_of_le ha hy.1)
  have hbounded (i : ℕ) : ∃ c : ℝ, ∀ y ∈ Icc a b,
      ‖iteratedFDerivWithin ℝ i Real.log (Ioi 0) y‖ ≤ c := by
    obtain ⟨c, hc⟩ := isCompact_Icc.bddAbove_image (hcontinuous i)
    exact ⟨c, fun y hy => hc (Set.mem_image_of_mem _ hy)⟩
  choose c hc using hbounded
  let D := 1 + ∑ i ∈ Finset.range (n + 1), max (c i) 0
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n + 1), max (c i) 0 :=
    Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro y hy i hi hin
  have hci : max (c i) 0 ≤ ∑ k ∈ Finset.range (n + 1), max (c k) 0 :=
    Finset.single_le_sum (fun k _ => le_max_right _ _)
      (Finset.mem_range.mpr (by omega))
  have hcD : c i ≤ D := by dsimp only [D]; linarith [le_max_left (c i) 0]
  exact (hc i y hy).trans (hcD.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))

/-- Ordinary derivatives of every test in one fixed positive annulus
are bounded by a fixed multiple of the original Euler integral norm.
The coefficient is selected before the test; the order is exactly n+1. -/
theorem exists_annular_iteratedDeriv_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ V : SmoothAnnularTest,
      Function.support V.toFun ⊆ Icc a b → ∀ y : ℝ,
      ‖iteratedDeriv n V.toFun y‖ ≤ D * testSeminorm V.toFun (n + 1) 0 := by
  obtain ⟨L, hL, hlogBound⟩ := log_derivatives_on_annulus a b ha n
  let D := (n.factorial : ℝ) * L ^ n
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hL) _)
  refine ⟨D, hD, ?_⟩
  intro V hsupport y
  by_cases hy : y ∈ Icc a b
  · have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    let g : ℝ → ℂ := fun x => V.toFun (Real.exp x)
    have hg : ContDiff ℝ ∞ g := V.smooth.comp Real.contDiff_exp
    have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
      Real.contDiffOn_log.mono (fun z hz => ne_of_gt hz)
    have hC (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDerivWithin ℝ i g Set.univ (Real.log y)‖ ≤
          testSeminorm V.toFun (n + 1) 0 := by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      change ‖iteratedDeriv i (fun x => V.toFun (Real.exp x)) (Real.log y)‖ ≤ _
      rw [← eulerDerivativeOrder_log_coordinate V i (Real.log y), Real.exp_log hy0]
      exact smoothAnnular_euler_norm_le_testSeminorm V i (n + 1) (by omega) y
    have hcomp := norm_iteratedFDerivWithin_comp_le
      (g := g) (f := Real.log) (n := n) (s := Ioi (0 : ℝ)) (t := Set.univ)
      (x := y) hg.contDiffOn hlog (by simp) uniqueDiffOn_univ isOpen_Ioi.uniqueDiffOn
      (fun _ _ => Set.mem_univ _) hy0 hC (hlogBound y hy)
    have he : Set.EqOn (g ∘ Real.log) V.toFun (Ioi (0 : ℝ)) := by
      intro z hz
      simp only [g, Function.comp_def, Real.exp_log hz]
    rw [iteratedFDerivWithin_congr he hy0 n,
      iteratedFDerivWithin_eq_iteratedFDeriv isOpen_Ioi.uniqueDiffOn
        (V.smooth.contDiffAt.of_le (by simp)) hy0,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hcomp
    apply hcomp.trans
    dsimp only [D]
    exact le_of_eq (by ring)
  · rw [annular_iteratedDeriv_zero V hsupport n hy, norm_zero]
    exact mul_nonneg hD (testSeminorm_nonneg V.toFun (n + 1) 0)

/-- A prescribed individual Schwartz seminorm is controlled uniformly
on the original annulus, with one extra Euler derivative. -/
theorem exists_annular_schwartz_seminorm_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (k n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ V : SmoothAnnularTest,
      Function.support V.toFun ⊆ Icc a b →
      SchwartzMap.seminorm ℂ k n (annularSchwartz V) ≤
        D * testSeminorm V.toFun (n + 1) 0 := by
  obtain ⟨C, hC, hderiv⟩ := exists_annular_iteratedDeriv_bound a b ha n
  have hb : 0 ≤ b := (ha.trans_le hab).le
  refine ⟨b ^ k * C, mul_nonneg (pow_nonneg hb _) hC, ?_⟩
  intro V hsupport
  have hM : 0 ≤ b ^ k * C * testSeminorm V.toFun (n + 1) 0 :=
    mul_nonneg (mul_nonneg (pow_nonneg hb _) hC) (testSeminorm_nonneg V.toFun (n + 1) 0)
  apply SchwartzMap.seminorm_le_bound' ℂ k n (annularSchwartz V) hM
  intro y
  change |y| ^ k * ‖iteratedDeriv n V.toFun y‖ ≤ _
  by_cases hy : y ∈ Icc a b
  · have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hw : |y| ^ k ≤ b ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (by simpa only [abs_of_pos hy0] using hy.2) k
    calc
      _ ≤ b ^ k * (C * testSeminorm V.toFun (n + 1) 0) :=
        mul_le_mul hw (hderiv V hsupport y) (norm_nonneg _) (pow_nonneg hb _)
      _ = _ := by ring
  · rw [annular_iteratedDeriv_zero V hsupport n hy, norm_zero, mul_zero]
    exact hM

/-- The exact finite Schwartz seminorm family requested by a kernel
producer has one common Euler order and coefficient. Both precede the
test and hence every moving row, scale, height and frequency. -/
theorem exists_annular_schwartz_finset_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (s : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ V : SmoothAnnularTest,
      Function.support V.toFun ⊆ Icc a b →
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (annularSchwartz V) ≤
        D * testSeminorm V.toFun J 0 := by
  choose coefficients hcoefficients hbound using fun p : ℕ × ℕ =>
    exists_annular_schwartz_seminorm_bound a b ha hab p.1 p.2
  let J := s.sup (fun p => p.2) + 1
  let D := 1 + ∑ p ∈ s, coefficients p
  have hsum : 0 ≤ ∑ p ∈ s, coefficients p :=
    Finset.sum_nonneg (fun p _ => hcoefficients p)
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨J, D, hD, ?_⟩
  intro V hsupport
  apply Seminorm.finset_sup_apply_le (mul_nonneg hD.le (testSeminorm_nonneg V.toFun J 0))
  intro p hp
  have horder : p.2 + 1 ≤ J :=
    Nat.succ_le_succ (Finset.le_sup (f := fun p : ℕ × ℕ => p.2) hp)
  have hc : coefficients p ≤ D := by
    have hs := Finset.single_le_sum (fun q _ => hcoefficients q) hp
    dsimp only [D]
    linarith
  apply (hbound p V hsupport).trans
  exact mul_le_mul hc (testSeminorm_mono_order V.toFun 0 horder)
    (testSeminorm_nonneg V.toFun (p.2 + 1) 0) hD.le

/-- Direct compatibility with the actual #10 slice control. The returned
Schwartz profile is pointwise the original function, and its coefficient
and height degree are charged explicitly rather than selected anew for
each moving profile. -/
theorem exists_sliceControl_schwartz_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (s : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ (f : ℝ → ℂ) (C H T : ℝ),
      SliceControl J 0 C H a b T f →
      ∃ F : SchwartzMap ℝ ℂ, (∀ y, F y = f y) ∧
        s.sup (schwartzSeminormFamily ℂ ℝ ℂ) F ≤ D * C * (1 + T) ^ H := by
  obtain ⟨J, D, hD, hbound⟩ := exists_annular_schwartz_finset_bound a b ha hab s
  refine ⟨J, D, hD, ?_⟩
  intro f C H T hprofile
  let V : SmoothAnnularTest := {
    toFun := f
    smooth := hprofile.1
    lower := a
    upper := b
    lower_pos := ha
    upper_ge := hab
    support := fun y hy => hprofile.2.1 y hy }
  refine ⟨annularSchwartz V, fun _ => rfl, ?_⟩
  apply (hbound V V.support).trans
  have h := mul_le_mul_of_nonneg_left hprofile.2.2 hD.le
  simpa only [mul_assoc] using h

end HeckeSkeleton.Moments.EngineInduction
