import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The actual Euler test seminorm is controlled by finite Schwartz orders

The project uses an Euler-derivative integral, whereas prime cancellation
and logarithmic Fourier inversion use Schwartz seminorms.  This file gives
the comparison on the same fixed annulus.  The orders and constants are
selected before the test, so the result applies to a whole moving family.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory Set
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ContDiff SchwartzMap

/-- The literal Euler operator as a continuous linear map on Schwartz space. -/
def profileEulerCLM : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ).flip
    (g := fun y : ℝ => (y : ℂ)) (by fun_prop)).comp (SchwartzMap.derivCLM ℝ ℂ)

@[simp] theorem profileEulerCLM_apply (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    profileEulerCLM f y = (y : ℂ) * deriv (f : ℝ → ℂ) y := rfl

def profileEulerIterCLM : ℕ → SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => profileEulerCLM.comp (profileEulerIterCLM j)

@[simp] theorem profileEulerIterCLM_apply (j : ℕ) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    profileEulerIterCLM j f y = eulerDerivativeOrder j (f : ℝ → ℂ) y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    have hfun : (profileEulerIterCLM j f : ℝ → ℂ) = eulerDerivativeOrder j (f : ℝ → ℂ) :=
      funext ih
    simp only [profileEulerIterCLM, ContinuousLinearMap.comp_apply,
      profileEulerCLM_apply, hfun, eulerDerivativeOrder, Function.iterate_succ_apply']
    rfl

theorem profileEulerCLM_support (f : SchwartzMap ℝ ℂ) :
    tsupport (profileEulerCLM f) ⊆ tsupport f := by
  change tsupport (fun y : ℝ => (y : ℂ) * deriv (f : ℝ → ℂ) y) ⊆ tsupport f
  exact tsupport_mul_subset_right.trans (SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℝ) f)

theorem profileEulerIterCLM_support (j : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport (profileEulerIterCLM j f) ⊆ tsupport f := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih => exact (profileEulerCLM_support _).trans ih

/-- All Euler orders up to J are bounded by one finite family of ordinary
Schwartz seminorms, chosen before the test. -/
theorem profileEuler_finite_order_control (J : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℂ) (j : ℕ), j ≤ J →
        SchwartzMap.seminorm ℝ 0 0 (profileEulerIterCLM j f) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) f := by
  let p (j : ℕ) : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (SchwartzMap.seminorm ℝ 0 0).comp (profileEulerIterCLM j).toLinearMap
  let q : Seminorm ℝ (SchwartzMap ℝ ℂ) := (Finset.range (J + 1)).sup p
  have hp (j : ℕ) : Continuous (p j) :=
    ((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
      (profileEulerIterCLM j).continuous
  have hq : Continuous q := Seminorm.continuous_finsetSup (fun j _ => hp j)
  obtain ⟨s, C, hC, hb⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  refine ⟨s, C, hCpos, ?_⟩
  intro f j hj
  have hjmem : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hjq : p j ≤ q := Finset.le_sup hjmem
  exact (Seminorm.le_def.mp hjq f).trans (Seminorm.le_def.mp hb f)

def annularEulerWeight (A y : ℝ) : ℝ := (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y

def annularEulerMass (a b A : ℝ) : ℝ :=
  ∫ y in Icc a b, annularEulerWeight A y

theorem annularEulerWeight_nonneg {A y : ℝ} (hy : 0 ≤ y) :
    0 ≤ annularEulerWeight A y := by unfold annularEulerWeight; positivity

theorem annularEulerWeight_continuousOn (a b A : ℝ) (ha : 0 < a) :
    ContinuousOn (annularEulerWeight A) (Icc a b) := by
  intro y hy
  have hypos : 0 < y := ha.trans_le hy.1
  exact (((Real.continuousAt_rpow_const y (1 / 4 : ℝ) (Or.inl hypos.ne')).add
    (Real.continuousAt_rpow_const y (-A) (Or.inl hypos.ne'))).div
      continuousAt_id hypos.ne').continuousWithinAt

theorem annularEulerMass_nonneg (a b A : ℝ) (ha : 0 < a) :
    0 ≤ annularEulerMass a b A :=
  setIntegral_nonneg measurableSet_Icc (fun y hy =>
    annularEulerWeight_nonneg (ha.le.trans hy.1))

/-- The concrete Euler integral, with its original positive-line weight,
is bounded by the zero-order seminorm of the Euler iterate. -/
theorem testIntegral_le_annular_euler (f : SchwartzMap ℝ ℂ) (a b A : ℝ)
    (ha : 0 < a) (hsupport : tsupport f ⊆ Icc a b) (j : ℕ) :
    testIntegral f j A ≤ annularEulerMass a b A *
      SchwartzMap.seminorm ℝ 0 0 (profileEulerIterCLM j f) := by
  let g := profileEulerIterCLM j f
  have hgs : tsupport g ⊆ Icc a b := (profileEulerIterCLM_support j f).trans hsupport
  have hzero (y : ℝ) (hy : y ∉ Icc a b) : g y = 0 := by
    apply Function.notMem_support.mp
    exact fun h => hy (hgs (subset_tsupport g h))
  have hweight := (annularEulerWeight_continuousOn a b A ha).integrableOn_Icc
  have hg : IntegrableOn (fun y : ℝ => ‖g y‖ * annularEulerWeight A y) (Icc a b) :=
    (g.continuous.norm.continuousOn.mul
      (annularEulerWeight_continuousOn a b A ha)).integrableOn_Icc
  have hrewrite : testIntegral f j A =
      ∫ y in Icc a b, ‖g y‖ * annularEulerWeight A y := by
    unfold testIntegral
    simp_rw [← profileEulerIterCLM_apply]
    change (∫ y in Ioi (0 : ℝ), ‖g y‖ * (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y) = _
    simp_rw [mul_div_assoc]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun y hy => ha.trans_le hy.1) (fun y hy => by simp [hzero y hy.2])
  rw [hrewrite, mul_comm (annularEulerMass a b A)]
  unfold annularEulerMass
  rw [← integral_const_mul]
  apply setIntegral_mono_on hg (hweight.const_mul _) measurableSet_Icc
  intro y hy
  apply mul_le_mul_of_nonneg_right _ (annularEulerWeight_nonneg (ha.le.trans hy.1))
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
    SchwartzMap.le_seminorm ℝ 0 0 g y

/-- The finite source seminorms and scalar precede the entire moving test
family.  This bridges the project's actual `testSeminorm` to the standard
Schwartz seminorms used by the Fourier and prime-cancellation modules. -/
theorem testSeminorm_finite_schwartz_control (a b A : ℝ) (ha : 0 < a) (J : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ f : SchwartzMap ℝ ℂ, tsupport f ⊆ Icc a b →
        testSeminorm f J A ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) f := by
  obtain ⟨s, C, hC, hb⟩ := profileEuler_finite_order_control J
  have hmass := annularEulerMass_nonneg a b A ha
  refine ⟨s, (annularEulerMass a b A + 1) * C, mul_pos (by linarith) hC, ?_⟩
  intro f hs
  have hsf : 0 ≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) f := by positivity
  apply testSeminorm_le_of_integrals _ J A _ (by positivity)
  intro j hj
  calc
    _ ≤ annularEulerMass a b A * SchwartzMap.seminorm ℝ 0 0 (profileEulerIterCLM j f) :=
      testIntegral_le_annular_euler f a b A ha hs j
    _ ≤ annularEulerMass a b A * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) f) :=
      mul_le_mul_of_nonneg_left (hb f j hj) hmass
    _ ≤ _ := by nlinarith

end HeckeSkeleton.Moments.UniformAmplify
