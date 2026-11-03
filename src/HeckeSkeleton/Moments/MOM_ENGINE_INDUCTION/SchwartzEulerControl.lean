import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.ThetaKernel.TestMellin
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual Schwartz control supplies the annular Euler integral budget

The Euler operator is the genuine continuous complex-linear operator
on Schwartz space obtained by differentiation and multiplication by the
coordinate. Its iterates are identified with the repository's literal
`eulerDerivativeOrder`. Continuity gives finitely many original Schwartz
seminorms controlling each iterate pointwise. The fixed positive annulus
then bounds the exact weighted integral in `testSeminorm`.

All seminorm indices and constants precede the actual profile, height,
row and frequency. This proves the quantitative direction needed to
consume a normalized Schwartz profile in the ranked Euler profile class;
no source dictionary, mixed-row regularity or energy estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators ContDiff Topology NNReal

/-- The literal Euler operator on one real coordinate, as a continuous
complex-linear map on the actual Schwartz profile space. -/
def schwartzEulerCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ).flip
    (g := fun y : ℝ => (y : ℂ)) Complex.ofRealCLM.hasTemperateGrowth).comp
      (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem schwartzEulerCLM_apply (φ : SchwartzMap ℝ ℂ) (y : ℝ) :
    schwartzEulerCLM φ y = (y : ℂ) * deriv (φ : ℝ → ℂ) y := rfl

/-- Every finite iterate remains a genuine continuous operator. -/
def schwartzEulerIterCLM : ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ
  | 0 => ContinuousLinearMap.id ℂ _
  | j + 1 => schwartzEulerCLM.comp (schwartzEulerIterCLM j)

@[simp] theorem schwartzEulerIterCLM_coe (j : ℕ) (φ : SchwartzMap ℝ ℂ) :
    (schwartzEulerIterCLM j φ : ℝ → ℂ) = eulerDerivativeOrder j (φ : ℝ → ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      funext y
      change (y : ℂ) * deriv (schwartzEulerIterCLM j φ : ℝ → ℂ) y = _
      rw [ih, eulerDerivativeOrder_succ]

/-- A finite set of original complex Schwartz seminorms controls the
actual Euler iterate at every point, uniformly before the profile. -/
theorem exists_schwartzEuler_uniform_bound (j : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖eulerDerivativeOrder j (φ : ℝ → ℂ) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  let T := schwartzEulerIterCLM j
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℂ ℝ ℂ
  have hq : Continuous q := (hp.continuous_seminorm (0, 0)).comp T.continuous
  obtain ⟨s, C, _hC, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, (C : ℝ), C.coe_nonneg, ?_⟩
  intro φ y
  have hb := Seminorm.le_def.mp hbound φ
  change SchwartzMap.seminorm ℂ 0 0 (schwartzEulerIterCLM j φ) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ at hb
  rw [← schwartzEulerIterCLM_coe j φ]
  exact (SchwartzMap.norm_le_seminorm ℂ (schwartzEulerIterCLM j φ) y).trans hb

private theorem annular_integral_weight_bound (a b A : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ Icc a b,
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ B := by
  have hc : ContinuousOn (fun y : ℝ => (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y)
      (Icc a b) := by
    have hn : ∀ y ∈ Icc a b, y ≠ 0 := fun y hy => (lt_of_lt_of_le ha hy.1).ne'
    exact ((continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy))).add
      (continuousOn_id.rpow_const (fun y hy => Or.inl (hn y hy)))).div continuousOn_id hn
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image hc
  exact ⟨|M| + 1, by positivity, fun y hy =>
    (hM (Set.mem_image_of_mem _ hy)).trans (by linarith [le_abs_self M])⟩

private theorem complexSchwartzSeminorms_mono {s t : Finset (ℕ × ℕ)}
    (hst : s ⊆ t) (φ : SchwartzMap ℝ ℂ) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      t.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ φ)
    (fun i hi => Seminorm.le_finset_sup_apply (hst hi))

/-- Reverse quantitative compatibility on a fixed positive annulus.
The finite Schwartz set and coefficient are chosen before the profile;
the target Euler order and weight may be arbitrary prescribed values. -/
theorem exists_schwartz_annular_testSeminorm_bound (a b : ℝ) (ha : 0 < a)
    (J : ℕ) (A : ℝ) :
    ∃ s : Finset (ℕ × ℕ), ∃ D : ℝ, 0 < D ∧ ∀ φ : SchwartzMap ℝ ℂ,
      Function.support (φ : ℝ → ℂ) ⊆ Icc a b →
      testSeminorm (φ : ℝ → ℂ) J A ≤
        D * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  choose sets coefficients hcoefficients hbound using exists_schwartzEuler_uniform_bound
  let s := (Finset.range (J + 1)).biUnion sets
  let C := 1 + ∑ j ∈ Finset.range (J + 1), coefficients j
  have hsum : 0 ≤ ∑ j ∈ Finset.range (J + 1), coefficients j :=
    Finset.sum_nonneg (fun j _ => hcoefficients j)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hsubset (j : ℕ) (hj : j ≤ J) : sets j ⊆ s := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hp⟩
  have hcC (j : ℕ) (hj : j ≤ J) : coefficients j ≤ C := by
    have hs := Finset.single_le_sum (fun k _ => hcoefficients k)
      (Finset.mem_range.mpr (show j < J + 1 by omega))
    dsimp only [C]
    linarith
  obtain ⟨B, hB, hweight⟩ := annular_integral_weight_bound a b A ha
  let m : ℝ := volume.real (Icc a b)
  have hm : 0 ≤ m := measureReal_nonneg
  let D := C * B * (m + 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨s, D, hD, ?_⟩
  intro φ hsupport
  let P := s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  have hP : 0 ≤ P := apply_nonneg _ φ
  have hEuler (j : ℕ) (hj : j ≤ J) (y : ℝ) :
      ‖eulerDerivativeOrder j (φ : ℝ → ℂ) y‖ ≤ C * P :=
    (hbound j φ y).trans (mul_le_mul (hcC j hj)
      (complexSchwartzSeminorms_mono (hsubset j hj) φ) (apply_nonneg _ φ) hC.le)
  have hgood : Good a b (φ : ℝ → ℂ) :=
    ⟨ha, φ.smooth ⊤, fun y hy => Function.notMem_support.mp (fun hy' => hy (hsupport hy'))⟩
  apply testSeminorm_le_of_integrals _ _ _ _ (mul_nonneg hD.le hP)
  intro j hj
  let f : ℝ → ℝ := fun y => ‖eulerDerivativeOrder j (φ : ℝ → ℂ) y‖ *
    (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y
  have hz : ∀ y, y ∉ Icc a b → f y = 0 := by
    intro y hy
    have he := (hgood.eulerDerivativeOrder j).zero y hy
    simp only [f, he, norm_zero, zero_mul, zero_div]
  have hzeroOutsidePositive : ∀ y, y ∉ Ioi (0 : ℝ) → f y = 0 := by
    intro y hy
    apply hz y
    intro hmem
    exact hy (lt_of_lt_of_le ha hmem.1)
  have hIntegral : testIntegral (φ : ℝ → ℂ) j A = ∫ y in Icc a b, f y := by
    change (∫ y in Ioi (0 : ℝ), f y) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOutsidePositive,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hfbound : ∀ y ∈ Icc a b, ‖f y‖ ≤ (C * P) * B := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hw : 0 ≤ (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y := by positivity
    have hfn : 0 ≤ f y := by dsimp only [f]; positivity
    rw [Real.norm_of_nonneg hfn]
    change ‖eulerDerivativeOrder j (φ : ℝ → ℂ) y‖ *
      (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y ≤ _
    rw [mul_div_assoc]
    exact mul_le_mul (hEuler j hj y) (hweight y hy) hw (mul_nonneg hC.le hP)
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := f) (s := Icc a b) isCompact_Icc.measure_lt_top hfbound
  rw [hIntegral]
  calc
    _ ≤ ‖∫ y in Icc a b, f y‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (∫ y in Icc a b, f y)
    _ ≤ ((C * P) * B) * m := hi
    _ ≤ ((C * P) * B) * (m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hC.le hP) hB.le)
    _ = D * P := by dsimp only [D]; ring

/-- A real normalized Schwartz child supplies the desired Euler slice
control. Taking `B=1` exhibits the fixed coefficient that must be included
in the common ranked profile budget. -/
theorem exists_schwartz_sliceControl_bound (a b : ℝ) (ha : 0 < a)
    (J : ℕ) (A : ℝ) :
    ∃ s : Finset (ℕ × ℕ), ∃ D : ℝ, 0 < D ∧
      ∀ (φ : SchwartzMap ℝ ℂ) (B : ℝ),
      Function.support (φ : ℝ → ℂ) ⊆ Icc a b →
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B →
      SliceControl J A (D * B) 0 a b 0 (φ : ℝ → ℂ) := by
  obtain ⟨s, D, hD, hbound⟩ := exists_schwartz_annular_testSeminorm_bound a b ha J A
  refine ⟨s, D, hD, ?_⟩
  intro φ B hsupport hB
  refine ⟨φ.smooth ⊤, fun y hy => hsupport hy, ?_⟩
  have h := (hbound φ hsupport).trans (mul_le_mul_of_nonneg_left hB hD.le)
  simpa only [Real.rpow_zero, mul_one] using h

end HeckeSkeleton.Moments.EngineInduction
