import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units

/-!
# Joint analyticity from three coordinate slices

The Cauchy kernel is viewed in the Banach algebra of continuous functions
on a product of three circles. Inversion in that algebra is analytic, and
the iterated circle integral is continuous linear. This gives joint
analyticity without replacing it by separate differentiability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinJointAnalytic

open Complex Metric Set Filter
open scoped Topology Real Ring

private abbrev Circle (c : ℂ) (R : ℝ) := sphere c R

private def circlePoint (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (θ : ℝ) : Circle c R :=
  ⟨circleMap c R θ, circleMap_mem_sphere c hR θ⟩

private theorem continuous_circlePoint (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    Continuous (circlePoint c R hR) :=
  (continuous_circleMap c R).subtype_mk _

private def circleIntegralLinear (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    C(Circle c R, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ θ in 0..2 * Real.pi,
    (circleMap 0 R θ * I) * f (circlePoint c R hR θ)
  map_add' f g := by
    change (∫ θ in 0..2 * Real.pi, (circleMap 0 R θ * I) *
      (f (circlePoint c R hR θ) + g (circlePoint c R hR θ))) = _
    simp_rw [mul_add]
    exact intervalIntegral.integral_add
      (((continuous_circleMap 0 R).mul continuous_const).mul
        (f.continuous.comp (continuous_circlePoint c R hR))).intervalIntegrable _ _
      (((continuous_circleMap 0 R).mul continuous_const).mul
        (g.continuous.comp (continuous_circlePoint c R hR))).intervalIntegrable _ _
  map_smul' a f := by
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm] using
      (intervalIntegral.integral_const_mul a
        (fun θ => (circleMap 0 R θ * I) * f (circlePoint c R hR θ)))

private theorem circleIntegralLinear_bound (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (f : C(Circle c R, ℂ)) :
    ‖circleIntegralLinear c R hR f‖ ≤ (|R| * (2 * Real.pi)) * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := |R| * ‖f‖)
    (f := fun θ => (circleMap 0 R θ * I) * f (circlePoint c R hR θ))
    (fun θ _ => by
      simp only [norm_mul, norm_circleMap_zero, norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg R))
  simpa only [circleIntegralLinear, LinearMap.coe_mk, AddHom.coe_mk,
    sub_zero, abs_of_pos Real.two_pi_pos, mul_assoc, mul_comm, mul_left_comm] using h

private def circleAverageCLM (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    C(Circle c R, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    (circleIntegralLinear c R hR).mkContinuous (|R| * (2 * Real.pi))
      (circleIntegralLinear_bound c R hR)

private theorem circleAverageCLM_eq_integral
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (f : C(Circle c R, ℂ))
    (g : ℂ → ℂ) (hfg : ∀ t : Circle c R, f t = g t) :
    circleAverageCLM c R hR f =
      (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), g z := by
  change (2 * Real.pi * I : ℂ)⁻¹ *
    (∫ θ in 0..2 * Real.pi,
      (circleMap 0 R θ * I) * f (circlePoint c R hR θ)) = _
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hfg]
  rfl

private def curryCLM (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace (X × Y)] : C(X × Y, ℂ) →L[ℂ] C(X, C(Y, ℂ)) where
  toFun := ContinuousMap.curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_curry

private def tripleAverageCLM (c : ℂ × ℂ × ℂ) (R : ℝ) (hR : 0 ≤ R) :
    C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ) →L[ℂ] ℂ :=
  (circleAverageCLM c.1 R hR).comp
    (((circleAverageCLM c.2.1 R hR).comp
      (((circleAverageCLM c.2.2 R hR).compLeftContinuous (Circle c.2.1 R)).comp
        (curryCLM (Circle c.2.1 R) (Circle c.2.2 R)))).compLeftContinuous
          (Circle c.1 R) |>.comp
            (curryCLM (Circle c.1 R) (Circle c.2.1 R × Circle c.2.2 R)))

private theorem inverse_apply {T : Type*} [TopologicalSpace T]
    (g : C(T, ℂ)) (hg : IsUnit g) (t : T) :
    Ring.inverse g t = (g t)⁻¹ := by
  rcases hg with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun f : C(T, ℂ) => f t) u.inv_val
  simpa only [ContinuousMap.mul_apply, ContinuousMap.one_apply] using h

private theorem analyticAt_inverse_const_sub
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : C(T, ℂ)) (ℓ : E →L[ℂ] ℂ) (v : E)
    (h : ∀ t, g t - ℓ v ≠ 0) :
    AnalyticAt ℂ (fun x => Ring.inverse (g - ContinuousMap.const T (ℓ x))) v := by
  have hu : IsUnit (g - ContinuousMap.const T (ℓ v)) :=
    (ContinuousMap.isUnit_iff_forall_ne_zero _).2 h
  have hinv := analyticAt_inverse (𝕜 := ℂ) hu.unit
  rw [hu.unit_spec] at hinv
  exact hinv.comp (analyticAt_const.sub
    (((ContinuousLinearMap.const ℂ T).comp ℓ).analyticAt))

private theorem circle_sub_ne_zero {c v : ℂ} {R : ℝ}
    (t : Circle c R) (hv : v ∈ ball c R) : (t : ℂ) - v ≠ 0 := by
  intro h
  have ht := t.property
  rw [Metric.mem_sphere, sub_eq_zero.mp h] at ht
  exact (ne_of_lt (Metric.mem_ball.mp hv)) ht

private def circleCoordinate (c : ℂ × ℂ × ℂ) (R : ℝ) (i : Fin 3) :
    C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ) :=
  if i = 0 then ⟨fun t => t.1.val, by fun_prop⟩
  else if i = 1 then ⟨fun t => t.2.1.val, by fun_prop⟩
  else ⟨fun t => t.2.2.val, by fun_prop⟩

private def tripleKernel (c : ℂ × ℂ × ℂ) (R : ℝ)
    (B : C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ))
    (v : ℂ × ℂ × ℂ) :
    C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ) :=
  Ring.inverse (circleCoordinate c R 0 - ContinuousMap.const _ v.1) *
    (Ring.inverse (circleCoordinate c R 1 - ContinuousMap.const _ v.2.1) *
      (Ring.inverse (circleCoordinate c R 2 - ContinuousMap.const _ v.2.2) * B))

private theorem tripleKernel_analyticAt
    (c : ℂ × ℂ × ℂ) (R : ℝ)
    (B : C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ))
    (v : ℂ × ℂ × ℂ)
    (hv : v.1 ∈ ball c.1 R ∧ v.2.1 ∈ ball c.2.1 R ∧ v.2.2 ∈ ball c.2.2 R) :
    AnalyticAt ℂ (tripleKernel c R B) v := by
  let ℓ₁ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)
  let ℓ₂ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  let ℓ₃ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  have h₁ := analyticAt_inverse_const_sub (circleCoordinate c R 0) ℓ₁ v
    (fun t => by simpa [circleCoordinate, ℓ₁] using circle_sub_ne_zero t.1 hv.1)
  have h₂ := analyticAt_inverse_const_sub (circleCoordinate c R 1) ℓ₂ v
    (fun t => by simpa [circleCoordinate, ℓ₂] using circle_sub_ne_zero t.2.1 hv.2.1)
  have h₃ := analyticAt_inverse_const_sub (circleCoordinate c R 2) ℓ₃ v
    (fun t => by simpa [circleCoordinate, ℓ₃] using circle_sub_ne_zero t.2.2 hv.2.2)
  exact h₁.mul (h₂.mul (h₃.mul analyticAt_const))

end HeckeSkeleton.HighBinJointAnalytic
