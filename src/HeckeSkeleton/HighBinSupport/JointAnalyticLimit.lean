import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Constructions
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
      ((((continuous_circleMap 0 R).mul continuous_const).mul
        (f.continuous.comp (continuous_circlePoint c R hR))).intervalIntegrable _ _)
      ((((continuous_circleMap 0 R).mul continuous_const).mul
        (g.continuous.comp (continuous_circlePoint c R hR))).intervalIntegrable _ _)
  map_smul' a f := by
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm, RingHom.id_apply] using
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
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
  change ‖∫ θ in 0..2 * Real.pi,
    (circleMap 0 R θ * I) * f (circlePoint c R hR θ)‖ ≤ _
  exact h.trans_eq (by ring)

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
  exact congrArg (fun z : ℂ => (circleMap 0 R θ * I) * z)
    (hfg (circlePoint c R hR θ))

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
      (((circleAverageCLM c.2.2 R hR).compLeftContinuous ℂ (Circle c.2.1 R)).comp
        (curryCLM (Circle c.2.1 R) (Circle c.2.2 R)))).compLeftContinuous ℂ
          (Circle c.1 R) |>.comp
            (curryCLM (Circle c.1 R) (Circle c.2.1 R × Circle c.2.2 R)))

private theorem inverse_apply {T : Type*} [TopologicalSpace T]
    (g : C(T, ℂ)) (hg : IsUnit g) (t : T) :
    Ring.inverse g t = (g t)⁻¹ := by
  rcases hg with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun f : C(T, ℂ) => f t) u.inv_val
  simpa only [ContinuousMap.mul_apply, ContinuousMap.one_apply, Units.inv_eq_val_inv] using h

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
  have ha : AnalyticAt ℂ (fun x : E => g - ContinuousMap.const T (ℓ x)) v :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : E => g) v).sub
      (((ContinuousLinearMap.const ℂ T).comp ℓ).analyticAt v)
  exact hinv.comp (f := fun x : E => g - ContinuousMap.const T (ℓ x)) (x := v) ha

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

private theorem tripleKernel_apply
    (c : ℂ × ℂ × ℂ) (R : ℝ)
    (B : C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ))
    (v : ℂ × ℂ × ℂ)
    (hv : v.1 ∈ ball c.1 R ∧ v.2.1 ∈ ball c.2.1 R ∧ v.2.2 ∈ ball c.2.2 R)
    (t : Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R) :
    tripleKernel c R B v t =
      ((t.1 : ℂ) - v.1)⁻¹ *
        (((t.2.1 : ℂ) - v.2.1)⁻¹ * (((t.2.2 : ℂ) - v.2.2)⁻¹ * B t)) := by
  have h₁ : IsUnit (circleCoordinate c R 0 - ContinuousMap.const _ v.1) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).2
    intro t
    simpa [circleCoordinate] using circle_sub_ne_zero t.1 hv.1
  have h₂ : IsUnit (circleCoordinate c R 1 - ContinuousMap.const _ v.2.1) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).2
    intro t
    simpa [circleCoordinate] using circle_sub_ne_zero t.2.1 hv.2.1
  have h₃ : IsUnit (circleCoordinate c R 2 - ContinuousMap.const _ v.2.2) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).2
    intro t
    simpa [circleCoordinate] using circle_sub_ne_zero t.2.2 hv.2.2
  simp only [tripleKernel, ContinuousMap.mul_apply,
    inverse_apply _ h₁, inverse_apply _ h₂, inverse_apply _ h₃]
  simp [circleCoordinate]

private theorem normalizedCauchy
    {c v : ℂ} {R : ℝ} (f : ℂ → ℂ)
    (hd : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hv : v ∈ ball c R) :
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(c, R), (z - v)⁻¹ * f z) = f v := by
  simpa only [smul_eq_mul] using
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) countable_empty hv
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz => hd z (ball_subset_closedBall hz.1))

private theorem circleAverageCLM_cauchy
    {c v : ℂ} {R : ℝ} (hR : 0 ≤ R) (H : C(Circle c R, ℂ))
    (f : ℂ → ℂ) (a : ℂ)
    (hH : ∀ t : Circle c R, H t = a * (((t : ℂ) - v)⁻¹ * f t))
    (hd : ∀ z ∈ closedBall c R, DifferentiableAt ℂ f z)
    (hv : v ∈ ball c R) :
    circleAverageCLM c R hR H = a * f v := by
  rw [circleAverageCLM_eq_integral c R hR H
    (fun z => a * ((z - v)⁻¹ * f z)) hH,
    circleIntegral.integral_const_mul]
  calc
    _ = a * ((2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(c, R), (z - v)⁻¹ * f z)) := by ring
    _ = a * f v := by rw [normalizedCauchy f hd hv]

private def closedPolydisc (c : ℂ × ℂ × ℂ) (R : ℝ) : Set (ℂ × ℂ × ℂ) :=
  closedBall c.1 R ×ˢ closedBall c.2.1 R ×ˢ closedBall c.2.2 R

private theorem tripleAverageCLM_cauchy
    (c : ℂ × ℂ × ℂ) (R : ℝ) (hR : 0 ≤ R)
    (H : C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ))
    (f : (ℂ × ℂ × ℂ) → ℂ) (v : ℂ × ℂ × ℂ)
    (hH : ∀ t, H t = ((t.1 : ℂ) - v.1)⁻¹ *
      (((t.2.1 : ℂ) - v.2.1)⁻¹ *
        (((t.2.2 : ℂ) - v.2.2)⁻¹ * f (t.1, t.2.1, t.2.2))))
    (hd : ∀ x ∈ closedPolydisc c R,
      DifferentiableAt ℂ (fun s => f (s, x.2.1, x.2.2)) x.1 ∧
      DifferentiableAt ℂ (fun w => f (x.1, w, x.2.2)) x.2.1 ∧
      DifferentiableAt ℂ (fun z => f (x.1, x.2.1, z)) x.2.2)
    (hv : v.1 ∈ ball c.1 R ∧ v.2.1 ∈ ball c.2.1 R ∧ v.2.2 ∈ ball c.2.2 R) :
    tripleAverageCLM c R hR H = f v := by
  have inner (a : Circle c.1 R) (b : Circle c.2.1 R) :
      circleAverageCLM c.2.2 R hR ((H.curry a).curry b) =
        ((a : ℂ) - v.1)⁻¹ * (((b : ℂ) - v.2.1)⁻¹ * f (a, b, v.2.2)) := by
    have h := circleAverageCLM_cauchy hR ((H.curry a).curry b)
      (fun z => f (a, b, z))
      (((a : ℂ) - v.1)⁻¹ * ((b : ℂ) - v.2.1)⁻¹)
      (fun t => by
        change H (a, b, t) = _
        rw [hH]
        ring)
      (fun z hz => (hd (a, b, z)
        ⟨sphere_subset_closedBall a.property, sphere_subset_closedBall b.property, hz⟩).2.2)
      hv.2.2
    simpa only [mul_assoc] using h
  let D : C(Circle c.1 R, ℂ) :=
    (((circleAverageCLM c.2.1 R hR).comp
      (((circleAverageCLM c.2.2 R hR).compLeftContinuous ℂ (Circle c.2.1 R)).comp
        (curryCLM (Circle c.2.1 R) (Circle c.2.2 R)))).compLeftContinuous ℂ
          (Circle c.1 R)) H.curry
  have middle (a : Circle c.1 R) :
      D a = ((a : ℂ) - v.1)⁻¹ * f (a, v.2.1, v.2.2) := by
    change circleAverageCLM c.2.1 R hR
      (((circleAverageCLM c.2.2 R hR).compLeftContinuous ℂ (Circle c.2.1 R))
        (H.curry a).curry) = _
    exact circleAverageCLM_cauchy hR _
      (fun w => f (a, w, v.2.2)) (((a : ℂ) - v.1)⁻¹)
      (fun b => inner a b)
      (fun w hw => (hd (a, w, v.2.2)
        ⟨sphere_subset_closedBall a.property, hw, ball_subset_closedBall hv.2.2⟩).2.1)
      hv.2.1
  change circleAverageCLM c.1 R hR D = _
  simpa only [one_mul] using circleAverageCLM_cauchy hR D
    (fun s => f (s, v.2.1, v.2.2)) 1
    (fun a => by simpa only [one_mul] using middle a)
    (fun s hs => (hd (s, v.2.1, v.2.2)
      ⟨hs, ball_subset_closedBall hv.2.1, ball_subset_closedBall hv.2.2⟩).1)
    hv.1

private theorem analyticAt_of_continuousOn_polydisc
    (f : (ℂ × ℂ × ℂ) → ℂ) (c : ℂ × ℂ × ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ContinuousOn f (closedPolydisc c R))
    (hd : ∀ x ∈ closedPolydisc c R,
      DifferentiableAt ℂ (fun s => f (s, x.2.1, x.2.2)) x.1 ∧
      DifferentiableAt ℂ (fun w => f (x.1, w, x.2.2)) x.2.1 ∧
      DifferentiableAt ℂ (fun z => f (x.1, x.2.1, z)) x.2.2) :
    AnalyticAt ℂ f c := by
  let B : C(Circle c.1 R × Circle c.2.1 R × Circle c.2.2 R, ℂ) :=
    ⟨fun t => f (t.1, t.2.1, t.2.2),
      hc.comp_continuous (by fun_prop) (fun t =>
        ⟨sphere_subset_closedBall t.1.property,
          sphere_subset_closedBall t.2.1.property,
          sphere_subset_closedBall t.2.2.property⟩)⟩
  have hk := tripleKernel_analyticAt c R B c
    ⟨mem_ball_self hR, mem_ball_self hR, mem_ball_self hR⟩
  have ha := (tripleAverageCLM c R hR.le).analyticAt (tripleKernel c R B c) |>.comp hk
  apply ha.congr
  filter_upwards [ball_mem_nhds c hR] with v hv
  have hv' : v.1 ∈ ball c.1 R ∧ v.2.1 ∈ ball c.2.1 R ∧ v.2.2 ∈ ball c.2.2 R := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hv
  exact tripleAverageCLM_cauchy c R hR.le (tripleKernel c R B v) f v
    (fun t => tripleKernel_apply c R B v hv' t) hd hv'

/-- A continuous function of three complex variables which is holomorphic
in each coordinate on an open set is jointly analytic there. -/
theorem analyticOnNhd_of_continuousOn_of_coordinate_differentiable
    {U : Set (ℂ × ℂ × ℂ)} {f : (ℂ × ℂ × ℂ) → ℂ}
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀ x ∈ U,
      DifferentiableAt ℂ (fun s => f (s, x.2.1, x.2.2)) x.1 ∧
      DifferentiableAt ℂ (fun w => f (x.1, w, x.2.2)) x.2.1 ∧
      DifferentiableAt ℂ (fun z => f (x.1, x.2.1, z)) x.2.2) :
    AnalyticOnNhd ℂ f U := by
  intro c hcU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU c hcU
  have hR : 0 < r / 2 := by positivity
  have hsub : closedPolydisc c (r / 2) ⊆ U := by
    intro v hv
    apply hrU
    rcases hv with ⟨hs, hw, hz⟩
    simp only [Metric.mem_closedBall] at hs hw hz
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  exact analyticAt_of_continuousOn_polydisc f c (r / 2) hR
    (hc.mono hsub) (fun x hx => hd x (hsub hx))

private theorem limit_comp_differentiableAt
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set (ℂ × ℂ × ℂ)} {F : ι → (ℂ × ℂ × ℂ) → ℂ}
    {f : (ℂ × ℂ × ℂ) → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U) (hU : IsOpen U)
    (g : ℂ → ℂ × ℂ × ℂ) (hg : Differentiable ℂ g)
    (v : ℂ) (hv : g v ∈ U) :
    DifferentiableAt ℂ (f ∘ g) v := by
  have hV : IsOpen (g ⁻¹' U) := hU.preimage hg.continuous
  have hlim' : TendstoLocallyUniformlyOn (fun i => F i ∘ g) (f ∘ g) l (g ⁻¹' U) :=
    hlim.comp g (fun _ hx => hx) hg.continuous.continuousOn
  have hF' : ∀ᶠ i in l, DifferentiableOn ℂ (F i ∘ g) (g ⁻¹' U) := by
    filter_upwards [hF] with i hi
    intro x hx
    exact ((hi (g x) hx).differentiableAt.comp x (hg x)).differentiableWithinAt
  exact (hlim'.differentiableOn hF' hV).differentiableAt (hV.mem_nhds hv)

/-- A locally uniform limit of jointly analytic functions of three complex
variables is jointly analytic on the same open set. The limit is allowed
to vanish, so this also applies to Euler products with finite zero factors. -/
theorem analyticOnNhd_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set (ℂ × ℂ × ℂ)} {F : ι → (ℂ × ℂ × ℂ) → ℂ}
    {f : (ℂ × ℂ × ℂ) → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_of_continuousOn_of_coordinate_differentiable hU
    (hlim.continuousOn (hF.mono fun _ hi => hi.continuousOn).frequently) ?_
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_def] using limit_comp_differentiableAt hlim hF hU
      (fun s => (s, x.2.1, x.2.2)) (by fun_prop) x.1 hx
  · simpa only [Function.comp_def] using limit_comp_differentiableAt hlim hF hU
      (fun w => (x.1, w, x.2.2)) (by fun_prop) x.2.1 hx
  · simpa only [Function.comp_def] using limit_comp_differentiableAt hlim hF hU
      (fun z => (x.1, x.2.1, z)) (by fun_prop) x.2.2 hx

#print axioms analyticOnNhd_of_continuousOn_of_coordinate_differentiable
#print axioms analyticOnNhd_of_tendstoLocallyUniformlyOn

end HeckeSkeleton.HighBinJointAnalytic
