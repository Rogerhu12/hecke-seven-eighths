import HeckeSkeleton.HighBinSupport.BoundaryRectangle
import HeckeGeneral.Analysis.FixedBinPointwiseIntegration
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite three-line transport with every horizontal face retained

The elementary rectangle identity is applied to each genuine coordinate.
Compact continuity proves every use of Fubini and subtraction.  The
resulting three boundary terms are explicit integrals over horizontal
faces; no fixed vertical integral is assigned to a tail by definition.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.FiniteTripleContour

open Set MeasureTheory Complex
open scoped Classical Topology

def vertical (sigma t : ℝ) : ℂ := (sigma : ℂ) + (t : ℂ) * I

def heightBox (H : ℝ) : Set ℝ := Icc (-H) H

def boxIntegral (F : ℂ → ℂ → ℂ → ℂ) (H sigma nu zeta : ℝ) : ℂ :=
  ∫ ts in heightBox H, ∫ tw in heightBox H, ∫ tz in heightBox H,
    F (vertical sigma ts) (vertical nu tw) (vertical zeta tz)

def sweptTube (s0 s1 w0 w1 z0 z1 : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {v | v.1.re ∈ uIcc s0 s1 ∧ v.2.1.re ∈ uIcc w0 w1 ∧ v.2.2.re ∈ uIcc z0 z1}

theorem setIntegral_swap_of_continuous (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (H : ℝ) :
    (∫ x in heightBox H, ∫ y in heightBox H, f x y) =
      ∫ y in heightBox H, ∫ x in heightBox H, f x y := by
  have hi : Integrable (Function.uncurry f)
      ((volume.restrict (heightBox H)).prod (volume.restrict (heightBox H))) := by
    rw [Measure.prod_restrict]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact integral_integral_swap hi

theorem tripleIntegral_swap_first_two (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (H : ℝ) :
    (∫ x in heightBox H, ∫ y in heightBox H, ∫ z in heightBox H, f x y z) =
      ∫ y in heightBox H, ∫ x in heightBox H, ∫ z in heightBox H, f x y z := by
  apply setIntegral_swap_of_continuous
  apply continuous_parametric_integral_of_continuous (s := heightBox H) _ isCompact_Icc
  exact hf.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)))

theorem tripleIntegral_cycle (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) (H : ℝ) :
    (∫ x in heightBox H, ∫ y in heightBox H, ∫ z in heightBox H, f x y z) =
      ∫ y in heightBox H, ∫ z in heightBox H, ∫ x in heightBox H, f x y z := by
  rw [tripleIntegral_swap_first_two f hf H]
  apply integral_congr_ae
  filter_upwards [] with y
  apply setIntegral_swap_of_continuous
  exact hf.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1, y, p.2)))

theorem continuous_vertical_kernel_of_analytic
    (F : ℂ → ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ × ℂ))
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2) U)
    (sigma nu zeta : ℝ)
    (hmem : ∀ ts tw tz : ℝ, (vertical sigma ts, vertical nu tw, vertical zeta tz) ∈ U) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      F (vertical sigma p.1) (vertical nu p.2.1) (vertical zeta p.2.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hmap : Continuous (fun q : ℝ × ℝ × ℝ =>
      (vertical sigma q.1, vertical nu q.2.1, vertical zeta q.2.2)) := by
    unfold vertical
    fun_prop
  have hmapAt : ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      (vertical sigma q.1, vertical nu q.2.1, vertical zeta q.2.2)) p := hmap.continuousAt
  exact (hF _ (hmem p.1 p.2.1 p.2.2)).continuousAt.comp_of_eq hmapAt rfl

theorem continuous_vertical_kernel
    (F : ℂ → ℂ → ℂ → ℂ) (s0 s1 w0 w1 z0 z1 : ℝ)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (sweptTube s0 s1 w0 w1 z0 z1))
    (sigma nu zeta : ℝ) (hs : sigma ∈ uIcc s0 s1)
    (hw : nu ∈ uIcc w0 w1) (hz : zeta ∈ uIcc z0 z1) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      F (vertical sigma p.1) (vertical nu p.2.1) (vertical zeta p.2.2)) := by
  apply continuous_vertical_kernel_of_analytic F _ hF sigma nu zeta
  intro ts tw tz
  simpa only [sweptTube, Set.mem_setOf_eq, vertical, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero] using And.intro hs (And.intro hw hz)

/-- The rectangle theorem in the set-integral convention of rowContourBox. -/
theorem rectangle_setIntegral_identity (F : ℂ → ℂ) (l r H : ℝ) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-H) H)) :
    (∫ t in heightBox H, F (vertical r t)) -
      (∫ t in heightBox H, F (vertical l t)) =
      I * ((∫ x : ℝ in l..r, F (vertical x (-H))) -
        ∫ x : ℝ in l..r, F (vertical x H)) := by
  simpa only [heightBox, vertical, intervalIntegral.integral_of_le (by linarith : -H ≤ H),
    integral_Icc_eq_integral_Ioc, Complex.ofReal_neg] using
      HighBinBoundary.finite_rectangle_identity F l r H hF

def zFaces (F : ℂ → ℂ → ℂ → ℂ) (H sigma nu z0 z1 : ℝ) : ℂ :=
  ∫ ts in heightBox H, ∫ tw in heightBox H,
    I * ((∫ x : ℝ in z1..z0, F (vertical sigma ts) (vertical nu tw) (vertical x (-H))) -
      ∫ x : ℝ in z1..z0, F (vertical sigma ts) (vertical nu tw) (vertical x H))

def wFaces (F : ℂ → ℂ → ℂ → ℂ) (H sigma w0 w1 zeta : ℝ) : ℂ :=
  ∫ ts in heightBox H, ∫ tz in heightBox H,
    I * ((∫ x : ℝ in w1..w0, F (vertical sigma ts) (vertical x (-H)) (vertical zeta tz)) -
      ∫ x : ℝ in w1..w0, F (vertical sigma ts) (vertical x H) (vertical zeta tz))

def sFaces (F : ℂ → ℂ → ℂ → ℂ) (H s0 s1 nu zeta : ℝ) : ℂ :=
  ∫ tw in heightBox H, ∫ tz in heightBox H,
    I * ((∫ x : ℝ in s1..s0, F (vertical x (-H)) (vertical nu tw) (vertical zeta tz)) -
      ∫ x : ℝ in s1..s0, F (vertical x H) (vertical nu tw) (vertical zeta tz))

theorem integral_sub_integral_twice
    (f g : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f))
    (hg : Continuous (Function.uncurry g)) (H : ℝ) :
    (∫ x in heightBox H, ∫ y in heightBox H, f x y) -
      (∫ x in heightBox H, ∫ y in heightBox H, g x y) =
      ∫ x in heightBox H, ∫ y in heightBox H, f x y - g x y := by
  have hfc : Continuous (fun x => ∫ y in heightBox H, f x y) :=
    continuous_parametric_integral_of_continuous hf isCompact_Icc
  have hgc : Continuous (fun x => ∫ y in heightBox H, g x y) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  have hfi : Integrable (fun x : ℝ => ∫ y in heightBox H, f x y)
      (volume.restrict (heightBox H)) :=
    hfc.continuousOn.integrableOn_compact (show IsCompact (heightBox H) from isCompact_Icc)
  have hgi : Integrable (fun x : ℝ => ∫ y in heightBox H, g x y)
      (volume.restrict (heightBox H)) :=
    hgc.continuousOn.integrableOn_compact (show IsCompact (heightBox H) from isCompact_Icc)
  rw [← integral_sub hfi hgi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hfx : Integrable (fun y : ℝ => f x y) (volume.restrict (heightBox H)) :=
    (hf.comp (show Continuous (fun y : ℝ => (x, y)) by fun_prop)).continuousOn.integrableOn_compact
      (show IsCompact (heightBox H) from isCompact_Icc)
  have hgx : Integrable (fun y : ℝ => g x y) (volume.restrict (heightBox H)) :=
    (hg.comp (show Continuous (fun y : ℝ => (x, y)) by fun_prop)).continuousOn.integrableOn_compact
      (show IsCompact (heightBox H) from isCompact_Icc)
  exact (integral_sub hfx hgx).symm

/-- Moving the innermost z line keeps both genuine horizontal z faces. -/
theorem boxIntegral_sub_z
    (F : ℂ → ℂ → ℂ → ℂ) (H sigma nu z0 z1 : ℝ) (hH : 0 ≤ H)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (sweptTube sigma sigma nu nu z0 z1)) :
    boxIntegral F H sigma nu z0 - boxIntegral F H sigma nu z1 =
      zFaces F H sigma nu z0 z1 := by
  have hcont0 := continuous_vertical_kernel F sigma sigma nu nu z0 z1 hF
    sigma nu z0 (by simp) (by simp) (by simp)
  have hcont1 := continuous_vertical_kernel F sigma sigma nu nu z0 z1 hF
    sigma nu z1 (by simp) (by simp) (by simp)
  have hinner (zeta : ℝ) (hc : Continuous (fun p : ℝ × ℝ × ℝ =>
      F (vertical sigma p.1) (vertical nu p.2.1) (vertical zeta p.2.2))) :
      Continuous (fun p : ℝ × ℝ => ∫ tz in heightBox H,
        F (vertical sigma p.1) (vertical nu p.2) (vertical zeta tz)) := by
    apply continuous_parametric_integral_of_continuous (s := heightBox H) _ isCompact_Icc
    exact hc.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)))
  unfold boxIntegral
  rw [integral_sub_integral_twice
    (fun ts tw => ∫ tz in heightBox H, F (vertical sigma ts) (vertical nu tw) (vertical z0 tz))
    (fun ts tw => ∫ tz in heightBox H, F (vertical sigma ts) (vertical nu tw) (vertical z1 tz))
    (hinner z0 hcont0) (hinner z1 hcont1) H]
  unfold zFaces
  apply integral_congr_ae
  filter_upwards [] with ts
  apply integral_congr_ae
  filter_upwards [] with tw
  apply rectangle_setIntegral_identity _ z1 z0 H hH
  intro z hz
  have hmem : (vertical sigma ts, vertical nu tw, z) ∈ sweptTube sigma sigma nu nu z0 z1 := by
    have hzr : z.re ∈ uIcc z0 z1 := by
      rw [uIcc_comm]
      exact hz.1
    simpa [sweptTube, vertical] using hzr
  have hs : DifferentiableAt ℂ (fun _zz : ℂ => vertical sigma ts) z :=
    differentiableAt_const _
  have hw : DifferentiableAt ℂ (fun _zz : ℂ => vertical nu tw) z :=
    differentiableAt_const _
  have hzid : DifferentiableAt ℂ (fun zz : ℂ => zz) z := differentiableAt_id
  have hmap : DifferentiableAt ℂ
      (fun zz : ℂ => (vertical sigma ts, vertical nu tw, zz)) z := hs.prodMk (hw.prodMk hzid)
  exact ((hF _ hmem).differentiableAt.comp
    (f := fun zz : ℂ => (vertical sigma ts, vertical nu tw, zz)) z hmap).differentiableWithinAt

/-- The middle-coordinate move is a proved Fubini permutation followed
by the same finite rectangle theorem. -/
theorem boxIntegral_sub_w
    (F : ℂ → ℂ → ℂ → ℂ) (H sigma w0 w1 zeta : ℝ) (hH : 0 ≤ H)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (sweptTube sigma sigma w0 w1 zeta zeta)) :
    boxIntegral F H sigma w0 zeta - boxIntegral F H sigma w1 zeta =
      wFaces F H sigma w0 w1 zeta := by
  let G : ℂ → ℂ → ℂ → ℂ := fun s z w => F s w z
  have hG : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => G v.1 v.2.1 v.2.2)
      (sweptTube sigma sigma zeta zeta w0 w1) := by
    intro v hv
    have hv' : (v.1, v.2.2, v.2.1) ∈ sweptTube sigma sigma w0 w1 zeta zeta :=
      ⟨hv.1, hv.2.2, hv.2.1⟩
    have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
    have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
      analyticAt_fst.comp analyticAt_snd
    have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
      analyticAt_snd.comp analyticAt_snd
    exact (hF _ hv').comp_of_eq (hs.prod (hz.prod hw)) rfl
  have hswap (wline : ℝ) (hw : wline ∈ uIcc w0 w1) :
      boxIntegral F H sigma wline zeta = boxIntegral G H sigma zeta wline := by
    have hc := continuous_vertical_kernel F sigma sigma w0 w1 zeta zeta hF
      sigma wline zeta (by simp) hw (by simp)
    unfold boxIntegral
    apply integral_congr_ae
    filter_upwards [] with ts
    apply setIntegral_swap_of_continuous
    exact hc.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (ts, p.1, p.2)))
  rw [hswap w0 (by simp), hswap w1 (by simp)]
  exact boxIntegral_sub_z G H sigma zeta w0 w1 hH hG

/-- The outer-coordinate move uses two justified Fubini permutations. -/
theorem boxIntegral_sub_s
    (F : ℂ → ℂ → ℂ → ℂ) (H s0 s1 nu zeta : ℝ) (hH : 0 ≤ H)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (sweptTube s0 s1 nu nu zeta zeta)) :
    boxIntegral F H s0 nu zeta - boxIntegral F H s1 nu zeta =
      sFaces F H s0 s1 nu zeta := by
  let G : ℂ → ℂ → ℂ → ℂ := fun w z s => F s w z
  have hG : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => G v.1 v.2.1 v.2.2)
      (sweptTube nu nu zeta zeta s0 s1) := by
    intro v hv
    have hv' : (v.2.2, v.1, v.2.1) ∈ sweptTube s0 s1 nu nu zeta zeta :=
      ⟨hv.2.2, hv.1, hv.2.1⟩
    have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
    have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
      analyticAt_fst.comp analyticAt_snd
    have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
      analyticAt_snd.comp analyticAt_snd
    exact (hF _ hv').comp_of_eq (hz.prod (hs.prod hw)) rfl
  have hcycle (sline : ℝ) (hs : sline ∈ uIcc s0 s1) :
      boxIntegral F H sline nu zeta = boxIntegral G H nu zeta sline := by
    exact tripleIntegral_cycle
      (fun ts tw tz => F (vertical sline ts) (vertical nu tw) (vertical zeta tz))
      (continuous_vertical_kernel F s0 s1 nu nu zeta zeta hF
        sline nu zeta hs (by simp) (by simp)) H
  rw [hcycle s0 (by simp), hcycle s1 (by simp)]
  exact boxIntegral_sub_z G H nu zeta s0 s1 hH hG

/-- The full finite transport retains all six horizontal faces in three
explicit pairs. It does not replace any vertical integral by a tail. -/
theorem boxIntegral_sub_eq_faces
    (F : ℂ → ℂ → ℂ → ℂ) (H s0 s1 w0 w1 z0 z1 : ℝ) (hH : 0 ≤ H)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (sweptTube s0 s1 w0 w1 z0 z1)) :
    boxIntegral F H s0 w0 z0 - boxIntegral F H s1 w1 z1 =
      sFaces F H s0 s1 w0 z0 + wFaces F H s1 w0 w1 z0 + zFaces F H s1 w1 z0 z1 := by
  have hs := boxIntegral_sub_s F H s0 s1 w0 z0 hH (hF.mono (by
    intro v hv
    have hw : v.2.1.re = w0 := by simpa using hv.2.1
    have hz : v.2.2.re = z0 := by simpa using hv.2.2
    exact ⟨hv.1, by simp [hw], by simp [hz]⟩))
  have hw := boxIntegral_sub_w F H s1 w0 w1 z0 hH (hF.mono (by
    intro v hv
    have hs : v.1.re = s1 := by simpa using hv.1
    have hz : v.2.2.re = z0 := by simpa using hv.2.2
    exact ⟨by simp [hs], hv.2.1, by simp [hz]⟩))
  have hz := boxIntegral_sub_z F H s1 w1 z0 z1 hH (hF.mono (by
    intro v hv
    have hs : v.1.re = s1 := by simpa using hv.1
    have hw : v.2.1.re = w1 := by simpa using hv.2.1
    exact ⟨by simp [hs], by simp [hw], hv.2.2⟩))
  linear_combination hs + hw + hz

theorem norm_horizontal_pair_le (F : ℂ → ℂ) (l r H M : ℝ)
    (hminus : ∀ x ∈ uIcc l r, ‖F (vertical x (-H))‖ ≤ M)
    (hplus : ∀ x ∈ uIcc l r, ‖F (vertical x H)‖ ≤ M) :
    ‖I * ((∫ x : ℝ in l..r, F (vertical x (-H))) -
      ∫ x : ℝ in l..r, F (vertical x H))‖ ≤ 2 * M * |r - l| := by
  rw [norm_mul, norm_I, one_mul]
  have hm := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hminus x (uIoc_subset_uIcc hx))
  have hp := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun x hx => hplus x (uIoc_subset_uIcc hx))
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_double_setIntegral_le (f : ℝ → ℝ → ℂ) (H M : ℝ) (hH : 0 ≤ H)
    (hf : ∀ x ∈ heightBox H, ∀ y ∈ heightBox H, ‖f x y‖ ≤ M) :
    ‖∫ x in heightBox H, ∫ y in heightBox H, f x y‖ ≤ M * (2 * H) ^ 2 := by
  have hvol : volume.real (heightBox H) = 2 * H := by
    rw [heightBox, Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  have hfinite : (volume : Measure ℝ) (heightBox H) < ⊤ :=
    isCompact_Icc.measure_lt_top
  have hinner (x : ℝ) (hx : x ∈ heightBox H) :
      ‖∫ y in heightBox H, f x y‖ ≤ M * (2 * H) := by
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const
      (μ := (volume : Measure ℝ)) (s := heightBox H) hfinite (hf x hx)
  have houter := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) (s := heightBox H) hfinite hinner
  simpa only [hvol, pow_two, mul_assoc] using houter

theorem norm_zFaces_le (F : ℂ → ℂ → ℂ → ℂ) (H sigma nu z0 z1 M : ℝ) (hH : 0 ≤ H)
    (hminus : ∀ ts ∈ heightBox H, ∀ tw ∈ heightBox H, ∀ x ∈ uIcc z0 z1,
      ‖F (vertical sigma ts) (vertical nu tw) (vertical x (-H))‖ ≤ M)
    (hplus : ∀ ts ∈ heightBox H, ∀ tw ∈ heightBox H, ∀ x ∈ uIcc z0 z1,
      ‖F (vertical sigma ts) (vertical nu tw) (vertical x H)‖ ≤ M) :
    ‖zFaces F H sigma nu z0 z1‖ ≤ (2 * M * |z0 - z1|) * (2 * H) ^ 2 := by
  apply norm_double_setIntegral_le _ H _ hH
  intro ts hts tw htw
  apply norm_horizontal_pair_le
  · intro x hx
    exact hminus ts hts tw htw x (by simpa only [uIcc_comm] using hx)
  · intro x hx
    exact hplus ts hts tw htw x (by simpa only [uIcc_comm] using hx)

theorem norm_wFaces_le (F : ℂ → ℂ → ℂ → ℂ) (H sigma w0 w1 zeta M : ℝ) (hH : 0 ≤ H)
    (hminus : ∀ ts ∈ heightBox H, ∀ tz ∈ heightBox H, ∀ x ∈ uIcc w0 w1,
      ‖F (vertical sigma ts) (vertical x (-H)) (vertical zeta tz)‖ ≤ M)
    (hplus : ∀ ts ∈ heightBox H, ∀ tz ∈ heightBox H, ∀ x ∈ uIcc w0 w1,
      ‖F (vertical sigma ts) (vertical x H) (vertical zeta tz)‖ ≤ M) :
    ‖wFaces F H sigma w0 w1 zeta‖ ≤ (2 * M * |w0 - w1|) * (2 * H) ^ 2 :=
  norm_zFaces_le (fun s z w => F s w z) H sigma zeta w0 w1 M hH hminus hplus

theorem norm_sFaces_le (F : ℂ → ℂ → ℂ → ℂ) (H s0 s1 nu zeta M : ℝ) (hH : 0 ≤ H)
    (hminus : ∀ tw ∈ heightBox H, ∀ tz ∈ heightBox H, ∀ x ∈ uIcc s0 s1,
      ‖F (vertical x (-H)) (vertical nu tw) (vertical zeta tz)‖ ≤ M)
    (hplus : ∀ tw ∈ heightBox H, ∀ tz ∈ heightBox H, ∀ x ∈ uIcc s0 s1,
      ‖F (vertical x H) (vertical nu tw) (vertical zeta tz)‖ ≤ M) :
    ‖sFaces F H s0 s1 nu zeta‖ ≤ (2 * M * |s0 - s1|) * (2 * H) ^ 2 :=
  norm_zFaces_le (fun w z s => F s w z) H nu zeta s0 s1 M hH hminus hplus

end Expansion.FiniteTripleContour

#print axioms Expansion.FiniteTripleContour.boxIntegral_sub_eq_faces
#print axioms Expansion.FiniteTripleContour.norm_zFaces_le
