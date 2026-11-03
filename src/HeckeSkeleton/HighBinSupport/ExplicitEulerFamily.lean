import HeckeSkeleton.HighBinSupport.ExceptionalSweptTube
import HeckeSkeleton.HighBinSupport.EulerProductBounds
import Mathlib.Topology.UniformSpace.UniformApproximation
/-!
# Normal convergence of the explicit marked and ramified Euler family

The local definition includes all four cases: regular/ramified and
unmarked/marked.  The prime-power Fourier identification in a number field
remains a separate arithmetic theorem; no such identity is assumed here.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open Set Filter
open scoped BigOperators Topology

def unmarkedZeroPart (q : ℝ) (cW cD : ℂ) (s w z : ℂ) : ℂ :=
  (1 - cW * (q : ℂ) ^ (-w) * (q : ℂ) ^ (-6 * z)) /
    (1 - cD * (q : ℂ) ^ (-s))

/-- R is the finite support of the row, Q the finite set of whole-index
marks.  Values at zeros of Gauss polynomials are retained literally. -/
def explicitLocalEuler {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) (i : ι) (v : ℂ × ℂ × ℂ) : ℂ :=
  if i ∈ R then
    ramifiedTableValue (P i) (q i) v.1 v.2.1 v.2.2 (j i) -
      (if i ∈ Q then 1 else 0)
  else
    phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2 -
      (if i ∈ Q then unmarkedZeroPart (q i) (cW i) (cD i) v.1 v.2.1 v.2.2 else 0)

theorem unmarkedZeroPart_analyticOnNhd {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (cW cD : ℂ) (hD : ‖cD‖ ≤ 1) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => unmarkedZeroPart q cW cD v.1 v.2.1 v.2.2)
      (sweptTube a e) := by
  intro v hv
  have hq0 : 0 < q := by linarith
  have hs : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hW : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => (q : ℂ) ^ (-v.2.1)) v :=
    analyticAt_realBase_cpow hq0 hw.neg
  have hD' : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => (q : ℂ) ^ (-v.1)) v :=
    analyticAt_realBase_cpow hq0 hs.neg
  have hV : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => (q : ℂ) ^ (-6 * v.2.2)) v :=
    analyticAt_realBase_cpow hq0 (analyticAt_const.mul hz)
  have hn := (phaseRowEuler_denominators_ne_zero hq ha he cD 0 v.1 v.2.2
    hD (by simp) hv.1.le hv.2.2.le).1
  exact (analyticAt_const.sub ((analyticAt_const.mul hW).mul hV)).div
    (analyticAt_const.sub (analyticAt_const.mul hD')) hn

theorem explicitLocalEuler_analyticOnNhd {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (he : 0 ≤ e)
    (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1) (i : ι) :
    AnalyticOnNhd ℂ (explicitLocalEuler R Q q cW cD cE P j i) (sweptTube a e) := by
  by_cases hR : i ∈ R
  · have h := ramifiedTable_analyticOnNhd (a := a) (e := e) (P i) (hq i)
      (by linarith) he (j i)
    have hfun : explicitLocalEuler R Q q cW cD cE P j i =
        (fun v : ℂ × ℂ × ℂ => ramifiedTableValue (P i) (q i) v.1 v.2.1 v.2.2 (j i) -
          (if i ∈ Q then 1 else 0)) := by
      funext v
      simp only [explicitLocalEuler, if_pos hR]
    rw [hfun]
    intro v hv
    exact (h v hv).sub analyticAt_const
  · have h := phaseRowEuler_analyticOnNhd (hq i) ha he (cW i) (cD i) (cE i) (hD i) (hE i)
    by_cases hQ : i ∈ Q
    · have hz := unmarkedZeroPart_analyticOnNhd (hq i) ha he (cW i) (cD i) (hD i)
      have hfun : explicitLocalEuler R Q q cW cD cE P j i =
          (fun v : ℂ × ℂ × ℂ => phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2 -
            unmarkedZeroPart (q i) (cW i) (cD i) v.1 v.2.1 v.2.2) := by
        funext v
        simp only [explicitLocalEuler, if_neg hR, if_pos hQ]
      rw [hfun]
      intro v hv
      exact (h v hv).sub (hz v hv)
    · have hfun : explicitLocalEuler R Q q cW cD cE P j i =
          (fun v : ℂ × ℂ × ℂ => phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2) := by
        funext v
        simp only [explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero]
      rw [hfun]
      exact h

/-- Actual normal convergence for the explicit four-case local family.
The exceptional factors require no lower bound and may be zero. -/
theorem explicitEuler_hasProdLocallyUniformlyOn {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e))) :
    HasProdLocallyUniformlyOn (explicitLocalEuler R Q q cW cD cE P j)
      (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v) (sweptTube a e) := by
  have hb : Summable (fun i => (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e)) :=
    hsum.mul_left _
  have hevent : ∀ᶠ i in cofinite, ∀ v ∈ sweptTube a e,
      ‖explicitLocalEuler R Q q cW cD cE P j i v - 1‖ ≤
        (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e) := by
    filter_upwards [(R ∪ Q).eventually_cofinite_notMem] with i hi v hv
    have hR : i ∉ R := fun h => hi (Finset.mem_union_left Q h)
    have hQ : i ∉ Q := fun h => hi (Finset.mem_union_right R h)
    simpa only [explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero] using
      phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv
  have h := Summable.hasProdLocallyUniformlyOn_one_add (sweptTube_isOpen a e) hb hevent
    (fun i => (explicitLocalEuler_analyticOnNhd R Q q cW cD cE P j hq ha he hD hE i).continuousOn.sub
      continuousOn_const)
  have hone (x : ℂ) : 1 + (x - 1) = x := by ring
  simpa only [hone] using h

#print axioms explicitLocalEuler_analyticOnNhd
#print axioms explicitEuler_hasProdLocallyUniformlyOn

/-- Joint continuity is a consequence of normal convergence and the
explicit local formula, including at zeros of individual factors. -/
theorem explicitEuler_continuousOn {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e))) :
    ContinuousOn (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v)
      (sweptTube a e) := by
  have h := explicitEuler_hasProdLocallyUniformlyOn R Q q cW cD cE P j
    hq ha ha' he he' hW hD hE hsum
  apply TendstoLocallyUniformlyOn.continuousOn h
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun F =>
    (F.analyticOnNhd_fun_prod (fun i _ =>
      explicitLocalEuler_analyticOnNhd R Q q cW cD cE P j hq ha he hD hE i)).continuousOn

/-- The complete explicit marked product is holomorphic in the moving
variable on a half-plane containing every fixed-bin rectangle. -/
theorem explicitEuler_differentiableOn_s {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (w z : ℂ) (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    DifferentiableOn ℂ
      (fun s => ∏' i, explicitLocalEuler R Q q cW cD cE P j i (s, w, z))
      {s | a + 15 * e < s.re} := by
  have h := explicitEuler_hasProdLocallyUniformlyOn R Q q cW cD cE P j
    hq ha ha' he he' hW hD hE hsum
  have hslice := h.comp (fun s : ℂ => (s, w, z))
    (show Set.MapsTo (fun s : ℂ => (s, w, z)) {s | a + 15 * e < s.re}
      (sweptTube a e) from fun s hs => ⟨hs, hw, hz⟩)
    (by fun_prop)
  have hlocal (i : ι) : AnalyticOnNhd ℂ
      (fun s => explicitLocalEuler R Q q cW cD cE P j i (s, w, z))
      {s | a + 15 * e < s.re} := by
    intro s hs
    have hi := explicitLocalEuler_analyticOnNhd R Q q cW cD cE P j hq ha he hD hE i
      (s, w, z) ⟨hs, hw, hz⟩
    exact AnalyticAt.comp (f := fun x : ℂ => (x, w, z)) (x := s) hi (by fun_prop)
  apply TendstoLocallyUniformlyOn.differentiableOn hslice
    (Filter.Eventually.of_forall fun F => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (F.analyticOnNhd_fun_prod (fun i _ => hlocal i)).differentiableOn

#print axioms explicitEuler_continuousOn
#print axioms explicitEuler_differentiableOn_s
end HeckeSkeleton.HighBinContinuation
