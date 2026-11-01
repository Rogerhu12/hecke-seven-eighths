import HeckeSkeleton.HighBinSupport.EulerAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open Set Filter
open scoped Topology BigOperators

private theorem one_add_error (x : ℂ) : 1 + (x - 1) = x := by ring

/-- A summability certificate for the prime norms gives convergence of the
actual regular product. This statement has only a scalar summability input,
not convergence or a bound for the desired Euler product. -/
theorem phaseRowEuler_multipliable {ι : Type*} (q : ι → ℝ)
    (cW cD cE : ι → ℂ) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    Multipliable (fun i => phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2) := by
  have hb : Summable (fun i => ‖phaseRowEuler (q i) (cW i) (cD i) (cE i)
      v.1 v.2.1 v.2.2 - 1‖) :=
    (hsum.mul_left (11 / sweptTubeEulerMargin)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun i => phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv)
  simpa only [one_add_error] using multipliable_one_add_of_summable hb

/-- The regular product converges locally uniformly on the whole open
three-variable tube.  No nonvanishing of the local numerators is needed. -/
theorem phaseRowEuler_hasProdLocallyUniformlyOn {ι : Type*} (q : ι → ℝ)
    (cW cD cE : ι → ℂ) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e))) :
    HasProdLocallyUniformlyOn
      (fun i (v : ℂ × ℂ × ℂ) => phaseRowEuler (q i) (cW i) (cD i) (cE i)
        v.1 v.2.1 v.2.2)
      (fun v : ℂ × ℂ × ℂ => ∏' i, phaseRowEuler (q i) (cW i) (cD i) (cE i)
        v.1 v.2.1 v.2.2) (sweptTube a e) := by
  have hb : Summable (fun i => (11 / sweptTubeEulerMargin) *
      (q i) ^ (-1 - 8 * e)) := hsum.mul_left _
  have h := Summable.hasProdLocallyUniformlyOn_one_add (sweptTube_isOpen a e) hb
    (f := fun i (v : ℂ × ℂ × ℂ) =>
      phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2 - 1)
    (Filter.Eventually.of_forall fun i v hv =>
      phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv)
    (fun i => (phaseRowEuler_analyticOnNhd (hq i) ha he
      (cW i) (cD i) (cE i) (hD i) (hE i)).continuousOn.sub continuousOn_const)
  simpa only [one_add_error] using h

/-- The corresponding normal convergence on each s-slice is enough for
the actual rectangular s-contour move. -/
theorem phaseRowEuler_hasProdLocallyUniformlyOn_s {ι : Type*} (q : ι → ℝ)
    (cW cD cE : ι → ℂ) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (w z : ℂ) (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    HasProdLocallyUniformlyOn
      (fun i s => phaseRowEuler (q i) (cW i) (cD i) (cE i) s w z)
      (fun s => ∏' i, phaseRowEuler (q i) (cW i) (cD i) (cE i) s w z)
      {s | a + 15 * e < s.re} := by
  have hU : IsOpen {s : ℂ | a + 15 * e < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hb : Summable (fun i => (11 / sweptTubeEulerMargin) *
      (q i) ^ (-1 - 8 * e)) := hsum.mul_left _
  have h := Summable.hasProdLocallyUniformlyOn_one_add hU hb
    (f := fun i s => phaseRowEuler (q i) (cW i) (cD i) (cE i) s w z - 1)
    (Filter.Eventually.of_forall fun i s hs =>
      phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) (s, w, z) ⟨hs, hw, hz⟩)
    (fun i => (phaseRowEuler_analytic_s (hq i) ha he
      (cW i) (cD i) (cE i) w z (hD i) (hE i) hw hz).continuousOn.sub
        continuousOn_const)
  simpa only [one_add_error] using h

/-- Holomorphy of the convergent regular product in the moving variable.
The convergence and local holomorphy are conclusions of the preceding
estimates, not assumptions about the desired product. -/
theorem phaseRowEuler_tprod_differentiableOn_s {ι : Type*} (q : ι → ℝ)
    (cW cD cE : ι → ℂ) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha' : a ≤ 1)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (w z : ℂ) (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    DifferentiableOn ℂ
      (fun s => ∏' i, phaseRowEuler (q i) (cW i) (cD i) (cE i) s w z)
      {s | a + 15 * e < s.re} := by
  classical
  have h := phaseRowEuler_hasProdLocallyUniformlyOn_s q cW cD cE
    hq ha ha' he he' hW hD hE hsum w z hw hz
  apply h.differentiableOn (Filter.Eventually.of_forall fun F => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (F.analyticOnNhd_fun_prod (fun i _ => phaseRowEuler_analytic_s (hq i) ha he
    (cW i) (cD i) (cE i) w z (hD i) (hE i) hw hz)).differentiableOn

#print axioms phaseRowEuler_multipliable
#print axioms phaseRowEuler_hasProdLocallyUniformlyOn
#print axioms phaseRowEuler_tprod_differentiableOn_s
end HeckeSkeleton.HighBinContinuation
