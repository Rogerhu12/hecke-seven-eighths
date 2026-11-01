import HeckeSkeleton.HighBinSupport.EulerPhase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions
/-!
# Analyticity of regular local factors throughout the high-bin move

The domain is genuinely open in all three complex variables.  Both apparent
geometric denominators have already been cancelled in the imported rational
function, so no condition excluding V=1 or W=1 occurs.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical
open Set

theorem analyticAt_realBase_cpow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {v : E} {q : ℝ}
    (hq : 0 < q) (hf : AnalyticAt ℂ f v) :
    AnalyticAt ℂ (fun x => (q : ℂ) ^ f x) v := by
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  simp only [Complex.cpow_def_of_ne_zero hq']
  convert! ((analyticAt_const :
    AnalyticAt ℂ (fun _ : E => Complex.log (q : ℂ)) v).mul hf).cexp' using 1

/-- Local regular factors are analytic jointly in (s,w,z) on the tube. -/
theorem phaseRowEuler_analyticOnNhd {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (cW cD cE : ℂ)
    (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => phaseRowEuler q cW cD cE v.1 v.2.1 v.2.2)
      (sweptTube a e) := by
  intro v hv
  have hq0 : 0 < q := by linarith
  have hs : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun v : ℂ × ℂ × ℂ => v.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  let V : (ℂ × ℂ × ℂ) → ℂ := fun x => (q : ℂ) ^ (-6 * x.2.2)
  let W : (ℂ × ℂ × ℂ) → ℂ := fun x => cW * (q : ℂ) ^ (-x.2.1)
  let D : (ℂ × ℂ × ℂ) → ℂ := fun x => cD * (q : ℂ) ^ (-x.1)
  let E : (ℂ × ℂ × ℂ) → ℂ := fun x =>
    cE * (q : ℂ) ^ (4 - 6 * x.1) * (q : ℂ) ^ (-6 * x.2.2)
  have hV : AnalyticAt ℂ V v := analyticAt_realBase_cpow hq0
    ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => (-6 : ℂ)) v).mul hz)
  have hW' : AnalyticAt ℂ W v :=
    analyticAt_const.mul (analyticAt_realBase_cpow hq0 hw.neg)
  have hD' : AnalyticAt ℂ D v :=
    analyticAt_const.mul (analyticAt_realBase_cpow hq0 hs.neg)
  have hE' : AnalyticAt ℂ E v :=
    (analyticAt_const.mul (analyticAt_realBase_cpow hq0
      (analyticAt_const.sub (analyticAt_const.mul hs)))).mul hV
  have hN : AnalyticAt ℂ (fun x =>
      (1 - E x) * (1 - W x * V x) +
        E x * (1 - W x) * ((1 - (q : ℂ)⁻¹) + W x * (1 - V x)) -
        D x * (1 - W x) * ((1 - V x) + ((q : ℂ) - 1) * W x * V x)) v := by
    fun_prop
  have hDen : AnalyticAt ℂ (fun x => (1 - E x) * (1 - D x)) v := by
    fun_prop
  have hn := phaseRowEuler_denominators_ne_zero hq ha he cD cE v.1 v.2.2
    hD hE hv.1.le hv.2.2.le
  exact hN.div hDen (mul_ne_zero hn.2 hn.1)

/-- The s-slice required for a fixed-bin contour move is analytic on a
whole half-plane containing the rectangular move. -/
theorem phaseRowEuler_analytic_s {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (cW cD cE w z : ℂ)
    (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hw : 1 - a - 7 * e < w.re) (hz : 17 / 50 - e < z.re) :
    AnalyticOnNhd ℂ (fun s => phaseRowEuler q cW cD cE s w z)
      {s | a + 15 * e < s.re} := by
  intro s hs
  have h := phaseRowEuler_analyticOnNhd hq ha he cW cD cE hD hE
    (s, w, z) ⟨hs, hw, hz⟩
  have hemb : AnalyticAt ℂ (fun x : ℂ => (x, w, z)) s := by fun_prop
  exact AnalyticAt.comp (f := fun x : ℂ => (x, w, z)) (x := s) h hemb

#print axioms phaseRowEuler_analyticOnNhd
#print axioms phaseRowEuler_analytic_s
end HeckeSkeleton.HighBinContinuation
