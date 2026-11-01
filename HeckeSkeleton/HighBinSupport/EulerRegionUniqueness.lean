import HeckeGeneral.Analysis.RowEulerRegion
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected

/-!
# Uniqueness on the original row Euler region

The repository's eight strict affine inequalities define a convex region.
Two jointly analytic functions on that region which agree on the original
absolute-convergence domain consequently agree throughout the region.
This statement does not extend that region to contours with nonpositive
real part in the second coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical
open Set Filter
open scoped Topology

theorem rowEulerRegion_convex : Convex ℝ rowEulerRegion := by
  let rS : (ℂ × ℂ × ℂ) →ₗ[ℝ] ℝ :=
    Complex.reLm.comp (LinearMap.fst ℝ ℂ (ℂ × ℂ))
  let rW : (ℂ × ℂ × ℂ) →ₗ[ℝ] ℝ :=
    Complex.reLm.comp ((LinearMap.fst ℝ ℂ ℂ).comp
      (LinearMap.snd ℝ ℂ (ℂ × ℂ)))
  let rZ : (ℂ × ℂ × ℂ) →ₗ[ℝ] ℝ :=
    Complex.reLm.comp ((LinearMap.snd ℝ ℂ ℂ).comp
      (LinearMap.snd ℝ ℂ (ℂ × ℂ)))
  change Convex ℝ
    ({v | (1 / 2 : ℝ) < rS v} ∩
      ({v | (0 : ℝ) < rW v} ∩
      ({v | (0 : ℝ) < rZ v} ∩
      ({v | (1 : ℝ) < (rS + rW) v} ∩
      ({v | (5 / 6 : ℝ) < (rS + rZ) v} ∩
      ({v | (2 : ℝ) < (rS + rW + (6 : ℝ) • rZ) v} ∩
      ({v | (1 : ℝ) < (rW + (6 : ℝ) • rZ) v} ∩
       {v | (1 : ℝ) < (rS + (6 : ℝ) • rZ) v})))))))
  exact (convex_halfSpace_gt rS.isLinear _).inter
    ((convex_halfSpace_gt rW.isLinear _).inter
    ((convex_halfSpace_gt rZ.isLinear _).inter
    ((convex_halfSpace_gt (rS + rW).isLinear _).inter
    ((convex_halfSpace_gt (rS + rZ).isLinear _).inter
    ((convex_halfSpace_gt (rS + rW + (6 : ℝ) • rZ).isLinear _).inter
    ((convex_halfSpace_gt (rW + (6 : ℝ) • rZ).isLinear _).inter
      (convex_halfSpace_gt (rS + (6 : ℝ) • rZ).isLinear _)))))))

theorem rowEulerRegion_isPreconnected : IsPreconnected rowEulerRegion :=
  rowEulerRegion_convex.isPreconnected

/-- Equality on the actual initial open domain determines an analytic
function on the entire original Euler region. The identity principle is
the Banach-space theorem, so the conclusion is genuinely in three complex
variables. -/
theorem eqOn_rowEulerRegion_of_initial
    {f g : (ℂ × ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f rowEulerRegion)
    (hg : AnalyticOnNhd ℂ g rowEulerRegion)
    (hinitial : ∀ v : ℂ × ℂ × ℂ,
      4 < v.1.re → 4 < v.2.1.re → 2 < v.2.2.re → f v = g v) :
    EqOn f g rowEulerRegion := by
  let U : Set (ℂ × ℂ × ℂ) :=
    {v | 4 < v.1.re ∧ 4 < v.2.1.re ∧ 2 < v.2.2.re}
  have hs : Continuous (fun v : ℂ × ℂ × ℂ => v.1.re) :=
    Complex.continuous_re.comp continuous_fst
  have hw : Continuous (fun v : ℂ × ℂ × ℂ => v.2.1.re) :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_snd)
  have hz : Continuous (fun v : ℂ × ℂ × ℂ => v.2.2.re) :=
    Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hs).inter
      ((isOpen_lt continuous_const hw).inter (isOpen_lt continuous_const hz))
  have hbase : ((5 : ℂ), (5 : ℂ), (5 : ℂ)) ∈ rowEulerRegion := by
    norm_num [rowEulerRegion]
  have hbaseU : ((5 : ℂ), (5 : ℂ), (5 : ℂ)) ∈ U := by
    norm_num [U]
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    rowEulerRegion_isPreconnected hbase
  filter_upwards [hU.mem_nhds hbaseU] with v hv
  exact hinitial v hv.1 hv.2.1 hv.2.2

#print axioms rowEulerRegion_convex
#print axioms rowEulerRegion_isPreconnected
#print axioms eqOn_rowEulerRegion_of_initial

end HeckeSkeleton.HighBinContinuation
