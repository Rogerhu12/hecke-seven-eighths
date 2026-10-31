import HeckeGeneral.Analysis.GlobalThetaData

/-! A nonzero real nonnegative smooth window has a positive lower bound
on one closed interval strictly inside its original support annulus. -/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.WindowPIT

open Filter Set HeckeGeneral.ThetaSkeleton.Global
open scoped Topology

theorem exists_positive_interval (w : SmoothAnnularTest)
    (hre : ∀ y, (w.toFun y).im = 0) (hnn : ∀ y, 0 ≤ (w.toFun y).re)
    (hne : ∃ y, w.toFun y ≠ 0) (hsupp : Function.support w.toFun ⊆ Set.Ioo 1 2) :
    ∃ a b m : ℝ, 1 < a ∧ a < b ∧ b < 2 ∧ 0 < m ∧
      ∀ y ∈ Set.Icc a b, m ≤ (w.toFun y).re := by
  obtain ⟨x, hx⟩ := hne
  have hxre : (w.toFun x).re ≠ 0 := by
    intro hzero
    apply hx
    apply Complex.ext
    · exact hzero
    · exact hre x
  have hxpos : 0 < (w.toFun x).re := lt_of_le_of_ne (hnn x) (Ne.symm hxre)
  have hxwin : x ∈ Set.Ioo (1 : ℝ) 2 := hsupp hx
  let m : ℝ := (w.toFun x).re / 2
  have hm : 0 < m := by dsimp only [m]; linarith
  have hnear : ∀ᶠ y in 𝓝 x, m < (w.toFun y).re := by
    have hs : IsOpen {y : ℝ | m < (w.toFun y).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp w.smooth.continuous)
    exact hs.mem_nhds (show m < (w.toFun x).re by dsimp only [m]; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let d : ℝ := min (δ / 2) (min ((x - 1) / 2) ((2 - x) / 2))
  have hd : 0 < d := lt_min (by linarith)
    (lt_min (by linarith [hxwin.1]) (by linarith [hxwin.2]))
  have hdδ : d ≤ δ / 2 := min_le_left _ _
  have hdx : d ≤ (x - 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : d ≤ (2 - x) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨x - d, x + d, m, by linarith, by linarith, by linarith, hm, ?_⟩
  intro y hy
  have habs : |y - x| ≤ d := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  exact (hball (y := y) (by rw [Real.dist_eq]; linarith)).le

end HeckeSkeleton.WindowPIT
