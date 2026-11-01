import HeckeSkeleton.HighBinSupport.EulerRegionAnalytic
import HeckeSkeleton.HighBinSupport.JointAnalyticLimit

/-!
Normal convergence and joint analyticity of the explicit four-case Euler
family on the repository's original corrected region. The hypotheses are
the elementary phase bounds and prime-norm summability. All finite marked
and ramified factors, including zero factors, remain in the product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open Set Filter
open scoped Classical Topology BigOperators

theorem explicitEuler_hasProdLocallyUniformlyOn_rowEulerRegion
    {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5)
    (hq : ∀ i, 2 ≤ q i) (hW : ∀ i, ‖cW i‖ ≤ 1)
    (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i) ^ (-σ))) :
    HasProdLocallyUniformlyOn (explicitLocalEuler R Q q cW cD cE P j)
      (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v)
      rowEulerRegion := by
  have hlocal (i : ι) :
      AnalyticOnNhd ℂ (explicitLocalEuler R Q q cW cD cE P j i) rowEulerRegion := by
    apply (explicitLocalEuler_analyticOnNhd_positiveRegion R Q q cW cD cE P j
      (fun i => lt_of_lt_of_le (by norm_num) (hq i)) hD hE i).mono
    intro v hv
    exact ⟨lt_trans (by norm_num) hv.1, lt_trans (by norm_num) hv.2.2.2.2.1⟩
  let U (δ : ℝ) : Set (ℂ × ℂ × ℂ) :=
    rowEulerRegion ∩ {v | 1 + δ < v.2.1.re + 6 * v.2.2.re ∧
      5 + δ < 6 * v.1.re + 6 * v.2.2.re ∧
      1 + δ < v.1.re + 6 * v.2.2.re ∧
      1 + δ < v.1.re + v.2.1.re ∧
      2 + δ < v.1.re + v.2.1.re + 6 * v.2.2.re}
  have hUopen (δ : ℝ) : IsOpen (U δ) := by
    have hs : Continuous (fun v : ℂ × ℂ × ℂ => v.1.re) :=
      Complex.continuous_re.comp continuous_fst
    have hw : Continuous (fun v : ℂ × ℂ × ℂ => v.2.1.re) :=
      Complex.continuous_re.comp (continuous_fst.comp continuous_snd)
    have hz : Continuous (fun v : ℂ × ℂ × ℂ => v.2.2.re) :=
      Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
    exact rowEulerRegion_isOpen.inter
      ((isOpen_lt continuous_const (hw.add (continuous_const.mul hz))).inter
      ((isOpen_lt continuous_const ((continuous_const.mul hs).add (continuous_const.mul hz))).inter
      ((isOpen_lt continuous_const (hs.add (continuous_const.mul hz))).inter
      ((isOpen_lt continuous_const (hs.add hw)).inter
        (isOpen_lt continuous_const ((hs.add hw).add (continuous_const.mul hz)))))))
  have hprod (δ : ℝ) (hδ : 0 < δ) :
      HasProdLocallyUniformlyOn (explicitLocalEuler R Q q cW cD cE P j)
        (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v) (U δ) := by
    have hprime : Summable (fun i => (q i) ^ (-1 - δ)) := by
      have h := hsum (1 + δ) (by linarith)
      convert h using 1
      funext i
      congr 1
      ring
    have hmajor := hprime.mul_left (11 / sweptTubeEulerMargin)
    have hbound : ∀ᶠ i : ι in cofinite,
        ∀ v ∈ U δ, ‖explicitLocalEuler R Q q cW cD cE P j i v - 1‖ ≤
          (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - δ) := by
      filter_upwards [(R ∪ Q).eventually_cofinite_notMem] with i hi v hv
      have hR : i ∉ R := fun h => hi (Finset.mem_union_left Q h)
      have hQ : i ∉ Q := fun h => hi (Finset.mem_union_right R h)
      rcases hv with ⟨hv, h1, h2, h3, h4, h5⟩
      have hb := phaseRowEuler_region_bound (hq i) hδ.le
        (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2 (hW i) (hD i) (hE i)
        hv.1.le hv.2.1.le hv.2.2.1.le h1.le h2.le h3.le h4.le h5.le
      simpa only [explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero] using hb
    have h := Summable.hasProdLocallyUniformlyOn_one_add (hUopen δ) hmajor
      (f := fun i v => explicitLocalEuler R Q q cW cD cE P j i v - 1) hbound
      (fun i => ((hlocal i).continuousOn.mono (fun _ hv => hv.1)).sub continuousOn_const)
    have hone (x : ℂ) : 1 + (x - 1) = x := by ring
    simpa only [hone] using h
  have hcover : rowEulerRegion = ⋃ δ : {δ : ℝ // 0 < δ}, U δ.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨δ, hδ, h1, h2, h3, h4, h5⟩ :=
        exists_region_margin v.1 v.2.1 v.2.2 hv
      apply Set.mem_iUnion.mpr
      refine ⟨⟨δ / 2, by positivity⟩, hv, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · intro hv
      obtain ⟨δ, hv⟩ := Set.mem_iUnion.mp hv
      exact hv.1
  rw [hcover]
  exact tendstoLocallyUniformlyOn_iUnion (fun δ => hUopen δ.val)
    (fun δ => hprod δ.val δ.property)

theorem explicitEuler_analyticOnNhd_rowEulerRegion
    {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5)
    (hq : ∀ i, 2 ≤ q i) (hW : ∀ i, ‖cW i‖ ≤ 1)
    (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable (fun i => (q i) ^ (-σ))) :
    AnalyticOnNhd ℂ
      (fun v => ∏' i, explicitLocalEuler R Q q cW cD cE P j i v)
      rowEulerRegion := by
  apply HighBinJointAnalytic.analyticOnNhd_of_tendstoLocallyUniformlyOn
    (explicitEuler_hasProdLocallyUniformlyOn_rowEulerRegion R Q q cW cD cE P j
      hq hW hD hE hsum) ?_ rowEulerRegion_isOpen
  exact Filter.Eventually.of_forall fun F => F.analyticOnNhd_fun_prod (fun i _ =>
    (explicitLocalEuler_analyticOnNhd_positiveRegion R Q q cW cD cE P j
      (fun i => lt_of_lt_of_le (by norm_num) (hq i)) hD hE i).mono
      (fun _ hv => ⟨lt_trans (by norm_num) hv.1, lt_trans (by norm_num) hv.2.2.2.2.1⟩))

end HeckeSkeleton.HighBinContinuation
