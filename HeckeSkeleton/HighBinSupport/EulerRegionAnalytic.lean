import HeckeGeneral.Analysis.RowEulerRegion
import HeckeSkeleton.HighBinSupport.EulerCorrectedRegion
import HeckeSkeleton.HighBinSupport.EulerAnalytic
import HeckeSkeleton.HighBinSupport.HighEulerScalarBounds
import HeckeSkeleton.HighBinSupport.ExplicitEulerFamily

/-!
Local analytic continuation on the positive-s region containing every
point of the original corrected Euler domain. This does not identify a
normally convergent three-variable product with an analytic function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open Set

/-- The local rational denominators are nonzero under their actual
real-part conditions, independently of the narrower high-bin tube. -/
theorem phaseRowEuler_denominators_ne_zero_of_re {q : ℝ} (hq : 1 < q)
    (cD cE s z : ℂ) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 0 < s.re) (hsz : 2 / 3 < s.re + z.re) :
    1 - cD * (q : ℂ) ^ (-s) ≠ 0 ∧
    1 - cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) ≠ 0 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hp (v : ℂ) : ‖(q : ℂ) ^ v‖ = q ^ v.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 v
  have hDs : ‖cD * (q : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hp, Complex.neg_re]
    calc
      _ ≤ 1 * q ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hq0.le _)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hEs : ‖cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z)‖ < 1 := by
    rw [norm_mul, norm_mul, hp, hp]
    calc
      _ ≤ 1 * q ^ (4 - 6 * s).re * q ^ (-6 * z).re :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hq0.le _))
          (Real.rpow_nonneg hq0.le _)
      _ = q ^ ((4 - 6 * s).re + (-6 * z).re) := by
        rw [one_mul, ← Real.rpow_add hq0]
      _ < 1 := by
        apply Real.rpow_lt_one_of_one_lt_of_neg hq
        norm_num [Complex.mul_re]
        linarith
  constructor
  · intro h
    have h' : cD * (q : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    simpa [h'] using hDs
  · intro h
    have h' : cE * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ) ^ (-6 * z) = 1 :=
      (sub_eq_zero.mp h).symm
    simpa [h'] using hEs

/-- Local joint analyticity needs only the two genuine rational
denominators; the cancelled geometric denominators play no role. -/
theorem phaseRowEuler_analyticAt {q : ℝ} (hq : 0 < q)
    (cW cD cE : ℂ) (v : ℂ × ℂ × ℂ)
    (hD0 : 1 - cD * (q : ℂ) ^ (-v.1) ≠ 0)
    (hE0 : 1 - cE * (q : ℂ) ^ (4 - 6 * v.1) * (q : ℂ) ^ (-6 * v.2.2) ≠ 0) :
    AnalyticAt ℂ
      (fun x : ℂ × ℂ × ℂ => phaseRowEuler q cW cD cE x.1 x.2.1 x.2.2) v := by
  have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  let V : (ℂ × ℂ × ℂ) → ℂ := fun x => (q : ℂ) ^ (-6 * x.2.2)
  let W : (ℂ × ℂ × ℂ) → ℂ := fun x => cW * (q : ℂ) ^ (-x.2.1)
  let D : (ℂ × ℂ × ℂ) → ℂ := fun x => cD * (q : ℂ) ^ (-x.1)
  let E : (ℂ × ℂ × ℂ) → ℂ := fun x =>
    cE * (q : ℂ) ^ (4 - 6 * x.1) * (q : ℂ) ^ (-6 * x.2.2)
  have hV : AnalyticAt ℂ V v := analyticAt_realBase_cpow hq
    ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ × ℂ => (-6 : ℂ)) v).mul hz)
  have hW : AnalyticAt ℂ W v :=
    analyticAt_const.mul (analyticAt_realBase_cpow hq hw.neg)
  have hD : AnalyticAt ℂ D v :=
    analyticAt_const.mul (analyticAt_realBase_cpow hq hs.neg)
  have hE : AnalyticAt ℂ E v :=
    (analyticAt_const.mul (analyticAt_realBase_cpow hq
      (analyticAt_const.sub (analyticAt_const.mul hs)))).mul hV
  have hN : AnalyticAt ℂ (fun x =>
      (1 - E x) * (1 - W x * V x) +
        E x * (1 - W x) * ((1 - (q : ℂ)⁻¹) + W x * (1 - V x)) -
        D x * (1 - W x) * ((1 - V x) + ((q : ℂ) - 1) * W x * V x)) v := by
    fun_prop
  have hDen : AnalyticAt ℂ (fun x => (1 - E x) * (1 - D x)) v := by
    fun_prop
  exact hN.div hDen (mul_ne_zero hE0 hD0)

theorem phaseRowEuler_analyticOnNhd_positiveRegion {q : ℝ} (hq : 1 < q)
    (cW cD cE : ℂ) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => phaseRowEuler q cW cD cE v.1 v.2.1 v.2.2)
      {v | 0 < v.1.re ∧ 2 / 3 < v.1.re + v.2.2.re} := by
  intro v hv
  have hn := phaseRowEuler_denominators_ne_zero_of_re hq cD cE v.1 v.2.2
    hD hE hv.1 hv.2
  exact phaseRowEuler_analyticAt (lt_trans zero_lt_one hq) cW cD cE v hn.1 hn.2

private theorem region_phaseMonomial_analytic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {x : E} {q : ℝ} (hq : 0 < q)
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (c : ℂ) (r : ℝ) (m n : ℕ) :
    AnalyticAt ℂ (fun y => phaseMonomial q c r (f y) (g y) m n) x := by
  exact analyticAt_const.mul (analyticAt_realBase_cpow hq
    ((analyticAt_const.sub (analyticAt_const.mul hf)).sub (analyticAt_const.mul hg)))

theorem ramifiedTable_analyticAt (P : PhaseData) {q : ℝ} (hq : 0 < q)
    (j : Fin 5) (v : ℂ × ℂ × ℂ) (hn : 1 - coordR P q v.1 v.2.2 ≠ 0) :
    AnalyticAt ℂ
      (fun x : ℂ × ℂ × ℂ => ramifiedTableValue P q x.1 x.2.1 x.2.2 j) v := by
  have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hV : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => coordV q x.2.2) v :=
    analyticAt_realBase_cpow hq (analyticAt_const.mul hz)
  have hR : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => coordR P q x.1 x.2.2) v :=
    region_phaseMonomial_analytic hq hs hz _ _ _ _
  have hX : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => (q : ℂ) ^ (-x.1)) v :=
    analyticAt_realBase_cpow hq hs.neg
  have hY : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => (q : ℂ) ^ (-x.2.1)) v :=
    analyticAt_realBase_cpow hq hw.neg
  have hm (c : ℂ) (r : ℝ) (m n : ℕ) :
      AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => phaseMonomial q c r x.1 x.2.1 m n) v :=
    region_phaseMonomial_analytic hq hs hw c r m n
  have hS : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => specialTerm P q x.1 x.2.1 j) v := by
    fin_cases j
    · exact hm _ _ _ _
    · exact hm _ _ _ _
    · exact (hm _ _ _ _).sub (hm _ _ _ _)
    · exact (hm _ _ _ _).neg
    · exact (hm _ _ _ _).neg
  unfold ramifiedTableValue
  apply AnalyticAt.div
  · fun_prop
  · exact analyticAt_const.sub hR
  · exact hn

theorem coordR_norm_lt_one_of_re (P : PhaseData) {q : ℝ} (hq : 1 < q)
    (s z : ℂ) (hsz : 2 / 3 < s.re + z.re) : ‖coordR P q s z‖ < 1 := by
  have h := phaseMonomial_norm_le_of_exponent_le q hq.le _ P.alpha_sq_bound
    4 s z 6 6 (4 - 6 * s.re - 6 * z.re) (by norm_num)
  exact h.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith))

theorem ramifiedTable_analyticOnNhd_positiveRegion (P : PhaseData) {q : ℝ}
    (hq : 1 < q) (j : Fin 5) :
    AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ × ℂ => ramifiedTableValue P q v.1 v.2.1 v.2.2 j)
      {v | 2 / 3 < v.1.re + v.2.2.re} := by
  intro v hv
  have hR := coordR_norm_lt_one_of_re P hq v.1 v.2.2 hv
  have hn : 1 - coordR P q v.1 v.2.2 ≠ 0 := by
    intro h
    have h' : coordR P q v.1 v.2.2 = 1 := (sub_eq_zero.mp h).symm
    simpa [h'] using hR
  exact ramifiedTable_analyticAt P (lt_trans zero_lt_one hq) j v hn

theorem unmarkedZeroPart_analyticAt {q : ℝ} (hq : 0 < q)
    (cW cD : ℂ) (v : ℂ × ℂ × ℂ)
    (hn : 1 - cD * (q : ℂ) ^ (-v.1) ≠ 0) :
    AnalyticAt ℂ
      (fun x : ℂ × ℂ × ℂ => unmarkedZeroPart q cW cD x.1 x.2.1 x.2.2) v := by
  have hs : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.1) v := analyticAt_fst
  have hw : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => x.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hW : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => (q : ℂ) ^ (-x.2.1)) v :=
    analyticAt_realBase_cpow hq hw.neg
  have hD : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => (q : ℂ) ^ (-x.1)) v :=
    analyticAt_realBase_cpow hq hs.neg
  have hV : AnalyticAt ℂ (fun x : ℂ × ℂ × ℂ => (q : ℂ) ^ (-6 * x.2.2)) v :=
    analyticAt_realBase_cpow hq (analyticAt_const.mul hz)
  exact (analyticAt_const.sub ((analyticAt_const.mul hW).mul hV)).div
    (analyticAt_const.sub (analyticAt_const.mul hD)) hn

/-- All four regular/ramified, marked/unmarked local branches are jointly
analytic on a region containing the entire original positive-w domain. -/
theorem explicitLocalEuler_analyticOnNhd_positiveRegion {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5)
    (hq : ∀ i, 1 < q i) (hD : ∀ i, ‖cD i‖ ≤ 1)
    (hE : ∀ i, ‖cE i‖ ≤ 1) (i : ι) :
    AnalyticOnNhd ℂ (explicitLocalEuler R Q q cW cD cE P j i)
      {v | 0 < v.1.re ∧ 2 / 3 < v.1.re + v.2.2.re} := by
  by_cases hR : i ∈ R
  · have h := ramifiedTable_analyticOnNhd_positiveRegion (P i) (hq i) (j i)
    have hfun : explicitLocalEuler R Q q cW cD cE P j i =
        (fun v : ℂ × ℂ × ℂ => ramifiedTableValue (P i) (q i) v.1 v.2.1 v.2.2 (j i) -
          (if i ∈ Q then 1 else 0)) := by
      funext v
      simp only [explicitLocalEuler, if_pos hR]
    rw [hfun]
    intro v hv
    exact (h v hv.2).sub analyticAt_const
  · have h := phaseRowEuler_analyticOnNhd_positiveRegion (hq i)
      (cW i) (cD i) (cE i) (hD i) (hE i)
    by_cases hQ : i ∈ Q
    · have hfun : explicitLocalEuler R Q q cW cD cE P j i =
          (fun v : ℂ × ℂ × ℂ => phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2 -
            unmarkedZeroPart (q i) (cW i) (cD i) v.1 v.2.1 v.2.2) := by
        funext v
        simp only [explicitLocalEuler, if_neg hR, if_pos hQ]
      rw [hfun]
      intro v hv
      have hn := phaseRowEuler_denominators_ne_zero_of_re (hq i)
        (cD i) (cE i) v.1 v.2.2 (hD i) (hE i) hv.1 hv.2
      exact (h v hv).sub (unmarkedZeroPart_analyticAt (lt_trans zero_lt_one (hq i))
        (cW i) (cD i) v hn.1)
    · have hfun : explicitLocalEuler R Q q cW cD cE P j i =
          (fun v : ℂ × ℂ × ℂ => phaseRowEuler (q i) (cW i) (cD i) (cE i) v.1 v.2.1 v.2.2) := by
        funext v
        simp only [explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero]
      rw [hfun]
      exact h

theorem exists_region_margin (s w z : ℂ)
    (hv : (s, w, z) ∈ rowEulerRegion) :
    ∃ δ : ℝ, 0 < δ ∧
      1 + δ ≤ w.re + 6 * z.re ∧ 5 + δ ≤ 6 * s.re + 6 * z.re ∧
      1 + δ ≤ s.re + 6 * z.re ∧ 1 + δ ≤ s.re + w.re ∧
      2 + δ ≤ s.re + w.re + 6 * z.re := by
  rcases hv with ⟨_hs, _hw, _hz, hsw, hsz, hswz, hwz, hsz'⟩
  let δ := min (w.re + 6 * z.re - 1)
    (min (6 * s.re + 6 * z.re - 5)
      (min (s.re + 6 * z.re - 1)
        (min (s.re + w.re - 1) (s.re + w.re + 6 * z.re - 2))))
  have hδ : 0 < δ := by
    dsimp only [δ]
    refine lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by linarith) (lt_min (by linarith) (by linarith))))
  have hle : δ ≤ min (w.re + 6 * z.re - 1)
    (min (6 * s.re + 6 * z.re - 5)
      (min (s.re + 6 * z.re - 1)
        (min (s.re + w.re - 1) (s.re + w.re + 6 * z.re - 2)))) := le_rfl
  simp only [le_min_iff] at hle
  rcases hle with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨δ, hδ, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem phaseRowEuler_region_bound
    {q δ : ℝ} (hq : 2 ≤ q) (hδ : 0 ≤ δ)
    (cW cD cE s w z : ℂ)
    (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (hs : 1 / 2 ≤ s.re) (hw : 0 ≤ w.re) (hz : 0 ≤ z.re)
    (h1 : 1 + δ ≤ w.re + 6 * z.re)
    (h2 : 5 + δ ≤ 6 * s.re + 6 * z.re)
    (h3 : 1 + δ ≤ s.re + 6 * z.re)
    (h4 : 1 + δ ≤ s.re + w.re)
    (h5 : 2 + δ ≤ s.re + w.re + 6 * z.re) :
    ‖phaseRowEuler q cW cD cE s w z - 1‖ ≤
      (11 / sweptTubeEulerMargin) * q ^ (-1 - δ) := by
  have hq0 : 0 < q := by linarith
  have hp (v : ℂ) : ‖(q : ℂ) ^ v‖ = q ^ v.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hq0 v
  have hv : (-6 * z).re = -6 * z.re := by simp [Complex.mul_re]
  have heq : (4 - 6 * s).re = 4 - 6 * s.re := by simp [Complex.mul_re]
  unfold phaseRowEuler
  refine rowEulerRationalValue_correctedRegion_bound
    hq hs hw hz hδ h1 h2 h3 h4 h5 _ _ _ _ ?_ ?_ ?_ ?_
  · simpa only [hp, hv] using (le_refl (q ^ (-6 * z.re)))
  · rw [norm_mul, hp, Complex.neg_re]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hW
      (Real.rpow_nonneg hq0.le (-w.re))
  · rw [norm_mul, hp, Complex.neg_re]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD
      (Real.rpow_nonneg hq0.le (-s.re))
  · rw [norm_mul, norm_mul, hp, hp, hv, heq]
    calc
      _ ≤ 1 * q ^ (4 - 6 * s.re) * q ^ (-6 * z.re) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hq0.le _))
          (Real.rpow_nonneg hq0.le _)
      _ = q ^ (4 - 6 * s.re - 6 * z.re) := by
        rw [one_mul, ← Real.rpow_add hq0]
        congr 1
        ring

theorem rowEulerRegion_isOpen : IsOpen rowEulerRegion := by
  have hs : Continuous (fun v : ℂ × ℂ × ℂ => v.1.re) :=
    Complex.continuous_re.comp continuous_fst
  have hw : Continuous (fun v : ℂ × ℂ × ℂ => v.2.1.re) :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_snd)
  have hz : Continuous (fun v : ℂ × ℂ × ℂ => v.2.2.re) :=
    Complex.continuous_re.comp (continuous_snd.comp continuous_snd)
  unfold rowEulerRegion
  exact (isOpen_lt continuous_const hs).inter
    ((isOpen_lt continuous_const hw).inter
    ((isOpen_lt continuous_const hz).inter
    ((isOpen_lt continuous_const (hs.add hw)).inter
    ((isOpen_lt continuous_const (hs.add hz)).inter
    ((isOpen_lt continuous_const ((hs.add hw).add (continuous_const.mul hz))).inter
    ((isOpen_lt continuous_const (hw.add (continuous_const.mul hz))).inter
      (isOpen_lt continuous_const (hs.add (continuous_const.mul hz)))))))))


end HeckeSkeleton.HighBinContinuation
