import HeckeSkeleton.HighBinSupport.ActualNormFormMellinInversion
import HeckeGeneral.Analysis.PrimeWindowGeometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Uniform Mellin seminorms for the genuine logarithm-removal test.

For P ≥ 2 we write h = 1/log P. The profile is h V(y)/(1+h log y),
where h ranges over a fixed compact interval. Joint smoothness of this
family and all its Euler derivatives gives fixed bounds on [1,2]. The
repository's actual Euler integration-by-parts estimate then gives rapid
Mellin decay with a constant chosen before P and the vertical height.
-/

noncomputable section
namespace HighBinVerified.NormFormMellin

open MeasureTheory Complex Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Topology ContDiff BigOperators

def compactLogProfile (V : SmoothAnnularTest) (h y : ℝ) : ℂ :=
  (h : ℂ) * V.toFun y / ((1 + h * Real.log y : ℝ) : ℂ)

def logProfileDomain : Set (ℝ × ℝ) :=
  {q | 0 < q.2 ∧ 1 + q.1 * Real.log q.2 ≠ 0}

theorem isOpen_logProfileDomain : IsOpen logProfileDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hy : ∀ᶠ r : ℝ × ℝ in 𝓝 q, 0 < r.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hq.1
  have hd : ContinuousAt (fun r : ℝ × ℝ => 1 + r.1 * Real.log r.2) q :=
    continuousAt_const.add (continuousAt_fst.mul
      (continuousAt_snd.log hq.1.ne'))
  exact hy.and (hd.eventually_ne hq.2)

theorem contDiffOn_compactLogProfile (V : SmoothAnnularTest) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => compactLogProfile V q.1 q.2)
      logProfileDomain := by
  intro q hq
  have hh : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => (r.1 : ℂ)) q :=
    (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).contDiffAt.comp q contDiffAt_fst
  have hv : ContDiffAt ℝ ∞ (fun r : ℝ × ℝ => V.toFun r.2) q :=
    V.smooth.contDiffAt.comp q contDiffAt_snd
  have hd : ContDiffAt ℝ ∞
      (fun r : ℝ × ℝ => ((1 + r.1 * Real.log r.2 : ℝ) : ℂ)) q :=
    (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).contDiffAt.comp q
      (contDiffAt_const.add (contDiffAt_fst.mul (contDiffAt_snd.log hq.1.ne')))
  have hd0 : ((1 + q.1 * Real.log q.2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hq.2
  have h := (hh.mul hv).mul (hd.inv hd0)
  simpa only [compactLogProfile, div_eq_mul_inv] using h.contDiffWithinAt

def jointLogEuler (V : SmoothAnnularTest) (j : ℕ) (q : ℝ × ℝ) : ℂ :=
  eulerDerivativeOrder j (compactLogProfile V q.1) q.2

/-- Joint regularity is retained by each actual Euler operator y d/dy. -/
theorem contDiffOn_jointLogEuler (V : SmoothAnnularTest) (j : ℕ) :
    ContDiffOn ℝ ∞ (jointLogEuler V j) logProfileDomain := by
  induction j with
  | zero =>
      simpa only [jointLogEuler, eulerDerivativeOrder, Function.iterate_zero_apply]
        using contDiffOn_compactLogProfile V
  | succ j ih =>
      have hy : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (q.2 : ℂ)) logProfileDomain :=
        ((Complex.ofRealCLM.contDiff (𝕜 := ℝ)).comp contDiff_snd).contDiffOn
      have hd : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
          fderiv ℝ (jointLogEuler V j) q (0, 1)) logProfileDomain :=
        (ih.fderiv_of_isOpen isOpen_logProfileDomain (by simp)).clm_apply contDiffOn_const
      apply (hy.mul hd).congr
      intro q hq
      have hdiff : DifferentiableAt ℝ (jointLogEuler V j) q :=
        ((ih q hq).contDiffAt (isOpen_logProfileDomain.mem_nhds hq)).differentiableAt
          (by simp)
      have hline : HasDerivAt (fun y : ℝ => (q.1, y)) (0, 1) q.2 :=
        (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
      have hderiv : deriv (eulerDerivativeOrder j (compactLogProfile V q.1)) q.2 =
          fderiv ℝ (jointLogEuler V j) q (0, 1) := by
        simpa only [Function.comp_def, jointLogEuler] using
          (hdiff.hasFDerivAt.comp_hasDerivAt q.2 hline).deriv
      change eulerDerivativeOrder (j + 1) (compactLogProfile V q.1) q.2 = _
      rw [eulerDerivativeOrder_succ, hderiv]

theorem divideLogProfile_eq_compactLogProfile (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    {P : ℝ} (hP : 2 ≤ P) :
    divideLogProfile V P = compactLogProfile V (Real.log P)⁻¹ := by
  funext y
  by_cases hy : V.toFun y = 0
  · simp only [divideLogProfile, compactLogProfile, hy, mul_zero, zero_div]
  have hy1 : 1 < y := (hann hy).1
  have hP1 : 1 < P := by linarith
  have hP0 : 0 < P := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 0 < Real.log P := Real.log_pos hP1
  have hY : 0 ≤ Real.log y := (Real.log_pos hy1).le
  have hsum : (Real.log P + Real.log y : ℂ) ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg hL hY).ne'
  have hden : ((1 + (Real.log P)⁻¹ * Real.log y : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have := mul_nonneg (inv_nonneg.mpr hL.le) hY
    linarith
  have hLc : (Real.log P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  simp only [divideLogProfile, compactLogProfile, Real.log_mul hP0.ne' hy0.ne',
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_one]
  push_cast at hden
  field_simp [hLc, hsum, hden] <;> ring

/-- Every Euler seminorm of the divided test is uniform over P ≥ 2. -/
theorem exists_uniform_divideLog_euler_bound (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : ℝ), 2 ≤ P → ∀ y ∈ Icc (1 : ℝ) 2,
      ‖eulerDerivativeOrder j (divideLogProfile V P) y‖ ≤ B := by
  let Q : Set (ℝ × ℝ) := Icc (0 : ℝ) (Real.log 2)⁻¹ ×ˢ Icc (1 : ℝ) 2
  have hQU : Q ⊆ logProfileDomain := by
    intro q hq
    have hlog : 0 ≤ Real.log q.2 := Real.log_nonneg hq.2.1
    have hmul : 0 ≤ q.1 * Real.log q.2 := mul_nonneg hq.1.1 hlog
    exact ⟨by linarith [hq.2.1], by linarith⟩
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn
    ((contDiffOn_jointLogEuler V j).continuousOn.mono hQU)
  refine ⟨max 0 B + 1, by have := le_max_left (0 : ℝ) B; linarith, ?_⟩
  intro P hP y hy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hh : (Real.log P)⁻¹ ∈ Icc (0 : ℝ) (Real.log 2)⁻¹ := by
    refine ⟨inv_nonneg.mpr (hlog2.le.trans hlogP), ?_⟩
    simpa only [one_div] using one_div_le_one_div_of_le hlog2 hlogP
  rw [divideLogProfile_eq_compactLogProfile V hann hP]
  exact (hB ((Real.log P)⁻¹, y) ⟨hh, hy⟩).trans
    ((le_max_right _ _).trans (by linarith))

/-- The weighted integral seminorms used by the actual Mellin proof have
constants independent of the prime scale. -/
theorem exists_uniform_divideLog_Iint_bound (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2) (j : ℕ) (sigma : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 2 ≤ P),
      Iint (divideLogTest V hann P (by linarith)) j sigma ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_divideLog_euler_bound V hann j
  let W : ℝ := ∫ y in Icc (1 : ℝ) 2, y ^ (-sigma - 1)
  have hW : 0 ≤ W := setIntegral_nonneg measurableSet_Icc
    (fun y hy => Real.rpow_nonneg (by linarith [hy.1]) _)
  refine ⟨B * W + 1, by have := mul_nonneg hB.le hW; linarith, ?_⟩
  intro P hP
  let Vp := divideLogTest V hann P (show 1 < P by linarith)
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := fun y hy => by linarith [hy.1]
  have heq : Iint Vp j sigma =
      ∫ y in Icc (1 : ℝ) 2, ‖eul Vp j y‖ * y ^ (-sigma - 1) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    intro y hy
    rw [(good_eul Vp j).zero y hy.2, norm_zero, zero_mul]
  have hw : ContinuousOn (fun y : ℝ => y ^ (-sigma - 1)) (Icc (1 : ℝ) 2) := by
    intro y hy
    exact (Real.continuousAt_rpow_const y (-sigma - 1)
      (Or.inl (by linarith [hy.1]))).continuousWithinAt
  calc
    Iint Vp j sigma = _ := heq
    _ ≤ ∫ y in Icc (1 : ℝ) 2, B * y ^ (-sigma - 1) := by
      apply setIntegral_mono_on ((integrableOn_Iint Vp j sigma).mono_set hsub)
        (hw.integrableOn_Icc.const_mul B) measurableSet_Icc
      intro y hy
      exact mul_le_mul_of_nonneg_right (hbound P hP y hy)
        (Real.rpow_nonneg (by linarith [hy.1]) _)
    _ = B * W := integral_const_mul B _
    _ ≤ B * W + 1 := by linarith

/-- Uniform rapid decay in every fixed real strip, with the scale P
quantified after the Mellin constant. -/
theorem exists_uniform_divideLog_mellin_bound (V : SmoothAnnularTest)
    (hann : Function.support V.toFun ⊆ Ioo (1 : ℝ) 2)
    (lower upper : ℝ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : ℝ), 2 ≤ P → ∀ sigma t : ℝ,
      lower ≤ sigma → sigma ≤ upper →
      (1 + |t|) ^ n * ‖mellin (divideLogProfile V P) ((sigma : ℂ) + t * I)‖ ≤ D := by
  obtain ⟨C0l, hC0l, h0l⟩ := exists_uniform_divideLog_Iint_bound V hann 0 (-upper)
  obtain ⟨C0u, hC0u, h0u⟩ := exists_uniform_divideLog_Iint_bound V hann 0 (-lower)
  obtain ⟨Cnl, hCnl, hnl⟩ := exists_uniform_divideLog_Iint_bound V hann n (-upper)
  obtain ⟨Cnu, hCnu, hnu⟩ := exists_uniform_divideLog_Iint_bound V hann n (-lower)
  refine ⟨2 ^ n * ((C0l + C0u) + (Cnl + Cnu)),
    mul_pos (by positivity) (by linarith), ?_⟩
  intro P hP sigma t hlo hhi
  let Vp := divideLogTest V hann P (show 1 < P by linarith)
  have hraw := pow_mul_norm_mellin_le Vp n (-sigma) (-t)
  have heq : -(((-sigma : ℝ) : ℂ) + (-t : ℝ) * I) = (sigma : ℂ) + t * I := by
    push_cast
    ring
  rw [heq] at hraw
  have ht : |t| ≤ ‖((-sigma : ℝ) : ℂ) + (-t : ℝ) * I‖ := by
    simpa using Complex.abs_im_le_norm (((-sigma : ℝ) : ℂ) + (-t : ℝ) * I)
  have h0 := Iint_strip_le Vp 0 (show -upper ≤ -sigma by linarith)
    (show -sigma ≤ -lower by linarith)
  have hn := Iint_strip_le Vp n (show -upper ≤ -sigma by linarith)
    (show -sigma ≤ -lower by linarith)
  calc
    _ ≤ (1 + ‖((-sigma : ℝ) : ℂ) + (-t : ℝ) * I‖) ^ n *
        ‖mellin Vp.toFun ((sigma : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) n) (norm_nonneg _)
    _ ≤ 2 ^ n * (Iint Vp 0 (-sigma) + Iint Vp n (-sigma)) := hraw
    _ ≤ 2 ^ n * ((C0l + C0u) + (Cnl + Cnu)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (h0.trans (add_le_add (h0l P hP) (h0u P hP)))
        (hn.trans (add_le_add (hnl P hP) (hnu P hP)))

/-- Uniformity also holds over all original prime-window profiles. -/
theorem exists_primeWindow_divideLog_mellin_bound (g : PrimeWindowGeometry)
    (lower upper : ℝ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin g.slots) (P : ℝ), 2 ≤ P → ∀ sigma t : ℝ,
      lower ≤ sigma → sigma ≤ upper →
      (1 + |t|) ^ n *
        ‖mellin (divideLogProfile (g.weight i) P) ((sigma : ℂ) + t * I)‖ ≤ D := by
  have hi := fun i : Fin g.slots =>
    exists_uniform_divideLog_mellin_bound (g.weight i) (g.support_annular i) lower upper n
  choose D hD hbound using hi
  have hsum : 0 ≤ ∑ i : Fin g.slots, D i := Finset.sum_nonneg (fun i _ => (hD i).le)
  refine ⟨1 + ∑ i : Fin g.slots, D i, by linarith, ?_⟩
  intro i P hP sigma t hlo hhi
  exact (hbound i P hP sigma t hlo hhi).trans
    ((Finset.single_le_sum (fun j _ => (hD j).le) (Finset.mem_univ i)).trans
      (by linarith))

end HighBinVerified.NormFormMellin

#print axioms HighBinVerified.NormFormMellin.exists_uniform_divideLog_euler_bound
#print axioms HighBinVerified.NormFormMellin.exists_uniform_divideLog_mellin_bound
#print axioms HighBinVerified.NormFormMellin.exists_primeWindow_divideLog_mellin_bound
