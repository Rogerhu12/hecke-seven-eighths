import HeckeGeneral.Analysis.TInputRanges
import HeckeSkeleton.HighBinSupport.ActualRegularEuler
import HeckeSkeleton.HighBinSupport.EulerCorrectedRegion
import HeckeSkeleton.HighBinSupport.EulerRegionAnalytic
import HeckeSkeleton.HighBinSupport.ActualEulerProduct

/-!
# The original corrected Euler region: actual product convergence

All five summability faces give a positive margin at every point of the
repository's `rowEulerRegion`. Actual ideal counting then proves the
`local_product` conclusion of `TRowEulerInput`, with arbitrary finite
exceptional tables and marks. Finite zero factors are retained.

This is a product-convergence theorem. It does not replace the separate
three-variable `AnalyticOnNhd` or initial Fourier-calibration obligations.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinActualEuler
open scoped Classical Topology BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Actual convergence on the exact region of the original Euler input.
The finite exceptional tables need no nonvanishing or size hypothesis. -/
theorem rowCorrection_multipliable_rowEulerRegion
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    Multipliable (fun p : ExteriorPrime K S =>
      if hp : p ∈ rowExceptionalPrimes K S Q u then
        finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
          (p.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2
      else localRowCorrection K S P ψ (E.rows.character u) p v.1 v.2.1 v.2.2) := by
  obtain ⟨δ, hδ, h1, h2, h3, h4, h5⟩ := exists_region_margin v.1 v.2.1 v.2.2 hv
  have hprime : Summable (fun p : ExteriorPrime K S =>
      (p.val.asIdeal.absNorm : ℝ) ^ (-1 - δ)) := by
    have h := summable_exteriorPrime_norm_rpow K S (σ := 1 + δ) (by linarith)
    convert h using 1
    funext p
    congr 1
    ring
  have hmajor := hprime.mul_left (11 / sweptTubeEulerMargin)
  let f : ExteriorPrime K S → ℂ := fun p =>
    if hp : p ∈ rowExceptionalPrimes K S Q u then
      finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) v.1 v.2.1 v.2.2
    else localRowCorrection K S P ψ (E.rows.character u) p v.1 v.2.1 v.2.2
  have hnorm : Summable (fun p => ‖f p - 1‖) := by
    apply hmajor.of_norm_bounded_eventually
    filter_upwards [(rowExceptionalPrimes K S Q u).finite_toSet.compl_mem_cofinite]
      with p hp
    have hb := phaseRowEuler_region_bound (exteriorPrime_norm_two_le K S p) hδ.le
      (primeCoefficient K (E.rows.character u) p.val)
      (primeCoefficient K ψ p.val * conj (primeCoefficient K (E.rows.character u) p.val))
      (primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6) v.1 v.2.1 v.2.2
      (norm_primeCoefficient_le_one K _ p.val)
      (actualEuler_D_phase_norm K S ψ (E.rows.character u) p)
      (actualEuler_E_phase_norm K S P ψ p) hv.1.le hv.2.1.le hv.2.2.1.le
      h1 h2 h3 h4 h5
    simpa only [f, dif_neg hp, norm_norm, localRowCorrection_eq_phase] using hb
  have hm := multipliable_one_add_of_summable hnorm
  have hident : (fun p => (1 : ℂ) + (f p - 1)) = f := by
    funext p
    ring
  rw [hident] at hm
  exact hm

/-- The finite Laurent tables agree with all four explicit local branches
on the whole original Euler region, including points outside every high
swept tube used in the contour argument. -/
theorem localFactor_eq_explicit_rowEulerRegion (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) (v : ℂ × ℂ × ℂ) (hv : v ∈ rowEulerRegion) :
    localFactor K S P ψ Q u p v =
      explicitLocalEuler (exteriorSupport K S u.ideal) Q
        (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
        (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
        (rowPhaseData K S P ψ u) (rowIndex K S u) p v := by
  have hq := exteriorPrime_norm_two_le K S p
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by linarith
  have hq1 : (1 : ℝ) < p.val.asIdeal.absNorm := by linarith
  have hs : 0 < v.1.re := lt_trans (by norm_num) hv.1
  have hsz : 2 / 3 < v.1.re + v.2.2.re := lt_trans (by norm_num) hv.2.2.2.2.1
  by_cases hR : p ∈ exteriorSupport K S u.ideal
  · have hp : p ∈ rowExceptionalPrimes K S Q u := Finset.mem_union_left Q hR
    have hden : 1 - coordR (rowPhaseData K S P ψ u p)
        (p.val.asIdeal.absNorm : ℝ) v.1 v.2.2 ≠ 0 := by
      have hn := coordR_norm_lt_one_of_re (rowPhaseData K S P ψ u p) hq1 v.1 v.2.2 hsz
      intro h
      have h' := (sub_eq_zero.mp h).symm
      simpa [h'] using hn
    have hvalue := HighBinFiniteTables.ramified_value (rowPhaseData K S P ψ u p)
      (p.val.asIdeal.absNorm : ℝ) hq0 v.1 v.2.1 v.2.2
      (rowRamifiedIndex K S u p hR) (decide (p ∈ Q)) hden
    by_cases hQ : p ∈ Q
    · simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowIndex, hp, hR, hQ] using hvalue
    · simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowIndex, hp, hR, hQ] using hvalue
  · by_cases hQ : p ∈ Q
    · have hp : p ∈ rowExceptionalPrimes K S Q u :=
        Finset.mem_union_right (exteriorSupport K S u.ideal) hQ
      have hden := phaseRowEuler_denominators_ne_zero_of_re hq1
        (rowD K S P ψ u p) (rowE K S P ψ p) v.1 v.2.2
        (rowD_norm K S P ψ u p) (rowE_norm K S P ψ p) hs hsz
      have hvalue := HighBinFiniteTables.regular_value (p.val.asIdeal.absNorm : ℝ) hq0
        (rowW K S P u p) (rowD K S P ψ u p) (rowE K S P ψ p)
        v.1 v.2.1 v.2.2 true hden.1 hden.2
      simpa [localFactor, arithmeticHighEulerData, exceptionalFactor, explicitLocalEuler,
        rowW, rowD, rowE, hp, hR, hQ] using hvalue
    · have hp : p ∉ rowExceptionalPrimes K S Q u := by
        simp only [rowExceptionalPrimes, Finset.mem_union, not_or, hR, hQ, and_self]
      simpa only [localFactor, dif_neg hp, explicitLocalEuler, if_neg hR, if_neg hQ,
        sub_zero, rowW, rowD, rowE] using
        localRowCorrection_eq_phase K S P ψ (arithmeticRowCharacter K S P u)
          p v.1 v.2.1 v.2.2

/-- Actual local joint analyticity on the exact original Euler region.
This establishes the local input for a normal-product argument; it does
not assert joint analyticity of the infinite product. -/
theorem localFactor_analyticOnNhd_rowEulerRegion
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) :
    AnalyticOnNhd ℂ (localFactor K S P ψ Q u p) rowEulerRegion := by
  have hq : ∀ p : ExteriorPrime K S, (1 : ℝ) < p.val.asIdeal.absNorm := by
    intro p
    have h := exteriorPrime_norm_two_le K S p
    linarith
  have h := explicitLocalEuler_analyticOnNhd_positiveRegion
    (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u) hq
    (rowD_norm K S P ψ u) (rowE_norm K S P ψ) p
  have hsub : rowEulerRegion ⊆ {v : ℂ × ℂ × ℂ |
      0 < v.1.re ∧ 2 / 3 < v.1.re + v.2.2.re} := by
    intro v hv
    exact ⟨lt_trans (by norm_num) hv.1, lt_trans (by norm_num) hv.2.2.2.2.1⟩
  apply AnalyticOnNhd.congr rowEulerRegion_isOpen (h.mono hsub)
  intro v hv
  exact (localFactor_eq_explicit_rowEulerRegion K S P ψ Q u p v hv).symm

/-- Normal convergence of the complete actual marked Euler product on
the entire original region. Each point has a positive common distance
from all five summability faces; no global lower bound on that distance
is imposed. Exceptional zero factors remain in the finite product. -/
theorem rowCorrection_hasProdLocallyUniformlyOn_rowEulerRegion
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    HasProdLocallyUniformlyOn (localFactor K S P ψ Q u)
      (fun v : ℂ × ℂ × ℂ => rowCorrection K S P ψ
        (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2)
      rowEulerRegion := by
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
      HasProdLocallyUniformlyOn (localFactor K S P ψ Q u)
        (fun v => ∏' p : ExteriorPrime K S, localFactor K S P ψ Q u p v) (U δ) := by
    have hprime : Summable (fun p : ExteriorPrime K S =>
        (p.val.asIdeal.absNorm : ℝ) ^ (-1 - δ)) := by
      have h := summable_exteriorPrime_norm_rpow K S (σ := 1 + δ) (by linarith)
      convert h using 1
      funext p
      congr 1
      ring
    have hmajor := hprime.mul_left (11 / sweptTubeEulerMargin)
    have hbound : ∀ᶠ p : ExteriorPrime K S in cofinite,
        ∀ v ∈ U δ, ‖localFactor K S P ψ Q u p v - 1‖ ≤
          (11 / sweptTubeEulerMargin) * (p.val.asIdeal.absNorm : ℝ) ^ (-1 - δ) := by
      filter_upwards [(rowExceptionalPrimes K S Q u).finite_toSet.compl_mem_cofinite]
        with p hp v hv
      rcases hv with ⟨hv, h1, h2, h3, h4, h5⟩
      have hb := phaseRowEuler_region_bound (exteriorPrime_norm_two_le K S p) hδ.le
        (rowW K S P u p) (rowD K S P ψ u p) (rowE K S P ψ p)
        v.1 v.2.1 v.2.2 (rowW_norm K S P u p)
        (rowD_norm K S P ψ u p) (rowE_norm K S P ψ p)
        hv.1.le hv.2.1.le hv.2.2.1.le h1.le h2.le h3.le h4.le h5.le
      simpa only [localFactor, dif_neg hp, localRowCorrection_eq_phase, rowW, rowD, rowE]
        using hb
    have h := Summable.hasProdLocallyUniformlyOn_one_add (hUopen δ) hmajor
      (f := fun p v => localFactor K S P ψ Q u p v - 1) hbound
      (fun p => ((localFactor_analyticOnNhd_rowEulerRegion K S P ψ Q u p).continuousOn.mono
        (fun _ hv => hv.1)).sub continuousOn_const)
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
  change HasProdLocallyUniformlyOn (localFactor K S P ψ Q u)
    (fun v => ∏' p : ExteriorPrime K S, localFactor K S P ψ Q u p v) rowEulerRegion
  rw [hcover]
  exact tendstoLocallyUniformlyOn_iUnion (fun δ => hUopen δ.val)
    (fun δ => hprod δ.val δ.property)

theorem rowCorrection_continuousOn_rowEulerRegion
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    ContinuousOn (fun v : ℂ × ℂ × ℂ => rowCorrection K S P ψ
      (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2) rowEulerRegion := by
  have h := rowCorrection_hasProdLocallyUniformlyOn_rowEulerRegion K S P ψ Q u
  apply TendstoLocallyUniformlyOn.continuousOn h
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun F =>
    (F.analyticOnNhd_fun_prod (fun p _ =>
      localFactor_analyticOnNhd_rowEulerRegion K S P ψ Q u p)).continuousOn

end HeckeSkeleton.HighBinContinuation
