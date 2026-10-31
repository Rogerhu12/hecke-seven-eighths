import HeckeGeneral.Analysis.TInputRanges
import HeckeSkeleton.HighBinSupport.ActualRegularEuler
import HeckeSkeleton.HighBinSupport.EulerCorrectedRegion
import HeckeSkeleton.HighBinSupport.EulerRegionAnalytic
import HeckeSkeleton.HighBinSupport.ActualEulerProduct
import HeckeSkeleton.HighBinSupport.EulerRegionProduct

/-!
# The original corrected Euler region: convergence and joint analyticity

All five summability faces give a positive margin at every point of the
repository's `rowEulerRegion`. Actual ideal counting then proves the
`local_product` conclusion of `TRowEulerInput`, with arbitrary finite
exceptional tables and marks. Finite zero factors are retained.

The locally uniform product of the actual finite factors gives joint
three-variable `AnalyticOnNhd` on this region. Initial Fourier calibration
is supplied separately by `ActualInitialCalibration`.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinContinuation

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
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
    have hp' : p ∉ rowExceptionalPrimes K S Q u := hp
    have hf : f p = localRowCorrection K S P ψ (E.rows.character u) p
        v.1 v.2.1 v.2.2 := by
      dsimp only [f]
      exact dif_neg hp'
    have hb := phaseRowEuler_region_bound (exteriorPrime_norm_two_le K S p) hδ.le
      (primeCoefficient K (E.rows.character u) p.val)
      (primeCoefficient K ψ p.val * conj (primeCoefficient K (E.rows.character u) p.val))
      (primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6) v.1 v.2.1 v.2.2
      (norm_primeCoefficient_le_one K _ p.val)
      (actualEuler_D_phase_norm K S ψ (E.rows.character u) p)
      (actualEuler_E_phase_norm K S P ψ p) hv.1.le hv.2.1.le hv.2.2.1.le
      h1 h2 h3 h4 h5
    simpa only [hf, norm_norm, localRowCorrection_eq_phase] using hb
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
        simp only [rowExceptionalPrimes, Finset.mem_union, not_or]
        exact ⟨hR, hQ⟩
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
  have h := explicitEuler_hasProdLocallyUniformlyOn_rowEulerRegion
    (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) (rowW_norm K S P u)
    (rowD_norm K S P ψ u) (rowE_norm K S P ψ)
    (fun σ hσ => summable_exteriorPrime_norm_rpow K S (σ := σ) hσ)
  have hfinite : ∀ F : Finset (ExteriorPrime K S), rowEulerRegion.EqOn
      (fun v => ∏ p ∈ F, explicitLocalEuler (exteriorSupport K S u.ideal) Q
        (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
        (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
        (rowPhaseData K S P ψ u) (rowIndex K S u) p v)
      (fun v => ∏ p ∈ F, localFactor K S P ψ Q u p v) := by
    intro F v hv
    apply Finset.prod_congr rfl
    intro p _
    exact (localFactor_eq_explicit_rowEulerRegion K S P ψ Q u p v hv).symm
  apply TendstoLocallyUniformlyOn.congr_right
    (TendstoLocallyUniformlyOn.congr h hfinite)
  intro v hv
  change (∏' p : ExteriorPrime K S, explicitLocalEuler (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P ψ u) (rowE K S P ψ)
    (rowPhaseData K S P ψ u) (rowIndex K S u) p v) =
      ∏' p : ExteriorPrime K S, localFactor K S P ψ Q u p v
  exact tprod_congr (fun p =>
    (localFactor_eq_explicit_rowEulerRegion K S P ψ Q u p v hv).symm)

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

/-- Joint analyticity of the actual Euler correction, including its
finite zero factors, on the exact original three-variable region. -/
theorem rowCorrection_analyticOnNhd_rowEulerRegion
    (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => rowCorrection K S P ψ
      (arithmeticHighEulerData K S P ψ) Q u v.1 v.2.1 v.2.2) rowEulerRegion := by
  apply HighBinJointAnalytic.analyticOnNhd_of_tendstoLocallyUniformlyOn
    (rowCorrection_hasProdLocallyUniformlyOn_rowEulerRegion K S P ψ Q u)
    ?_ rowEulerRegion_isOpen
  exact Filter.Eventually.of_forall fun F =>
    F.analyticOnNhd_fun_prod (fun p _ =>
      localFactor_analyticOnNhd_rowEulerRegion K S P ψ Q u p)

end HeckeSkeleton.HighBinContinuation
