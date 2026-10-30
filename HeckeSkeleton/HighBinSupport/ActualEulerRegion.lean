import HeckeGeneral.Analysis.TInputRanges
import HeckeSkeleton.HighBinSupport.ActualRegularEuler
import HeckeSkeleton.HighBinSupport.EulerCorrectedRegion

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
open scoped Classical Topology BigOperators ComplexConjugate

private theorem exists_region_margin (s w z : ℂ)
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

private theorem phaseRowEuler_region_bound
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

end HeckeSkeleton.HighBinContinuation
