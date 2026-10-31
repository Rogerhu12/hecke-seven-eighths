import Expansion.ActualFiniteHeightReciprocal
import Expansion.ActualModerateSweepHolomorphy

/-!
# Integrability of the actual selected moderate contour

The selected real coordinate a may lie to the left of the common packet
boundary.  The actual row detector nevertheless gives a zero-free
rectangle up to its selected upper height.  Its local reciprocal, the
entire nonprincipal numerator and the genuine Euler swept tube make the
original compensated kernel continuous at every retained height point.

Compactness then gives absolute Bochner integrability on the original
three-height box.  The line is exactly (a+16e, 1-a-6e, 17/50); its w
coordinate may be negative.  No global zero-free extension, reciprocal
bound, or integrability assumption is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

include nu in
/-- Joint differentiability at any point of the actual swept tube that
lies in the detected finite rectangle.  A norm pole in the denominator
is included with the original reciprocal's removable value. -/
theorem differentiableAt_actual_detected_kernel_comp [IsTotallyComplex K]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (ray : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {Z a e Hupper : ℝ} (hZ : 0 < Z)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hbelow : rowZeroBelow K Sset psi {1} P (arithmeticHighEulerData K Sset P psi)
      u Hupper (a + 2 * e))
    (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x)
    (hsre : a + 2 * e < (s x).re) (hheight : |(s x).im| ≤ Hupper)
    (hzre : 1 / 6 < (z x).re) (hregion : (s x, w x, z x) ∈ sweptTube a e) :
    DifferentiableAt ℂ (fun y => compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ray u Z (s y) (w y) (z y)) x := by
  let R := (arithmeticHighEulerData K Sset P psi).rows
  have hnon := rowCharacterInput_ne_normTwist_of_not_principal K Sset P R hAllowed u hu
  have hrec := differentiableAt_actual_row_reciprocal_of_rowZeroBelow K Sset psi P
    (arithmeticHighEulerData K Sset P psi) u Hupper (a + 2 * e)
    (by linarith) hbelow (s x) hsre hheight
  have hrec' := hrec.comp x hs
  have hLw := ((heckeEulerDeletionPolynomial_analyticAt K (R.character u)
    (exceptionalPrimes K Sset) (w x)).differentiableAt.fun_mul
      (differentiable_heckeContinuation_of_nonNorm K (R.character u) hnon (w x))).comp x hw
  have hzeta : 1 < (6 * z x).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hLz := ((heckeEulerDeletionPolynomial_analyticAt K 1
    (exceptionalPrimes K Sset) (6 * z x)).differentiableAt.fun_mul
      (analyticAt_heckeContinuation K 1 hzeta).differentiableAt).comp x
        ((differentiableAt_const _).fun_mul hz)
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive (z x)
    (by
      change 0 < (z x).re
      linarith only [hzre])).differentiableAt.comp x hz
  have hden := (HighBinBoundary.ActualDenominator.differentiable_mellin
    P.denominator.toSmoothAnnularTest (w x)).comp x hw
  have hN : (frequencyRowNorm K Sset u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealNorm_pos K u.ideal.val).ne'
  have hX : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hY : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hnPower := hz.neg.const_cpow (Or.inl hN)
  have hxPower : DifferentiableAt ℂ
      (fun y => ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z y)) x :=
    ((differentiableAt_const _).sub hz).const_cpow (Or.inl hX)
  have hzPower := ((hs.add hz).sub_const 1).const_cpow (Or.inl hZc)
  have hyPower := (hw.sub_const 1).const_cpow (Or.inl hY)
  have hexp := (((hs.add hz).sub_const 1).pow 2).cexp
  have hcorr := differentiableAt_actual_swept_fullCorrection_comp K S P psi g ray u Z
    ha ha1 he he1 s w z x hs hw hz hregion
  simp_rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g ray u Z hZ]
  simp only [div_eq_mul_inv]
  have hL := (hLz.fun_mul hLw).fun_mul hrec'
  exact ((((((((((differentiableAt_const _).fun_mul hexp).fun_mul hM).fun_mul hden).fun_mul hnPower).fun_mul hxPower).fun_mul
    hzPower).fun_mul hyPower).fun_mul hL).fun_mul hcorr).fun_mul (differentiableAt_const _)

include nu in
/-- Continuity on precisely the retained height box.  The zero detector
only needs its actual upper height, even when the selected a is below B. -/
theorem continuousOn_actual_shifted_rowVerticalKernel_box [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (ray : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {Z a e T Hupper : ℝ} (hZ : 0 < Z)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hTH : T ≤ Hupper)
    (hbelow : rowZeroBelow K Sset psi {1} P (arithmeticHighEulerData K Sset P psi)
      u Hupper (a + 2 * e)) :
    ContinuousOn (rowVerticalKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ray u Z
      (a + 16 * e) (1 - a - 6 * e) (17 / 50)) (rowRetainedHeightBox T) := by
  let point : (ℝ × ℝ × ℝ) → ℂ × ℂ × ℂ := fun t =>
    (((a + 16 * e : ℝ) : ℂ) + (t.1 : ℂ) * Complex.I,
      ((1 - a - 6 * e : ℝ) : ℂ) + (t.2.1 : ℂ) * Complex.I,
      ((17 / 50 : ℝ) : ℂ) + (t.2.2 : ℂ) * Complex.I)
  have hp : Continuous point := by dsimp only [point]; fun_prop
  intro t ht
  have hts : |t.1| ≤ Hupper := (abs_le.mpr ht.1).trans hTH
  have hsr : a + 2 * e < (point t).1.re := by simp only [point]; simp; linarith
  have hsi : |(point t).1.im| ≤ Hupper := by simpa [point] using hts
  have hzr : 1 / 6 < (point t).2.2.re := by norm_num [point]
  have hregion : point t ∈ sweptTube a e := by
    change a + 15 * e < (point t).1.re ∧
      1 - a - 7 * e < (point t).2.1.re ∧ 17 / 50 - e < (point t).2.2.re
    simp only [point]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hk := differentiableAt_actual_detected_kernel_comp K S mu nu P psi hAllowed
    g ray u hu hZ ha ha1 he he1 hbelow
    Prod.fst (fun v : ℂ × ℂ × ℂ => v.2.1) (fun v : ℂ × ℂ × ℂ => v.2.2) (point t)
    differentiableAt_fst (differentiableAt_fst.comp _ differentiableAt_snd)
    (differentiableAt_snd.comp _ differentiableAt_snd) hsr hsi hzr hregion
  exact (hk.continuousAt.comp hp.continuousAt).continuousWithinAt

include nu in
/-- Absolute Bochner integrability of every selected original row on
the actual final height box, before any label partition is introduced. -/
theorem integrableOn_actual_shifted_rowVerticalKernel_box [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (ray : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {Z a e T Hupper : ℝ} (hZ : 0 < Z)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hTH : T ≤ Hupper)
    (hbelow : rowZeroBelow K Sset psi {1} P (arithmeticHighEulerData K Sset P psi)
      u Hupper (a + 2 * e)) :
    IntegrableOn (rowVerticalKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ray u Z
      (a + 16 * e) (1 - a - 6 * e) (17 / 50))
      (rowRetainedHeightBox T) rowHeightVolume := by
  unfold rowHeightVolume
  exact (continuousOn_actual_shifted_rowVerticalKernel_box K S mu nu P psi hAllowed g ray u hu
    hZ ha ha1 he he1 hTH hbelow).integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

end Expansion.Project

#print axioms Expansion.Project.differentiableAt_actual_detected_kernel_comp
#print axioms Expansion.Project.continuousOn_actual_shifted_rowVerticalKernel_box
#print axioms Expansion.Project.integrableOn_actual_shifted_rowVerticalKernel_box
