import HeckeSkeleton.ExpansionModels.ActualMellinRegularity
import HeckeSkeleton.HighBinSupport.ActualEulerRegion
import HeckeGeneral.Analysis.CompensatedRowKernelFactorization
import HeckeGeneral.Analysis.TInputFixedBinTransfer
import HeckeGeneral.Analysis.FixedBinPointwiseIntegration

/-!
# Actual row kernels on the original absolute contours

The literal finite-window correction is continuous after composition with
continuous parameters in the proved Euler region.  Above the absolute
L-series lines, actual nonvanishing and the positive Mellin regularity
therefore make the entire original compensated kernel continuous.

Compactness proves both joint integrability on every retained height box
and all three sequential integrability conditions for its original
iterated contour integral.  The assertions retain every original row and
all finite compensation terms, with the corrected Poisson scalar.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.KernelRegularity

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The actual correction is a finite sum of continuous powers and actual
Euler products on their proved joint region. -/
theorem continuous_actual_fullCorrection_comp
    {X : Type*} [TopologicalSpace X]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (s w z : X → ℂ)
    (hs : Continuous s) (hw : Continuous w) (hz : Continuous z)
    (hregion : ∀ x, (s x, w x, z x) ∈ rowEulerRegion) :
    Continuous (fun x => compensatedRowFullCorrection K Sset P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z (s x) (w x) (z x)) := by
  unfold compensatedRowFullCorrection
  apply continuous_finsetSum
  intro p _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro J _
  dsimp only
  have hsel : (exteriorNorm K Sset (subsetPrimeIdeal K Sset p J) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealNorm_pos K (subsetPrimeIdeal K Sset p J).val).ne'
  have hmark :
      (exteriorNorm K Sset (subsetPrimeIdeal K Sset p (Finset.univ \ J)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (idealNorm_pos K (subsetPrimeIdeal K Sset p (Finset.univ \ J)).val).ne'
  have hspow := ((hz.sub hw).sub_const 1).const_cpow (Or.inl hsel)
  have hmpow := ((hs.add hz).sub_const 1).const_cpow (Or.inl hmark)
  have hcor := (rowCorrection_continuousOn_rowEulerRegion K Sset P psi
    ((Finset.univ \ J).image p) u).comp_continuous
      (hs.prodMk (hw.prodMk hz)) hregion
  exact (((continuous_const.mul hspow).mul continuous_const).mul hmpow).mul hcor

private theorem continuous_deletedContinuation_comp_right
    {X : Type*} [TopologicalSpace X]
    (chi : HeckeCharacter K) (D : Finset (HeightOneSpectrum (𝓞 K)))
    (f : X → ℂ) (hf : Continuous f) (hright : ∀ x, 1 < (f x).re) :
    Continuous (fun x => heckeDeletedContinuation K chi D (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((heckeEulerDeletionPolynomial_analyticAt K chi D (f x)).continuousAt.mul
    (analyticAt_heckeContinuation K chi (hright x)).continuousAt).comp hf.continuousAt

private theorem deletedContinuation_ne_zero_right
    (chi : HeckeCharacter K) (D : Finset (HeightOneSpectrum (𝓞 K)))
    (s : ℂ) (hs : 1 < s.re) : heckeDeletedContinuation K chi D s ≠ 0 :=
  mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K chi D (zero_lt_one.trans hs))
    (heckeContinuation_ne_zero K chi hs)

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)

include nu

/-- Joint continuity on the entire three-dimensional space of heights.
The real coordinates include both the original (5,5,3) contours and the
large-row (2,2,1+3/zeta) contours. -/
theorem continuous_actual_rowVerticalKernel_absolute [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (hZ : 0 < Z)
    (sLine wLine zLine : ℝ) (hsLine : 1 < sLine) (hwLine : 1 < wLine)
    (hzLine : 1 / 6 < zLine) :
    Continuous (rowVerticalKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z sLine wLine zLine) := by
  let s : (ℝ × ℝ × ℝ) → ℂ := fun t => (sLine : ℂ) + (t.1 : ℂ) * Complex.I
  let w : (ℝ × ℝ × ℝ) → ℂ := fun t => (wLine : ℂ) + (t.2.1 : ℂ) * Complex.I
  let z : (ℝ × ℝ × ℝ) → ℂ := fun t => (zLine : ℂ) + (t.2.2 : ℂ) * Complex.I
  have hs : Continuous s := by dsimp only [s]; fun_prop
  have hw : Continuous w := by dsimp only [w]; fun_prop
  have hz : Continuous z := by dsimp only [z]; fun_prop
  have hsre (t : ℝ × ℝ × ℝ) : (s t).re = sLine := by simp [s]
  have hwre (t : ℝ × ℝ × ℝ) : (w t).re = wLine := by simp [w]
  have hzre (t : ℝ × ℝ × ℝ) : (z t).re = zLine := by simp [z]
  have hregion (t : ℝ × ℝ × ℝ) : (s t, w t, z t) ∈ rowEulerRegion := by
    simp only [rowEulerRegion, Set.mem_setOf_eq, hsre, hwre, hzre]
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  have hcorr := continuous_actual_fullCorrection_comp K S P psi g T u Z s w z hs hw hz hregion
  have hM : Continuous (fun t => additiveMellin K Sset muS P.additive (z t)) :=
    (continuous_actual_additiveMellin_line K S mu nu P.additive
      (show 0 < zLine by linarith)).comp (continuous_snd.comp continuous_snd)
  have hden : Continuous (fun t => mellin P.denominator.toFun (w t)) :=
    (HighBinBoundary.ActualDenominator.differentiable_mellin P.denominator.toSmoothAnnularTest).continuous.comp hw
  have hN : (frequencyRowNorm K Sset u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealNorm_pos K u.ideal.val).ne'
  have hX : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hY : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hnPower := hz.neg.const_cpow (Or.inl hN)
  have hxPower : Continuous (fun t =>
      ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z t)) :=
    (continuous_const.sub hz).const_cpow (Or.inl hX)
  have hzPower := ((hs.add hz).sub_const 1).const_cpow (Or.inl hZc)
  have hyPower := (hw.sub_const 1).const_cpow (Or.inl hY)
  have hexp := Complex.continuous_exp.comp (((hs.add hz).sub_const 1).pow 2)
  have hLz := continuous_deletedContinuation_comp_right K 1 (exceptionalPrimes K Sset)
    (fun t => 6 * z t) (continuous_const.mul hz) (fun t => by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, hzre]
      linarith)
  have hLw := continuous_deletedContinuation_comp_right K
    ((arithmeticHighEulerData K Sset P psi).rows.character u) (exceptionalPrimes K Sset)
    w hw (fun t => by rw [hwre]; exact hwLine)
  have hLs := continuous_deletedContinuation_comp_right K
    (psi * conjugate ((arithmeticHighEulerData K Sset P psi).rows.character u))
    (exceptionalPrimes K Sset) s hs (fun t => by rw [hsre]; exact hsLine)
  have hLsn (t : ℝ × ℝ × ℝ) := deletedContinuation_ne_zero_right K
    (psi * conjugate ((arithmeticHighEulerData K Sset P psi).rows.character u))
    (exceptionalPrimes K Sset) (s t) (by rw [hsre]; exact hsLine)
  have hL := (hLz.mul hLw).div hLs hLsn
  unfold rowVerticalKernel
  simp_rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZ]
  exact (((((((((continuous_const.mul hexp).mul hM).mul hden).mul hnPower).mul hxPower).mul
    hzPower).mul hyPower).mul hL).mul hcorr).div_const _

/-- Every original finite height box is genuinely integrable, jointly in
the three heights, before changing the integration coordinates. -/
theorem integrableOn_actual_rowVerticalKernel_absolute_box [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (hZ : 0 < Z)
    (sLine wLine zLine H : ℝ) (hsLine : 1 < sLine) (hwLine : 1 < wLine)
    (hzLine : 1 / 6 < zLine) :
    IntegrableOn (rowVerticalKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z sLine wLine zLine)
      (rowRetainedHeightBox H) rowHeightVolume := by
  have hc := continuous_actual_rowVerticalKernel_absolute K S mu nu P psi g T u Z hZ
    sLine wLine zLine hsLine hwLine hzLine
  exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

/-- All three original sequential integrals are integrable on every finite
box.  This permits the fixed arithmetic row sum to pass through each one. -/
theorem actual_rowContourBox_sequential_integrable [IsTotallyComplex K]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (hZ : 0 < Z)
    (sLine wLine zLine H : ℝ) (hsLine : 1 < sLine) (hwLine : 1 < wLine)
    (hzLine : 1 / 6 < zLine) :
    (∀ ts tw : ℝ, IntegrableOn
      (fun tz => rowKernelOnLines K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z sLine wLine zLine ts tw tz) (Icc (-H) H)) ∧
    (∀ ts : ℝ, IntegrableOn
      (fun tw => ∫ tz in Icc (-H) H,
        rowKernelOnLines K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
          g T u Z sLine wLine zLine ts tw tz) (Icc (-H) H)) ∧
    IntegrableOn (fun ts => ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H,
      rowKernelOnLines K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z sLine wLine zLine ts tw tz) (Icc (-H) H) := by
  let F := rowVerticalKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z sLine wLine zLine
  have hc : Continuous F := continuous_actual_rowVerticalKernel_absolute K S mu nu P psi
    g T u Z hZ sLine wLine zLine hsLine hwLine hzLine
  have hm : Continuous (fun p : ℝ × ℝ => ∫ tz in Icc (-H) H, F (p.1, p.2, tz)) := by
    apply continuous_parametric_integral_of_continuous
      (f := fun (p : ℝ × ℝ) (tz : ℝ) => F (p.1, p.2, tz)) _ isCompact_Icc
    exact hc.comp (by fun_prop)
  have ho : Continuous (fun ts : ℝ => ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H,
      F (ts, tw, tz)) :=
    continuous_parametric_integral_of_continuous
      (f := fun ts tw : ℝ => ∫ tz in Icc (-H) H, F (ts, tw, tz)) hm isCompact_Icc
  refine ⟨?_, ?_, ho.continuousOn.integrableOn_Icc⟩
  · intro ts tw
    exact (hc.comp (show Continuous (fun tz : ℝ => (ts, tw, tz)) by fun_prop)).continuousOn.integrableOn_Icc
  · intro ts
    exact (hm.comp (show Continuous (fun tw : ℝ => (ts, tw)) by fun_prop)).continuousOn.integrableOn_Icc

end HeckeSkeleton.Expansion.KernelRegularity

#print axioms HeckeSkeleton.Expansion.KernelRegularity.continuous_actual_fullCorrection_comp
#print axioms HeckeSkeleton.Expansion.KernelRegularity.continuous_actual_rowVerticalKernel_absolute
#print axioms HeckeSkeleton.Expansion.KernelRegularity.integrableOn_actual_rowVerticalKernel_absolute_box
#print axioms HeckeSkeleton.Expansion.KernelRegularity.actual_rowContourBox_sequential_integrable
