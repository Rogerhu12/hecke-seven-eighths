import Expansion.ActualTargetReciprocalStrip
import HeckeSkeleton.ExpansionModels.ActualKernelRegularity
import RowCharacterNormTwistExclusion
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Holomorphy of the actual nonprincipal row kernel

The original Euler region, the genuine additive Mellin transform, and the
common packet boundary make the actual compensated kernel holomorphic on
the complete small-row and large-row swept regions.  All finite marks,
all compensation subsets and the original normalization remain literal.
The numerator character is proved non-norm from the original arithmetic
nonprincipal-row condition.  The denominator reciprocal retains its
analytic value at every removable norm pole.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def actualNonprincipalRowRegion (B : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {v | B < v.1.re ∧ 1 / 6 < v.2.2.re ∧ v ∈ rowEulerRegion}

/-- The whole rectangular region swept by the small contours remains
inside the original Euler region. There are no numerator residues here. -/
theorem small_swept_mem_actualNonprincipalRowRegion
    {B e : ℝ} (hB : 7 / 8 < B) (he : 0 < e)
    (s w z : ℂ) (hs : B + e ≤ s.re) (hw : 1 / 2 ≤ w.re) (hz : 17 / 50 ≤ z.re) :
    (s, w, z) ∈ actualNonprincipalRowRegion B := by
  dsimp only [actualNonprincipalRowRegion, rowEulerRegion, Set.mem_setOf_eq]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The actual finite-window correction is differentiable after arbitrary
differentiable coordinate maps into its proved Euler region. -/
theorem differentiableAt_actual_fullCorrection_comp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x) (hregion : (s x, w x, z x) ∈ rowEulerRegion) :
    DifferentiableAt ℂ (fun y => compensatedRowFullCorrection K Sset P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z (s y) (w y) (z y)) x := by
  unfold compensatedRowFullCorrection
  apply DifferentiableAt.fun_sum
  intro p _
  apply (differentiableAt_const _).mul
  apply DifferentiableAt.fun_sum
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
  have hcor := (rowCorrection_analyticOnNhd_rowEulerRegion K Sset P psi
    ((Finset.univ \ J).image p) u (s x, w x, z x) hregion).differentiableAt.comp
      (f := fun y => (s y, w y, z y)) x
      (hs.prodMk (hw.prodMk hz))
  exact ((((differentiableAt_const _).mul hspow).mul (differentiableAt_const _)).mul hmpow).mul hcor

/-- The finite correction is jointly analytic after analytic coordinate
maps. This uses its existing joint Euler-product analyticity directly. -/
theorem analyticAt_actual_fullCorrection_comp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ) (s w z : X → ℂ) (x : X)
    (hs : AnalyticAt ℂ s x) (hw : AnalyticAt ℂ w x)
    (hz : AnalyticAt ℂ z x) (hregion : (s x, w x, z x) ∈ rowEulerRegion) :
    AnalyticAt ℂ (fun y => compensatedRowFullCorrection K Sset P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z (s y) (w y) (z y)) x := by
  unfold compensatedRowFullCorrection
  apply Finset.analyticAt_fun_sum
  intro p _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro J _
  dsimp only
  have hsel : (exteriorNorm K Sset (subsetPrimeIdeal K Sset p J) : ℂ) ∈
      Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (idealNorm_pos K (subsetPrimeIdeal K Sset p J).val)
  have hmark : (exteriorNorm K Sset
      (subsetPrimeIdeal K Sset p (Finset.univ \ J)) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr
      (idealNorm_pos K (subsetPrimeIdeal K Sset p (Finset.univ \ J)).val)
  have hspow := analyticAt_const.cpow
    ((hz.sub hw).sub (analyticAt_const (v := (1 : ℂ)))) hsel
  have hmpow := analyticAt_const.cpow
    ((hs.add hz).sub (analyticAt_const (v := (1 : ℂ)))) hmark
  have hcor := (rowCorrection_analyticOnNhd_rowEulerRegion K Sset P psi
    ((Finset.univ \ J).image p) u (s x, w x, z x) hregion).comp
      (hs.prod (hw.prod hz))
  exact (((analyticAt_const.mul hspow).mul analyticAt_const).mul hmpow).mul hcor

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
/-- Coordinatewise and joint holomorphy of the literal actual kernel,
with its original finite compensation and normalizers. -/
theorem differentiableAt_actual_nonprincipal_kernel_comp [IsTotallyComplex K]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B Z : ℝ} (hB : 1 / 2 ≤ B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x)
    (hregion : (s x, w x, z x) ∈ actualNonprincipalRowRegion B) :
    DifferentiableAt ℂ (fun y => compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z (s y) (w y) (z y)) x := by
  let R := (arithmeticHighEulerData K Sset P psi).rows
  have hpacket : psi * conjugate (R.character u) ∈ HeckePacket K omega :=
    packet_mul_finiteOrder (heckeLogNorm K) omega hpsi (R.finite_order u).inv
  have hnon := rowCharacterInput_ne_normTwist_of_not_principal K Sset P R hAllowed u hu
  have hrec := (differentiableOn_actual_target_reciprocal K Sset omega
    (psi * conjugate (R.character u)) hpacket hB hboundary).differentiableAt
      ((isOpen_rightHalfPlane B).mem_nhds hregion.1)
  have hrec' := hrec.comp x hs
  have hLw := ((heckeEulerDeletionPolynomial_analyticAt K (R.character u)
    (exceptionalPrimes K Sset) (w x)).differentiableAt.mul
      (differentiable_heckeContinuation_of_nonNorm K (R.character u) hnon (w x))).comp x hw
  have hzeta : 1 < (6 * z x).re := by
    have hzr := hregion.2.1
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hLz := ((heckeEulerDeletionPolynomial_analyticAt K 1
    (exceptionalPrimes K Sset) (6 * z x)).differentiableAt.mul
      (analyticAt_heckeContinuation K 1 hzeta).differentiableAt).comp x
        ((differentiableAt_const _).mul hz)
  have hzpos : 0 < (z x).re := by
    have hzr : (1 / 6 : ℝ) < (z x).re := hregion.2.1
    linarith
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive (z x)
    hzpos).differentiableAt.comp x hz
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
  have hcorr := differentiableAt_actual_fullCorrection_comp K S P psi g T u Z
    s w z x hs hw hz hregion.2.2
  simp_rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZ]
  simp only [div_eq_mul_inv]
  have hL := (hLz.mul hLw).mul hrec'
  exact ((((((((((differentiableAt_const _).mul hexp).mul hM).mul hden).mul hnPower).mul hxPower).mul
    hzPower).mul hyPower).mul hL).mul hcorr).mul (differentiableAt_const _)

include nu in
/-- Joint analyticity of the literal kernel follows by composing each
one-variable analytic factor and the actual joint finite correction. -/
theorem analyticAt_actual_nonprincipal_kernel_comp [IsTotallyComplex K]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B Z : ℝ} (hB : 1 / 2 ≤ B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s w z : X → ℂ) (x : X)
    (hs : AnalyticAt ℂ s x) (hw : AnalyticAt ℂ w x)
    (hz : AnalyticAt ℂ z x)
    (hregion : (s x, w x, z x) ∈ actualNonprincipalRowRegion B) :
    AnalyticAt ℂ (fun y => compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g T u Z (s y) (w y) (z y)) x := by
  let R := (arithmeticHighEulerData K Sset P psi).rows
  have hpacket : psi * conjugate (R.character u) ∈ HeckePacket K omega :=
    packet_mul_finiteOrder (heckeLogNorm K) omega hpsi (R.finite_order u).inv
  have hnon := rowCharacterInput_ne_normTwist_of_not_principal K Sset P R hAllowed u hu
  have hrec := (differentiableOn_actual_target_reciprocal K Sset omega
    (psi * conjugate (R.character u)) hpacket hB hboundary).analyticAt
      ((isOpen_rightHalfPlane B).mem_nhds hregion.1)
  have hrec' := hrec.comp hs
  have hLw := ((heckeEulerDeletionPolynomial_analyticAt K (R.character u)
    (exceptionalPrimes K Sset) (w x)).mul
      ((differentiable_heckeContinuation_of_nonNorm K (R.character u) hnon)
        .analyticAt (w x))).comp hw
  have hzeta : 1 < (6 * z x).re := by
    have hzr : (1 / 6 : ℝ) < (z x).re := hregion.2.1
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hLz := ((heckeEulerDeletionPolynomial_analyticAt K 1
    (exceptionalPrimes K Sset) (6 * z x)).mul
      (analyticAt_heckeContinuation K 1 hzeta)).comp
        ((analyticAt_const (v := (6 : ℂ))).mul hz)
  have hzpos : 0 < (z x).re := by
    have hzr : (1 / 6 : ℝ) < (z x).re := hregion.2.1
    linarith
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive
    (z x) hzpos).comp hz
  have hden := ((HighBinBoundary.ActualDenominator.differentiable_mellin
    P.denominator.toSmoothAnnularTest).analyticAt (w x)).comp hw
  have hN : (frequencyRowNorm K Sset u : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (idealNorm_pos K u.ideal.val)
  have hX : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (Real.rpow_pos_of_pos hZ _)
  have hY : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (Real.rpow_pos_of_pos hZ _)
  have hZc : (Z : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hZ
  have hnPower := analyticAt_const.cpow hz.neg hN
  have hxPower : AnalyticAt ℂ
      (fun y => ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z y)) x :=
    analyticAt_const.cpow (analyticAt_const.sub hz) hX
  have hzPower := analyticAt_const.cpow
    ((hs.add hz).sub (analyticAt_const (v := (1 : ℂ)))) hZc
  have hyPower := analyticAt_const.cpow (hw.sub (analyticAt_const (v := (1 : ℂ)))) hY
  have hexp := (((hs.add hz).sub (analyticAt_const (v := (1 : ℂ)))).pow 2).cexp
  have hcorr := analyticAt_actual_fullCorrection_comp K S P psi g T u Z
    s w z x hs hw hz hregion.2.2
  simp_rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZ]
  simp only [div_eq_mul_inv]
  have hL := (hLz.mul hLw).mul hrec'
  exact ((((((((((analyticAt_const.mul hexp).mul hM).mul hden).mul hnPower).mul hxPower).mul
    hzPower).mul hyPower).mul hL).mul hcorr).mul analyticAt_const

include nu in
/-- Joint holomorphy on the actual nonprincipal region, with no separate
strip-regularity input. -/
theorem analyticOnNhd_actual_nonprincipal_kernel [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B Z : ℝ} (hB : 1 / 2 ≤ B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => compensatedRowMellinKernel K Sset muS
      P psi (arithmeticHighEulerData K Sset P psi) g T u Z v.1 v.2.1 v.2.2)
      (actualNonprincipalRowRegion B) := by
  intro v hv
  exact analyticAt_actual_nonprincipal_kernel_comp K S mu nu P omega psi hpsi hAllowed
    g T u hu hB hZ hboundary Prod.fst (fun v : ℂ × ℂ × ℂ => v.2.1)
      (fun v : ℂ × ℂ × ℂ => v.2.2) v
      analyticAt_fst (analyticAt_fst.comp analyticAt_snd)
      (analyticAt_snd.comp analyticAt_snd) hv

end Expansion.Project

#print axioms Expansion.Project.differentiableAt_actual_nonprincipal_kernel_comp
#print axioms Expansion.Project.analyticAt_actual_fullCorrection_comp
#print axioms Expansion.Project.analyticAt_actual_nonprincipal_kernel_comp
#print axioms Expansion.Project.analyticOnNhd_actual_nonprincipal_kernel
