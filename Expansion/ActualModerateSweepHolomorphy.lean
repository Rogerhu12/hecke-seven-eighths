import Expansion.ActualRowKernelHolomorphy
import Expansion.ActualOuterContourTransport
import HeckeSkeleton.HighBinSupport.JointAnalyticLimit

/-!
# Actual moderate-row holomorphy on the genuine high-bin swept tube

The moderate starting line can have negative real w.  The repository's
positive rowEulerRegion does not contain it.  This file derives joint
holomorphy directly from the actual normally convergent high-bin Euler
product on its larger sweptTube, including the entire original finite
correction and the actual reciprocal supplied by the common packet.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def actualModerateRowRegion (B a e : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {v | B < v.1.re ∧ 1 / 6 < v.2.2.re ∧ v ∈ sweptTube a e}

theorem moderate_swept_mem_actualModerateRowRegion
    {B a e : ℝ} (haB : a ≤ B) (he : 0 < e)
    (s w z : ℂ) (hs : B + 20 * e ≤ s.re)
    (hw : 1 - a - 6 * e ≤ w.re) (hz : 17 / 50 ≤ z.re) :
    (s, w, z) ∈ actualModerateRowRegion B a e := by
  change B < s.re ∧ 1 / 6 < z.re ∧
    a + 15 * e < s.re ∧ 1 - a - 7 * e < w.re ∧ 17 / 50 - e < z.re
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Normal convergence of the actual marked Euler product gives joint
analyticity on the open high-bin tube, also when Re(w) is negative. -/
theorem analyticOnNhd_actual_rowCorrection_sweptTube
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (u : FrequencyRow K Sset)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => rowCorrection K Sset P psi
      (arithmeticHighEulerData K Sset P psi) Q u v.1 v.2.1 v.2.2) (sweptTube a e) := by
  have hp := explicitEuler_hasProdLocallyUniformlyOn (exteriorSupport K Sset u.ideal) Q
    (fun p : ExteriorPrime K Sset => (p.val.asIdeal.absNorm : ℝ))
    (rowW K Sset P u) (rowD K Sset P psi u) (rowE K Sset P psi)
    (rowPhaseData K Sset P psi u) (rowIndex K Sset u)
    (exteriorPrime_norm_two_le K Sset) ha ha1 he.le he1
    (rowW_norm K Sset P u) (rowD_norm K Sset P psi u) (rowE_norm K Sset P psi)
    (summable_exteriorPrime_swept_error K Sset he)
  have han := HighBinJointAnalytic.analyticOnNhd_of_tendstoLocallyUniformlyOn hp
    (Filter.Eventually.of_forall fun F => F.analyticOnNhd_fun_prod (fun p _ =>
      explicitLocalEuler_analyticOnNhd (exteriorSupport K Sset u.ideal) Q
        (fun q : ExteriorPrime K Sset => (q.val.asIdeal.absNorm : ℝ))
        (rowW K Sset P u) (rowD K Sset P psi u) (rowE K Sset P psi)
        (rowPhaseData K Sset P psi u) (rowIndex K Sset u)
        (exteriorPrime_norm_two_le K Sset) ha he.le
        (rowD_norm K Sset P psi u) (rowE_norm K Sset P psi) p))
    (sweptTube_isOpen a e)
  apply AnalyticOnNhd.congr (sweptTube_isOpen a e) han
  intro v hv
  exact (rowCorrection_eq_explicitEuler K Sset P psi Q u ha he.le v hv).symm

/-- The original finite tuple/subset correction is analytic on the same
larger tube; no factor is divided out and its zeros are retained. -/
theorem differentiableAt_actual_swept_fullCorrection_comp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z : ℝ)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x) (hregion : (s x, w x, z x) ∈ sweptTube a e) :
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
  have hcor := (analyticOnNhd_actual_rowCorrection_sweptTube K S P psi
    ((Finset.univ \ J).image p) u ha ha1 he he1 (s x, w x, z x) hregion).differentiableAt.comp
      (f := fun y => (s y, w y, z y)) x
      (hs.prodMk (hw.prodMk hz))
  exact ((((differentiableAt_const _).mul hspow).mul (differentiableAt_const _)).mul hmpow).mul hcor

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
theorem differentiableAt_actual_moderate_kernel_comp [IsTotallyComplex K]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B Z a e : ℝ} (hB : 1 / 2 ≤ B) (hZ : 0 < Z)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x)
    (hregion : (s x, w x, z x) ∈ actualModerateRowRegion B a e) :
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
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive (z x)
    (by have := hregion.2.1; linarith)).differentiableAt.comp x hz
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
  have hcorr := differentiableAt_actual_swept_fullCorrection_comp K S P psi g T u Z
    ha ha1 he he1 s w z x hs hw hz hregion.2.2
  simp_rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZ]
  simp only [div_eq_mul_inv]
  have hL := (hLz.mul hLw).mul hrec'
  exact ((((((((((differentiableAt_const _).mul hexp).mul hM).mul hden).mul hnPower).mul hxPower).mul
    hzPower).mul hyPower).mul hL).mul hcorr).mul (differentiableAt_const _)

include nu in
/-- Joint holomorphy on the actual nonprincipal region, with no separate
strip-regularity input. -/
theorem analyticOnNhd_actual_moderate_kernel [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B Z a e : ℝ} (hB : 1 / 2 ≤ B) (hZ : 0 < Z)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => compensatedRowMellinKernel K Sset muS
      P psi (arithmeticHighEulerData K Sset P psi) g T u Z v.1 v.2.1 v.2.2)
      (actualModerateRowRegion B a e) := by
  have hopen : IsOpen (actualModerateRowRegion B a e) :=
    ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      ((isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))).inter
          (sweptTube_isOpen a e)))
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro v hv
  exact (differentiableAt_actual_moderate_kernel_comp K S mu nu P omega psi hpsi hAllowed
    g T u hu hB hZ ha ha1 he he1 hboundary Prod.fst (fun v : ℂ × ℂ × ℂ => v.2.1)
      (fun v : ℂ × ℂ × ℂ => v.2.2) v
      differentiableAt_fst (differentiableAt_fst.comp _ differentiableAt_snd)
      (differentiableAt_snd.comp _ differentiableAt_snd) hv).differentiableWithinAt

include nu in
/-- Actual transport to the exact starting contour used by wholeBinBoundary.
No positive-w restriction is imposed or inferred. -/
theorem actual_moderate_row_initial_finite_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B e a Z H : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (ha : 51 / 100 ≤ a) (haB : a ≤ B) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 5 5 3 -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50) =
      actualOuterHorizontalFaces K S mu P psi g T u Z H
        (B + 20 * e) (1 - a - 6 * e) (17 / 50) := by
  let F := compensatedRowMellinKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z
  have hsubset : FiniteTripleContour.sweptTube 5 (B + 20 * e) 5
      (1 - a - 6 * e) 3 (17 / 50) ⊆ actualModerateRowRegion B a e := by
    intro v hv
    have hs : B + 20 * e ≤ v.1.re :=
      (le_min (by linarith : B + 20 * e ≤ 5) le_rfl).trans hv.1.1
    have hw : 1 - a - 6 * e ≤ v.2.1.re :=
      (le_min (by linarith : 1 - a - 6 * e ≤ 5) le_rfl).trans hv.2.1.1
    have hz : 17 / 50 ≤ v.2.2.re :=
      (le_min (by norm_num : (17 / 50 : ℝ) ≤ 3) le_rfl).trans hv.2.2.1
    exact moderate_swept_mem_actualModerateRowRegion haB he v.1 v.2.1 v.2.2 hs hw hz
  have hkernel := (analyticOnNhd_actual_moderate_kernel K S mu nu P omega psi hpsi hAllowed
    g T u hu (by linarith : 1 / 2 ≤ B) hZ ha (haB.trans hB1) he he1 hboundary).mono hsubset
  have hh := FiniteTripleContour.boxIntegral_sub_eq_faces F H 5 (B + 20 * e) 5
    (1 - a - 6 * e) 3 (17 / 50) hH hkernel
  change _ * FiniteTripleContour.boxIntegral F H 5 5 3 -
    _ * FiniteTripleContour.boxIntegral F H (B + 20 * e) (1 - a - 6 * e) (17 / 50) = _
  rw [← mul_sub, hh]
  rfl

include nu in
/-- Every finite original nonprincipal bin transports with exactly its
own members.  The set may depend on finite-height zero data; no all-height
zero assertion is extracted from the bin membership. -/
theorem actual_moderate_bin_initial_finite_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (rows : Finset (FrequencyRow K Sset))
    (hnon : ∀ u ∈ rows, ¬principalFrequencyRow K Sset u)
    {B e a Z H : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (ha : 51 / 100 ≤ a) (haB : a ≤ B) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    (∑ u ∈ rows, rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 5 5 3) -
      (∑ u ∈ rows, rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H (B + 20 * e) (1 - a - 6 * e) (17 / 50)) =
      ∑ u ∈ rows, actualOuterHorizontalFaces K S mu P psi g T u Z H
        (B + 20 * e) (1 - a - 6 * e) (17 / 50) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact actual_moderate_row_initial_finite_transport K S mu nu P omega psi hpsi hAllowed
    g T u (hnon u hu) hB hB1 ha haB he he1 hZ hH hboundary

end Expansion.Project

#print axioms Expansion.Project.analyticOnNhd_actual_rowCorrection_sweptTube
#print axioms Expansion.Project.analyticOnNhd_actual_moderate_kernel
#print axioms Expansion.Project.actual_moderate_bin_initial_finite_transport
