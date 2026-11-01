import Expansion.ActualPrincipalResidueTails
import Expansion.ActualPrincipalInitialTransport
import Expansion.ActualPrincipalMainContour
import HeckeSkeleton.ExpansionModels.ActualKernelRegularity

/-!
# Exact finite principal residue accounting

Compact continuity justifies the actual finite Fubini exchanges and
subtractions.  The two finite shifts retain the original w and z vertical
remainders, the actual normalized double residue, and the two already
estimated errors.  No vertical remainder is reclassified as a height tail.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open HeckeSkeleton.Expansion.MellinRegularity HeckeSkeleton.Expansion.KernelRegularity
open Expansion.FiniteTripleContour (vertical)
open scoped Classical Topology

private theorem finite_w_residue_accounting
    (Fp Fm : ℝ → ℝ → ℝ → ℂ) (R : ℝ → ℝ → ℂ)
    (hFp : Continuous (fun p : ℝ × ℝ × ℝ => Fp p.1 p.2.1 p.2.2))
    (hFm : Continuous (fun p : ℝ × ℝ × ℝ => Fm p.1 p.2.1 p.2.2))
    (hR : Continuous (Function.uncurry R)) (lambda : ℂ) (H : ℝ) :
    lambda ^ 3 * (∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H, Fp ts tw tz) -
      lambda ^ 3 * (∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H, Fm ts tw tz) -
      lambda ^ 2 * (∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, R ts tz) =
      lambda ^ 2 * ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H,
        (lambda * ∫ tw in Icc (-H) H, Fp ts tw tz) -
          (lambda * ∫ tw in Icc (-H) H, Fm ts tw tz) - R ts tz := by
  have hperm (F : ℝ → ℝ → ℝ → ℂ)
      (hF : Continuous (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)) :
      (∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H, F ts tw tz) =
        ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, ∫ tw in Icc (-H) H, F ts tw tz := by
    apply integral_congr_ae
    filter_upwards [] with ts
    exact FiniteTripleContour.setIntegral_swap_of_continuous (fun tw tz => F ts tw tz)
      (hF.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (ts, p.1, p.2)))) H
  let U : ℝ → ℝ → ℂ := fun ts tz => lambda * ∫ tw in Icc (-H) H, Fp ts tw tz
  let V : ℝ → ℝ → ℂ := fun ts tz => lambda * ∫ tw in Icc (-H) H, Fm ts tw tz
  have hU : Continuous (Function.uncurry U) := by
    change Continuous (fun p : ℝ × ℝ => lambda * ∫ tw in Icc (-H) H, Fp p.1 tw p.2)
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous
      (f := fun p : ℝ × ℝ => fun tw : ℝ => Fp p.1 tw p.2) (s := Icc (-H) H) _ isCompact_Icc
    exact hFp.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2, p.1.2)))
  have hV : Continuous (Function.uncurry V) := by
    change Continuous (fun p : ℝ × ℝ => lambda * ∫ tw in Icc (-H) H, Fm p.1 tw p.2)
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous
      (f := fun p : ℝ × ℝ => fun tw : ℝ => Fm p.1 tw p.2) (s := Icc (-H) H) _ isCompact_Icc
    exact hFm.comp (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2, p.1.2)))
  have hsub := FiniteTripleContour.integral_sub_integral_twice U V hU hV H
  have hres := FiniteTripleContour.integral_sub_integral_twice
    (fun ts tz => U ts tz - V ts tz) R (hU.sub hV) hR H
  simp only [FiniteTripleContour.heightBox] at hsub hres
  change _ = lambda ^ 2 * ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H,
    U ts tz - V ts tz - R ts tz
  rw [← hres, ← hsub, hperm Fp hFp, hperm Fm hFm]
  simp only [U, V, integral_const_mul]
  ring

private theorem finite_z_residue_accounting
    (Fp Fm : ℝ → ℝ → ℂ) (R : ℝ → ℂ)
    (hFp : Continuous (Function.uncurry Fp)) (hFm : Continuous (Function.uncurry Fm))
    (hR : Continuous R) (lambda : ℂ) (H : ℝ) :
    lambda ^ 2 * (∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, Fp ts tz) -
      lambda ^ 2 * (∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, Fm ts tz) -
      lambda * (∫ ts in Icc (-H) H, R ts) =
      lambda * ∫ ts in Icc (-H) H,
        (lambda * ∫ tz in Icc (-H) H, Fp ts tz) -
          (lambda * ∫ tz in Icc (-H) H, Fm ts tz) - R ts := by
  have hU : Continuous (fun ts => lambda * ∫ tz in Icc (-H) H, Fp ts tz) :=
    continuous_const.mul (continuous_parametric_integral_of_continuous hFp isCompact_Icc)
  have hV : Continuous (fun ts => lambda * ∫ tz in Icc (-H) H, Fm ts tz) :=
    continuous_const.mul (continuous_parametric_integral_of_continuous hFm isCompact_Icc)
  have hsub :
      (∫ ts in Icc (-H) H,
        (lambda * ∫ tz in Icc (-H) H, Fp ts tz) -
          (lambda * ∫ tz in Icc (-H) H, Fm ts tz)) =
        (∫ ts in Icc (-H) H, lambda * ∫ tz in Icc (-H) H, Fp ts tz) -
          (∫ ts in Icc (-H) H, lambda * ∫ tz in Icc (-H) H, Fm ts tz) := by
    exact integral_sub (μ := volume.restrict (Icc (-H) H))
      hU.continuousOn.integrableOn_Icc hV.continuousOn.integrableOn_Icc
  have hres :
      (∫ ts in Icc (-H) H,
        (lambda * ∫ tz in Icc (-H) H, Fp ts tz) -
          (lambda * ∫ tz in Icc (-H) H, Fm ts tz) - R ts) =
        (∫ ts in Icc (-H) H,
          (lambda * ∫ tz in Icc (-H) H, Fp ts tz) -
            (lambda * ∫ tz in Icc (-H) H, Fm ts tz)) -
          (∫ ts in Icc (-H) H, R ts) := by
    exact integral_sub (μ := volume.restrict (Icc (-H) H))
      (hU.sub hV).continuousOn.integrableOn_Icc hR.continuousOn.integrableOn_Icc
  rw [hres, hsub]
  simp only [integral_const_mul]
  ring

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

private theorem continuous_actual_target_reciprocal_comp
    {X : Type*} [TopologicalSpace X]
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B : ℝ} (hB : 1 / 2 ≤ B)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s : X → ℂ) (hs : Continuous s) (hmem : ∀ x, B < (s x).re) :
    Continuous (fun x => (heckeDeletedContinuation K psi (exceptionalPrimes K Sset) (s x))⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((differentiableOn_actual_target_reciprocal K Sset omega psi hpsi hB hboundary).differentiableAt
    ((isOpen_rightHalfPlane B).mem_nhds (hmem x))).continuousAt.comp hs.continuousAt

private theorem continuous_actual_deletedZeta_line (sigma : ℝ) (hsigma : sigma ≠ 1) :
    Continuous (fun t : ℝ => heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (vertical sigma t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne : vertical sigma t ≠ 1 := by
    intro hh
    exact hsigma (by simpa [vertical] using congrArg Complex.re hh)
  exact (actual_deletedZeta_analyticAt K Sset _ hne).continuousAt.comp (by unfold vertical; fun_prop)

include nu in
theorem continuous_actualPrincipal_core_heights [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (g : PrimeWindowGeometry) {B e Z wLine zLine : ℝ}
    (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z)
    (hw : 19 / 20 ≤ wLine) (hz : 33 / 200 ≤ zLine) (hzPole : zLine ≠ 1 / 6)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (W : ℂ → ℂ) (hW : Continuous (fun t : ℝ => W (vertical wLine t))) :
    Continuous (fun p : ℝ × ℝ × ℝ => actualPrincipalKernelCore K S mu P psi g Z
      (vertical (B + e) p.1) (vertical wLine p.2.1) (vertical zLine p.2.2)
      (W (vertical wLine p.2.1))) := by
  let s : ℝ × ℝ × ℝ → ℂ := fun p => vertical (B + e) p.1
  let w : ℝ × ℝ × ℝ → ℂ := fun p => vertical wLine p.2.1
  let z : ℝ × ℝ × ℝ → ℂ := fun p => vertical zLine p.2.2
  have hs : Continuous s := by dsimp [s, vertical]; fun_prop
  have hwc : Continuous w := by dsimp [w, vertical]; fun_prop
  have hzc : Continuous z := by dsimp [z, vertical]; fun_prop
  have hrec := continuous_actual_target_reciprocal_comp K S omega psi hpsi
    (by linarith : 1 / 2 ≤ B) hboundary s hs (by intro p; simp [s, vertical]; linarith)
  have hLz : Continuous (fun p => heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hne : 6 * z p ≠ 1 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp [z, vertical] at hr
      apply hzPole
      linarith
    have hline : ContinuousAt (fun q : ℝ × ℝ × ℝ => (6 : ℂ) * z q) p :=
      (continuous_const.mul hzc).continuousAt
    exact (actual_deletedZeta_analyticAt K Sset _ hne).continuousAt.comp_of_eq hline rfl
  have hM : Continuous (fun p => additiveMellin K Sset muS P.additive (z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (analyticOnNhd_actual_additiveMellin K S mu nu P.additive (z p)
      (by simp [z, vertical]; linarith)).continuousAt.comp hzc.continuousAt
  have hden := (HighBinBoundary.ActualDenominator.differentiable_mellin
    P.denominator.toSmoothAnnularTest).continuous.comp hwc
  have hx : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hy : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hzc0 : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hxp : Continuous (fun p => ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z p)) :=
    (continuous_const.sub hzc).const_cpow (Or.inl hx)
  have hzp := ((hs.add hzc).sub (continuous_const (y := (1 : ℂ)))).const_cpow
    (Or.inl hzc0)
  have hyp := (hwc.sub (continuous_const (y := (1 : ℂ)))).const_cpow (Or.inl hy)
  have hg := (((hs.add hzc).sub (continuous_const (y := (1 : ℂ)))).pow 2).cexp
  have hcorr := continuous_actual_fullCorrection_comp K S P psi g ∅
    (physicalPrincipalRow K Sset) Z s w z hs hwc hzc (by
      intro p
      apply principal_rectangle_mem_rowEulerRegion
      · simp [s, vertical]; linarith
      · simpa [w, vertical] using hw
      · simpa [z, vertical] using hz)
  have hval : Continuous (fun p : ℝ × ℝ × ℝ => W (w p)) :=
    hW.comp (continuous_fst.comp continuous_snd)
  unfold actualPrincipalKernelCore
  simp only [div_eq_mul_inv]
  exact ((((((((continuous_const.mul hg).mul hM).mul hden).mul hxp).mul hzp).mul hyp).mul
    ((hLz.mul hval).mul hrec)).mul hcorr).mul continuous_const

include nu in
theorem continuous_actualPrincipal_w_residue_heights [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (g : PrimeWindowGeometry) {B e Z zLine : ℝ}
    (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z)
    (hz : 33 / 200 ≤ zLine) (hzPole : zLine ≠ 1 / 6)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    Continuous (fun p : ℝ × ℝ => actualPrincipalWResidueKernel K S mu P psi g Z
      (vertical (B + e) p.1) (vertical zLine p.2)) := by
  have hc := continuous_actualPrincipal_core_heights K S mu nu P omega psi hpsi g
    hB he hZ (wLine := 1) (by norm_num) hz hzPole hboundary
    (fun _ => deletedZetaResidue K Sset) continuous_const
  simpa only [actualPrincipalWResidueKernel, vertical, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.ofReal_one] using hc.comp'
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1, (0 : ℝ), p.2)))

private theorem continuous_actualPrincipal_double_residue
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (g : PrimeWindowGeometry) {B e Z : ℝ} (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    Continuous (fun t : ℝ => actualPrincipalZRegularPart K S mu P psi g Z
      (vertical (B + e) t) (1 / 6) * (deletedZetaResidue K Sset / 6)) := by
  let s : ℝ → ℂ := vertical (B + e)
  have hs : Continuous s := by
    change Continuous (fun t : ℝ => ((B + e : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    fun_prop
  have hrec := continuous_actual_target_reciprocal_comp K S omega psi hpsi
    (by linarith : 1 / 2 ≤ B) hboundary s hs (by intro t; simp [s, vertical]; linarith)
  have hcorr := continuous_actual_fullCorrection_comp K S P psi g ∅
    (physicalPrincipalRow K Sset) Z s (fun _ => 1) (fun _ => 1 / 6)
    hs continuous_const continuous_const (by
      intro t
      apply principal_rectangle_mem_rowEulerRegion
      · simp [s, vertical]; linarith
      · norm_num
      · norm_num)
  have hg := (((hs.add_const (1 / 6 : ℂ)).sub (continuous_const (y := (1 : ℂ)))).pow 2).cexp
  have hp := ((hs.add_const (1 / 6 : ℂ)).sub (continuous_const (y := (1 : ℂ)))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  unfold actualPrincipalZRegularPart
  simp only [div_eq_mul_inv]
  exact ((((((((continuous_const.mul hg).mul_const _).mul_const _).mul_const _).mul hp).mul
    (continuous_const.mul hrec)).mul hcorr).mul_const _).mul_const _

def actualPrincipalWResidueBox (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(2 : ℤ)) *
    ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H,
      actualPrincipalWResidueKernel K S mu P psi g Z
        (vertical (B + e) ts) (vertical (1 / 6 + e) tz)

include nu in
theorem actualPrincipal_finite_w_accounting [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e Z : ℝ}
    (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z) (H : ℝ)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z H (B + e) (1 + e) (1 / 6 + e) -
      actualPrincipalWRemainder K S mu P psi g Z H B e -
      actualPrincipalWResidueBox K S mu P psi g Z H B e =
      actualPrincipalWShiftError K S mu P psi g Z H B e := by
  let F (sigma : ℝ) (ts tw tz : ℝ) := actualPrincipalKernelCore K S mu P psi g Z
    (vertical (B + e) ts) (vertical sigma tw) (vertical (1 / 6 + e) tz)
    (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (vertical sigma tw))
  have hcont (sigma : ℝ) (hsigma : 19 / 20 ≤ sigma) (hpole : sigma ≠ 1) :
      Continuous (fun p : ℝ × ℝ × ℝ => F sigma p.1 p.2.1 p.2.2) :=
    continuous_actualPrincipal_core_heights K S mu nu P omega psi hpsi g hB he hZ
      hsigma (by linarith) (by linarith) hboundary
      (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset))
      (continuous_actual_deletedZeta_line K S sigma hpole)
  have hres := continuous_actualPrincipal_w_residue_heights K S mu nu P omega psi hpsi g
    hB he hZ (zLine := 1 / 6 + e) (by linarith) (by linarith) hboundary
  have hh := finite_w_residue_accounting (F (1 + e)) (F (19 / 20))
    (fun ts tz => actualPrincipalWResidueKernel K S mu P psi g Z
      (vertical (B + e) ts) (vertical (1 / 6 + e) tz))
    (hcont _ (by linarith) (by linarith)) (hcont _ le_rfl (by norm_num)) hres
    (2 * (Real.pi : ℂ))⁻¹ H
  simp only [actualPrincipalWRemainder, actualPrincipalWResidueBox, actualPrincipalWShiftError,
    rowContourBox]
  simp_rw [actualPrincipalKernel_eq_core K S mu P psi hAllowed g Z hZ]
  simpa only [F, principalFiniteVerticalIntegral, vertical, zpow_neg, zpow_ofNat, inv_pow] using hh

include nu in
theorem actualPrincipal_finite_z_accounting [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (g : PrimeWindowGeometry) {B e Z : ℝ}
    (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z) (H : ℝ)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    actualPrincipalWResidueBox K S mu P psi g Z H B e -
      actualPrincipalZRemainder K S mu P psi g Z H B e -
      actualDoubleResidueLineTruncation K Sset P psi g Z H (B + e) =
      actualPrincipalZShiftError K S mu P psi g Z H B e := by
  have hcont (sigma : ℝ) (hsigma : 33 / 200 ≤ sigma) (hpole : sigma ≠ 1 / 6) :=
    continuous_actualPrincipal_w_residue_heights K S mu nu P omega psi hpsi g
      hB he hZ hsigma hpole hboundary
  have hres := continuous_actualPrincipal_double_residue K S mu P omega psi hpsi g hB he hZ hboundary
  have hh := finite_z_residue_accounting
    (fun ts tz => actualPrincipalWResidueKernel K S mu P psi g Z
      (vertical (B + e) ts) (vertical (1 / 6 + e) tz))
    (fun ts tz => actualPrincipalWResidueKernel K S mu P psi g Z
      (vertical (B + e) ts) (vertical (33 / 200) tz))
    (fun ts => actualPrincipalZRegularPart K S mu P psi g Z (vertical (B + e) ts) (1 / 6) *
      (deletedZetaResidue K Sset / 6))
    (hcont _ (by linarith) (by linarith)) (hcont _ le_rfl (by norm_num)) hres
    (2 * (Real.pi : ℂ))⁻¹ H
  have hresEq (ts : ℝ) := actualPrincipal_double_residue_eq K S mu P psi hAllowed hN g Z hZ
    (vertical (B + e) ts) (by simp [vertical]; linarith)
  unfold actualPrincipalWResidueBox actualPrincipalZRemainder actualDoubleResidueLineTruncation
    actualPrincipalZShiftError
  dsimp only [FiniteTripleContour.vertical, ExpansionInterfaces.Mellin.vertical] at hresEq ⊢
  simp_rw [← hresEq]
  simpa only [principalFiniteVerticalIntegral, FiniteTripleContour.vertical,
    ExpansionInterfaces.Mellin.vertical, zpow_neg, zpow_ofNat, inv_pow] using hh

include nu in
theorem actualPrincipal_two_finite_residues [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (g : PrimeWindowGeometry) {B e Z : ℝ}
    (hB : 7 / 8 < B) (he : 0 < e) (hZ : 0 < Z) (H : ℝ)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z H (B + e) (1 + e) (1 / 6 + e) -
      principalLineProbe K Sset P psi Z =
      (actualPrincipalWRemainder K S mu P psi g Z H B e +
        actualPrincipalZRemainder K S mu P psi g Z H B e +
        actualPrincipalSlotRemainder K Sset P psi g Z H (B + e)) +
      (actualPrincipalWShiftError K S mu P psi g Z H B e +
        actualPrincipalZShiftError K S mu P psi g Z H B e +
        actualPrincipalMainTail K Sset P psi Z H (B + e)) := by
  have hw := actualPrincipal_finite_w_accounting K S mu nu P omega psi hpsi hAllowed g
    hB he hZ H hboundary
  have hz := actualPrincipal_finite_z_accounting K S mu nu P omega psi hpsi hAllowed hN g
    hB he hZ H hboundary
  have hm := actualDoubleResidue_sub_principal_eq K Sset P psi g Z H (B + e)
  linear_combination hw + hz + hm

end Expansion.Project

#print axioms Expansion.Project.continuous_actualPrincipal_core_heights
#print axioms Expansion.Project.actualPrincipal_finite_w_accounting
#print axioms Expansion.Project.actualPrincipal_finite_z_accounting
#print axioms Expansion.Project.actualPrincipal_two_finite_residues
