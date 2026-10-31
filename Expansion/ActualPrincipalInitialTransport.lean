import Expansion.ActualPrincipalPoleLimits
import Expansion.FiniteTripleContourTransport

/-!
# Initial finite transport of the actual principal row

Before either numerator pole is crossed, the actual principal kernel is
jointly holomorphic on the original positive three-variable region to
the right of the common target boundary.  The genuine finite rectangle
theorem therefore transports (5,5,3) to (B+e,1+e,1/6+e), retaining all six
horizontal faces in their literal integrals.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open HeckeSkeleton.Expansion.MellinRegularity
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def actualPrincipalInitialRegion (B : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {v | B < v.1.re ∧ 1 < v.2.1.re ∧ 1 / 6 < v.2.2.re}

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
theorem differentiableAt_actual_principal_kernel_comp [IsTotallyComplex K]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B Z : ℝ} (hB : 7 / 8 < B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s w z : X → ℂ) (x : X)
    (hs : DifferentiableAt ℂ s x) (hw : DifferentiableAt ℂ w x)
    (hz : DifferentiableAt ℂ z x)
    (hregion : (s x, w x, z x) ∈ actualPrincipalInitialRegion B) :
    DifferentiableAt ℂ (fun y => compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset)
        Z (s y) (w y) (z y)) x := by
  have hrec := (differentiableOn_actual_target_reciprocal K Sset omega psi hpsi
    (by linarith : 1 / 2 ≤ B) hboundary).differentiableAt
      ((isOpen_rightHalfPlane B).mem_nhds hregion.1)
  have hrec' := hrec.comp x hs
  have hLw := ((heckeEulerDeletionPolynomial_analyticAt K 1
    (exceptionalPrimes K Sset) (w x)).differentiableAt.fun_mul
      (analyticAt_heckeContinuation K 1 hregion.2.1).differentiableAt).comp x hw
  have hzeta : 1 < (6 * z x).re := by
    have hzr := hregion.2.2
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hLz := ((heckeEulerDeletionPolynomial_analyticAt K 1
    (exceptionalPrimes K Sset) (6 * z x)).differentiableAt.fun_mul
      (analyticAt_heckeContinuation K 1 hzeta).differentiableAt).comp x
        ((differentiableAt_const _).fun_mul hz)
  have hM := (analyticOnNhd_actual_additiveMellin K S mu nu P.additive (z x)
    (by have := hregion.2.2; linarith)).differentiableAt.comp x hz
  have hden := (HighBinBoundary.ActualDenominator.differentiable_mellin
    P.denominator.toSmoothAnnularTest (w x)).comp x hw
  have hX : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hY : ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hxPower : DifferentiableAt ℂ
      (fun y => ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z y)) x :=
    ((differentiableAt_const _).sub hz).const_cpow (Or.inl hX)
  have hzPower := ((hs.add hz).sub_const 1).const_cpow (Or.inl hZc)
  have hyPower := (hw.sub_const 1).const_cpow (Or.inl hY)
  have hexp := (((hs.add hz).sub_const 1).pow 2).cexp
  have hEuler : (s x, w x, z x) ∈ rowEulerRegion :=
    principal_rectangle_mem_rowEulerRegion (s x) (w x) (z x)
      (by have := hregion.1; linarith)
      (by have := hregion.2.1; linarith) (by have := hregion.2.2; linarith)
  have hcorr := differentiableAt_actual_fullCorrection_comp K S P psi g ∅
    (physicalPrincipalRow K Sset) Z s w z x hs hw hz hEuler
  simp_rw [actualPrincipalKernel_eq_core K S mu P psi hAllowed g Z hZ]
  unfold actualPrincipalKernelCore
  simp only [div_eq_mul_inv]
  have hL := (hLz.fun_mul hLw).fun_mul hrec'
  exact (((((((((differentiableAt_const _).fun_mul hexp).fun_mul hM).fun_mul hden).fun_mul hxPower).fun_mul
    hzPower).fun_mul hyPower).fun_mul hL).fun_mul hcorr).fun_mul (differentiableAt_const _)

include nu in
theorem analyticOnNhd_actual_principal_kernel [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B Z : ℝ} (hB : 7 / 8 < B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => compensatedRowMellinKernel K Sset muS
      P psi (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset)
        Z v.1 v.2.1 v.2.2) (actualPrincipalInitialRegion B) := by
  have hopen : IsOpen (actualPrincipalInitialRegion B) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      ((isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))).inter
        (isOpen_lt continuous_const
          (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))))
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro v hv
  exact (differentiableAt_actual_principal_kernel_comp K S mu nu P omega psi hpsi hAllowed
    g hB hZ hboundary Prod.fst (fun v : ℂ × ℂ × ℂ => v.2.1)
      (fun v : ℂ × ℂ × ℂ => v.2.2) v differentiableAt_fst
      (differentiableAt_fst.comp _ differentiableAt_snd)
      (differentiableAt_snd.comp _ differentiableAt_snd) hv).differentiableWithinAt

/-- The six genuine horizontal faces of the initial principal transport. -/
def actualPrincipalInitialHorizontal (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  let F := compensatedRowMellinKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset) Z
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    (FiniteTripleContour.sFaces F H 5 (B + e) 5 3 +
      FiniteTripleContour.wFaces F H (B + e) 5 (1 + e) 3 +
      FiniteTripleContour.zFaces F H (B + e) (1 + e) 3 (1 / 6 + e))

include nu in
/-- The original finite three-variable contour move, before taking either
residue.  Every horizontal face remains visible on the right-hand side. -/
theorem actualPrincipal_initial_box_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e Z H : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z H 5 5 3 -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ (physicalPrincipalRow K Sset) Z H (B + e) (1 + e) (1 / 6 + e) =
          actualPrincipalInitialHorizontal K S mu P psi g Z H B e := by
  let F := compensatedRowMellinKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset) Z
  have hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ × ℂ => F v.1 v.2.1 v.2.2)
      (FiniteTripleContour.sweptTube 5 (B + e) 5 (1 + e) 3 (1 / 6 + e)) := by
    apply (analyticOnNhd_actual_principal_kernel K S mu nu P omega psi hpsi hAllowed
      g hB hZ hboundary).mono
    intro v hv
    simp only [FiniteTripleContour.sweptTube, Set.mem_setOf_eq,
      uIcc_of_ge (show B + e ≤ 5 by linarith),
      uIcc_of_ge (show 1 + e ≤ 5 by linarith),
      uIcc_of_ge (show 1 / 6 + e ≤ 3 by linarith)] at hv
    exact ⟨by linarith [hv.1.1], by linarith [hv.2.1.1], by linarith [hv.2.2.1]⟩
  have hh := FiniteTripleContour.boxIntegral_sub_eq_faces F H 5 (B + e) 5 (1 + e)
    3 (1 / 6 + e) hH hF
  simpa only [rowContourBox, actualPrincipalInitialHorizontal, FiniteTripleContour.boxIntegral,
    FiniteTripleContour.heightBox, FiniteTripleContour.vertical, mul_sub, F] using
      congrArg (fun c : ℂ => (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) * c) hh

end Expansion.Project

#print axioms Expansion.Project.analyticOnNhd_actual_principal_kernel
#print axioms Expansion.Project.actualPrincipal_initial_box_transport
