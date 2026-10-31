import Expansion.ActualTargetReciprocalStrip
import Expansion.ActualPrincipalSlotRemainder
import HeckeGeneral.Analysis.GaussianContour
import DedekindZetaZeroFree.Analysis.VerticalContourShift

/-!
# The actual principal main integral on the common line

Only the principal main correction is moved from the common line to the
original line Re = 2.  Its actual deleted reciprocal is analytic across
the full strip, including removable norm poles.  The genuine Gaussian
absorbs its proved polynomial height bound.  The finite-height main term
therefore differs from the original principalLineProbe by an explicitly
bounded Gaussian tail.  The compensated slot error stays on its original
common line throughout this argument.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionInterfaces.Mellin
open DedekindZetaZeroFree
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A fixed polynomial height loss uses only half the original Gaussian. -/
theorem actual_polynomial_gaussian_bound (k t : ℝ) (hk : 0 ≤ k) :
    (4 + |t|) ^ k * Real.exp (-(t ^ 2)) ≤
      Real.exp (4 * k + k ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  rw [Real.rpow_def_of_pos (by positivity : 0 < 4 + |t|),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (4 + |t|) ≤ 4 + |t| :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_right hlog hk
  nlinarith [sq_abs t, sq_nonneg (|t| - k)]

theorem actual_halfGaussian_polynomial_decay (t : ℝ) :
    Real.exp (-(1 / 2 : ℝ) * t ^ 2) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
  have he := Real.add_one_le_exp (t ^ 2 / 2)
  have hp : (1 + |t|) ^ 2 ≤ 4 * Real.exp (t ^ 2 / 2) := by
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |t|), Real.rpow_two]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |t|) ^ 2)).mpr
  have hn : Real.exp (-(1 / 2 : ℝ) * t ^ 2) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  nlinarith [mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-(1 / 2 : ℝ) * t ^ 2))]

/-- The integrand uses the original principal correction, Gaussian and
deleted target continuation; it is analytic even at a removable norm pole. -/
theorem differentiableOn_actualPrincipal_main
    (P : ProbeData K S) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B Z : ℝ} (hB : 7 / 8 < B) (hZ : 0 < Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    DifferentiableOn ℂ
      (fun s => actualPrincipalWeightedTerm K S psi Z s (principalCorrection K S P psi s))
      (rightHalfPlane B) := by
  have hr := differentiableOn_actual_target_reciprocal K S omega psi hpsi
    (by linarith : 1 / 2 ≤ B) hboundary
  intro s hs
  have hp : DifferentiableAt ℂ (fun z : ℂ => (Z : ℂ) ^ (z - 11 / 16)) s :=
    (differentiableAt_id.sub_const _).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  have hg : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((z - 5 / 6) ^ 2)) s := by
    fun_prop
  have hcorr := (analyticOnNhd_principalCorrection K S P psi s (by
    have : B < s.re := hs
    show (2 / 3 : ℝ) < s.re
    linarith)).differentiableAt
  simpa only [actualPrincipalWeightedTerm, div_eq_mul_inv] using
    ((hp.mul hg).mul hcorr).differentiableWithinAt.mul (hr s hs)

/-- All constants precede the prime scale and the line height.  The power
of Z retains the exact real part of the line rather than a strip maximum. -/
theorem exists_actualPrincipal_main_gaussian_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z → ∀ sigma ∈ Icc (B + e) 2, ∀ t : ℝ,
      ‖actualPrincipalWeightedTerm K S psi Z (vertical sigma t)
        (principalCorrection K S P psi (vertical sigma t))‖ ≤
          C * Z ^ (sigma - 11 / 16) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  obtain ⟨Cr, k, hCr, hk, hrec⟩ := exists_actual_target_strip_reciprocal_bound
    K S hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨CH, hCH, hHbound⟩ := exists_norm_principalCorrection_le K S P psi
    (σ₁ := (7 / 8 : ℝ)) (by norm_num)
  let C : ℝ := Real.exp ((7 / 6 : ℝ) ^ 2) * (CH + 1) * Cr *
    Real.exp (4 * k + k ^ 2 / 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Z hZ sigma hsigma t
  have hGauss : ‖Complex.exp ((vertical sigma t - 5 / 6) ^ 2)‖ ≤
      Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp (-(t ^ 2)) := by
    have habs : |sigma - 5 / 6| ≤ 7 / 6 := by
      apply abs_le.mpr
      constructor <;> linarith [hsigma.1, hsigma.2]
    simpa only [gaussianContourFactor, vertical, Complex.ofReal_div,
      Complex.ofReal_ofNat] using gaussianContourFactor_strip_bound
        (5 / 6) (7 / 6) sigma t (by norm_num) habs
  have hcorr : ‖principalCorrection K S P psi (vertical sigma t)‖ ≤ CH + 1 :=
    (hHbound _ (by simp only [vertical_re]; linarith [hsigma.1])).trans (by linarith)
  have hrec' : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S)
      (vertical sigma t))⁻¹‖ ≤ Cr * (4 + |t|) ^ k := by
    simpa only [vertical_im] using hrec (vertical sigma t)
      (by simpa only [vertical_re] using hsigma.1)
      (by simpa only [vertical_re] using hsigma.2)
  have hre : (vertical sigma t - (11 / 16 : ℂ)).re = sigma - 11 / 16 := by simp
  rw [actualPrincipalWeightedTerm, div_eq_mul_inv, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ, hre]
  calc
    _ ≤ (Z ^ (sigma - 11 / 16) *
          (Real.exp ((7 / 6 : ℝ) ^ 2) * Real.exp (-(t ^ 2))) * (CH + 1)) *
          (Cr * (4 + |t|) ^ k) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hGauss
        (Real.rpow_nonneg hZ.le _)) hcorr (norm_nonneg _) (by positivity))
        hrec' (norm_nonneg _) (by positivity)
    _ = (Z ^ (sigma - 11 / 16) * Real.exp ((7 / 6 : ℝ) ^ 2) * (CH + 1) * Cr) *
          ((4 + |t|) ^ k * Real.exp (-(t ^ 2))) := by ring
    _ ≤ (Z ^ (sigma - 11 / 16) * Real.exp ((7 / 6 : ℝ) ^ 2) * (CH + 1) * Cr) *
          (Real.exp (4 * k + k ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
      mul_le_mul_of_nonneg_left (actual_polynomial_gaussian_bound k t hk) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Exact contour shift of the actual principal main term.  The common
packet boundary is the only zero-location premise. -/
theorem actualPrincipal_main_line_eq
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e Z : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hZ : 1 ≤ Z)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
      actualPrincipalWeightedTerm K S psi Z (vertical (B + e) t)
        (principalCorrection K S P psi (vertical (B + e) t)) =
      principalLineProbe K S P psi Z := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  obtain ⟨C, hC, hb⟩ := exists_actualPrincipal_main_gaussian_bound K S hcomplex
    P omega psi hpsi hB hB1 he he1 hboundary
  let f : ℂ → ℂ := fun s =>
    actualPrincipalWeightedTerm K S psi Z s (principalCorrection K S P psi s)
  have hdecay : ∀ s ∈ comparisonClosedStrip (B + e) 2,
      ‖f s‖ ≤ (4 * C * Z ^ (2 - 11 / 16 : ℝ)) * (1 + |s.im|) ^ (-2 : ℝ) := by
    intro s hs
    have hsv : vertical s.re s.im = s := Complex.re_add_im s
    have hpoint := hb Z hZpos s.re ⟨hs.1, hs.2⟩ s.im
    rw [hsv] at hpoint
    have hp : Z ^ (s.re - 11 / 16) ≤ Z ^ (2 - 11 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hs.2])
    apply hpoint.trans
    calc
      _ ≤ (C * Z ^ (2 - 11 / 16 : ℝ)) *
          (4 * (1 + |s.im|) ^ (-2 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le)
          (actual_halfGaussian_polynomial_decay s.im) (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  have hshift := verticalIntegral_eq_of_strip_decay (B + e) 2
    (4 * C * Z ^ (2 - 11 / 16 : ℝ)) f (rightHalfPlane B)
    (by linarith) (by positivity) (isOpen_rightHalfPlane B)
    (by intro s hs; show B < s.re; linarith [hs.1])
    (differentiableOn_actualPrincipal_main K S P omega psi hpsi hB hZpos hboundary) hdecay
  simpa only [principalLineProbe, f, actualPrincipalWeightedTerm, vertical,
    Complex.ofReal_ofNat] using congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z) hshift

/-- A Gaussian point bound gives a uniform tail beyond either endpoint.
This helper assumes no contour relation. -/
theorem actual_gaussian_integral_tail_bound
    (f : ℝ → ℂ) (hf : Measurable f) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hbound : ∀ t : ℝ, ‖f t‖ ≤ M * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :
    ‖(∫ t : ℝ, f t) - ∫ t : ℝ in Icc (-H) H, f t‖ ≤
      M * Real.exp (-(1 / 4 : ℝ) * H ^ 2) *
        (∫ t : ℝ, Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by
  have hg : Integrable (fun t : ℝ => Real.exp (-(1 / 4 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hi : Integrable f :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul M).mono'
      hf.aestronglyMeasurable (ae_of_all _ hbound)
  have htail : ∀ t ∈ (Icc (-H) H)ᶜ,
      ‖f t‖ ≤ (M * Real.exp (-(1 / 4 : ℝ) * H ^ 2)) *
        Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
    intro t ht
    have habs : H ≤ |t| := by
      by_contra! hn
      exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hsq : H ^ 2 ≤ t ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hH (abs_nonneg t)).mpr habs
    apply (hbound t).trans
    calc
      M * Real.exp (-(1 / 2 : ℝ) * t ^ 2) ≤
          M * Real.exp (-(1 / 4 : ℝ) * H ^ 2 + -(1 / 4 : ℝ) * t ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hM
      _ = _ := by rw [Real.exp_add]; ring
  rw [← setIntegral_compl measurableSet_Icc hi]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ t in (Icc (-H) H)ᶜ, ‖f t‖) ≤
        ∫ t in (Icc (-H) H)ᶜ,
          (M * Real.exp (-(1 / 4 : ℝ) * H ^ 2)) * Real.exp (-(1 / 4 : ℝ) * t ^ 2) :=
      integral_mono_ae hi.norm.integrableOn
        ((hg.const_mul _).integrableOn)
        (ae_restrict_of_forall_mem measurableSet_Icc.compl htail)
    _ = (M * Real.exp (-(1 / 4 : ℝ) * H ^ 2)) *
        ∫ t in (Icc (-H) H)ᶜ, Real.exp (-(1 / 4 : ℝ) * t ^ 2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hg (ae_of_all _ (fun t => Real.exp_nonneg _))) (by positivity)

def actualPrincipalMainTail
    (P : ProbeData K S) (psi : HeckeCharacter K) (Z H sigma : ℝ) : ℂ :=
  actualPrincipalLineTruncation K S P psi Z H sigma - principalLineProbe K S P psi Z

/-- The finite main term is normalized to the original untruncated
principal probe with a Gaussian tail on the original common line. -/
theorem exists_actualPrincipal_main_tail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z H : ℝ, 1 ≤ Z → 0 ≤ H →
      ‖actualPrincipalMainTail K S P psi Z H (B + e)‖ ≤
        C * Z ^ (B + e - 11 / 16) * Real.exp (-(1 / 4 : ℝ) * H ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_actualPrincipal_main_gaussian_bound K S hcomplex
    P omega psi hpsi hB hB1 he he1 hboundary
  let G : ℝ := ∫ t : ℝ, Real.exp (-(1 / 4 : ℝ) * t ^ 2)
  have hG : 0 ≤ G := integral_nonneg (fun t => Real.exp_nonneg _)
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  have hkappa : 0 < kappa := norm_pos_iff.mpr (inv_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  refine ⟨kappa * C * (G + 1), by positivity, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let f : ℝ → ℂ := fun t => actualPrincipalWeightedTerm K S psi Z (vertical (B + e) t)
    (principalCorrection K S P psi (vertical (B + e) t))
  have hf : Measurable f :=
    (measurable_actualPrincipalWeightedTerm K S psi Z hZpos _
      (measurable_actual_principalCorrection K S P psi)).comp
      (by unfold vertical; fun_prop)
  have hpoint : ∀ t, ‖f t‖ ≤
      (C * Z ^ (B + e - 11 / 16)) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) :=
    hb Z hZpos (B + e) ⟨le_rfl, by linarith⟩
  have htail := actual_gaussian_integral_tail_bound f hf
    (C * Z ^ (B + e - 11 / 16)) H (by positivity) hH hpoint
  have hline := actualPrincipal_main_line_eq K S hcomplex P omega psi hpsi
    hB hB1 he he1 hZ hboundary
  have heq : actualPrincipalMainTail K S P psi Z H (B + e) =
      -(2 * (Real.pi : ℂ))⁻¹ *
        ((∫ t : ℝ, f t) - ∫ t : ℝ in Icc (-H) H, f t) := by
    unfold actualPrincipalMainTail actualPrincipalLineTruncation
    rw [← hline]
    change _ * (∫ t : ℝ in Icc (-H) H, f t) - _ * (∫ t : ℝ, f t) = _
    ring
  rw [heq, norm_mul, norm_neg]
  calc
    _ ≤ kappa * ((C * Z ^ (B + e - 11 / 16)) *
        Real.exp (-(1 / 4 : ℝ) * H ^ 2) * G) :=
      mul_le_mul_of_nonneg_left htail hkappa.le
    _ ≤ kappa * ((C * Z ^ (B + e - 11 / 16)) *
        Real.exp (-(1 / 4 : ℝ) * H ^ 2) * (G + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hkappa.le
      exact mul_le_mul_of_nonneg_left (by linarith : G ≤ G + 1) (by positivity)
    _ = _ := by ring

/-- The actual double residue separates into the retained common-line
slot error and the proved main Gaussian tail by a literal identity. -/
theorem actualDoubleResidue_sub_principal_eq
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H sigma : ℝ) :
    actualDoubleResidueLineTruncation K S P psi g Z H sigma - principalLineProbe K S P psi Z =
      actualPrincipalSlotRemainder K S P psi g Z H sigma +
        actualPrincipalMainTail K S P psi Z H sigma := by
  unfold actualPrincipalSlotRemainder actualPrincipalMainTail
  ring

end Expansion.Project

#print axioms Expansion.Project.actualPrincipal_main_line_eq
#print axioms Expansion.Project.exists_actualPrincipal_main_tail_bound
#print axioms Expansion.Project.actualDoubleResidue_sub_principal_eq
