import Expansion.ActualPrincipalUniformDecay
import Expansion.FiniteTripleContourTransport
import HeckeGeneral.Analysis.PowerHeightComparison

/-!
# Power-height tails of the two actual principal residue moves

Each error is the original finite vertical difference minus the actual
residue, integrated over the original remaining finite height variables.
The exponents in the resulting power-height budget are chosen before the
tail order.  No contour estimate is an input to either endpoint theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open DedekindZetaZeroFree DedekindZetaZeroFree.Quantitative.SimplePoleVerticalShift
open scoped Classical Topology

theorem principal_finite_shift_error_bound
    (f : ℂ → ℂ) (a b M H : ℝ) (R : ℂ) (N : ℕ) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (ha : Continuous (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)))
    (hb : Continuous (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * Complex.I)))
    (hba : ∀ t : ℝ, 1 ≤ |t| → ‖f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      M * (1 + |t|) ^ (-((N : ℝ) + 2)))
    (hbb : ∀ t : ℝ, 1 ≤ |t| → ‖f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      M * (1 + |t|) ^ (-((N : ℝ) + 2)))
    (hshift : comparisonVerticalIntegral b f - comparisonVerticalIntegral a f = R) :
    ‖principalFiniteVerticalIntegral b H f - principalFiniteVerticalIntegral a H f - R‖ ≤
      (2 * ‖(2 * (Real.pi : ℂ))⁻¹‖ * M * principalTailEnvelopeMass) * H ^ (-(N : ℝ)) := by
  have hleft := principal_vertical_tail_bound f a M hM N ha hba H hH
  have hright := principal_vertical_tail_bound f b M hM N hb hbb H hH
  have heq : principalFiniteVerticalIntegral b H f - principalFiniteVerticalIntegral a H f - R =
      (comparisonVerticalIntegral a f - principalFiniteVerticalIntegral a H f) -
        (comparisonVerticalIntegral b f - principalFiniteVerticalIntegral b H f) := by
    rw [← hshift]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

private theorem principal_height_volume_bound (H A : ℝ) (n : ℕ) (hH : 0 ≤ H) :
    (1 + H) ^ A * (2 * H) ^ n ≤ (2 : ℝ) ^ n * (1 + H) ^ (A + n) := by
  have hp : 0 < 1 + H := by linarith
  calc
    _ ≤ (1 + H) ^ A * (2 * (1 + H)) ^ n := by gcongr; linarith
    _ = _ := by rw [mul_pow, Real.rpow_add hp, Real.rpow_natCast]; ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

def actualPrincipalWShiftError (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(2 : ℤ)) *
    ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H,
      principalFiniteVerticalIntegral (1 + e) H
        (fun w => actualPrincipalKernelCore K S mu P psi g Z
          (vertical (B + e) ts) w (vertical (1 / 6 + e) tz)
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
      principalFiniteVerticalIntegral (19 / 20) H
        (fun w => actualPrincipalKernelCore K S mu P psi g Z
          (vertical (B + e) ts) w (vertical (1 / 6 + e) tz)
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
      actualPrincipalWResidueKernel K S mu P psi g Z
        (vertical (B + e) ts) (vertical (1 / 6 + e) tz)

def actualPrincipalZShiftError (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ ts in Icc (-H) H,
    principalFiniteVerticalIntegral (1 / 6 + e) H
      (actualPrincipalWResidueKernel K S mu P psi g Z (vertical (B + e) ts)) -
    principalFiniteVerticalIntegral (33 / 200) H
      (actualPrincipalWResidueKernel K S mu P psi g Z (vertical (B + e) ts)) -
    actualPrincipalZRegularPart K S mu P psi g Z (vertical (B + e) ts) (1 / 6) *
      (deletedZetaResidue K Sset / 6)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
theorem actualPrincipal_w_shift_error_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualPrincipalWShiftError K S mu P psi g Z H B e) := by
  obtain ⟨A, Zd, hA, hZd, hd⟩ := exists_actualPrincipal_w_uniform_decay K S mu nu
    hcomplex P omega psi hpsi hunram g hB hB1 he he1 hboundary
  obtain ⟨Zs, hZs, hshift⟩ := actualPrincipal_w_fullLine_shift K S mu hcomplex P psi hunram g he he1
  refine ⟨A + 2, 5, 1, by linarith, zero_lt_one, ?_⟩
  intro tau htau _ N
  obtain ⟨C, hC, hc⟩ := hd (N + 2)
  let D : ℝ := 2 * ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * principalTailEnvelopeMass
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(2 : ℤ))‖
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by positivity) principalTailEnvelopeMass_nonneg
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * (D + 1) * 4, max Zd Zs, by positivity,
    hZd.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hZD : Zd ≤ Z := (le_max_left _ _).trans hZ
  have hZS : Zs ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZd.trans hZD
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let H : ℝ := Z ^ tau
  have hH : 1 ≤ H := Real.one_le_rpow hZ1 htau.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  let M : ℝ := D * Z ^ (5 : ℝ) * (1 + H) ^ A * H ^ (-(N : ℝ))
  have hpoint (ts : ℝ) (hts : ts ∈ Icc (-H) H) (tz : ℝ) (_htz : tz ∈ Icc (-H) H) :
      ‖principalFiniteVerticalIntegral (1 + e) H
        (fun w => actualPrincipalKernelCore K S mu P psi g Z
          (vertical (B + e) ts) w (vertical (1 / 6 + e) tz)
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
      principalFiniteVerticalIntegral (19 / 20) H
        (fun w => actualPrincipalKernelCore K S mu P psi g Z
          (vertical (B + e) ts) w (vertical (1 / 6 + e) tz)
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
      actualPrincipalWResidueKernel K S mu P psi g Z
        (vertical (B + e) ts) (vertical (1 / 6 + e) tz)‖ ≤ M := by
    let s := vertical (B + e) ts
    let z := vertical (1 / 6 + e) tz
    let f : ℂ → ℂ := fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
      (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)
    have hs : s.re = B + e := by simp [s, vertical]
    have hz : z.re = 1 / 6 + e := by simp [z, vertical]
    have hcont (a : ℝ) (hlo : 19 / 20 ≤ a) (ha1 : a ≠ 1) :
        Continuous (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hne : (a : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
        intro hh
        exact ha1 (by simpa using congrArg Complex.re hh)
      have hline : ContinuousAt (fun r : ℝ => (a : ℂ) + (r : ℂ) * Complex.I) t :=
        by fun_prop
      exact (differentiableAt_actualPrincipal_w_kernel K S mu P psi g Z hZpos s z _ hne
        (principal_rectangle_mem_rowEulerRegion s _ z (by rw [hs]; linarith)
          (by simpa using hlo) (by rw [hz]; linarith))).continuousAt.comp hline
    have hdec (a : ℝ) (hlo : 19 / 20 ≤ a) (hhi : a ≤ 1 + e)
        (t : ℝ) (ht : 1 ≤ |t|) :
        ‖f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A) * (1 + |t|) ^ (-((N : ℝ) + 2)) := by
      simpa only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, Nat.cast_add, Nat.cast_ofNat] using
          hc Z hZD s ((a : ℂ) + (t : ℂ) * Complex.I) z hs hz
            (by simpa using hlo) (by simpa using hhi) (by simpa using ht)
    have hb := principal_finite_shift_error_bound f (19 / 20) (1 + e)
      (C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A) H
      (actualPrincipalWResidueKernel K S mu P psi g Z s z) N (by positivity) hH
      (hcont _ le_rfl (by norm_num)) (hcont _ (by linarith) (by linarith))
      (hdec _ le_rfl (by linarith)) (hdec _ (by linarith) le_rfl)
      (hshift Z hZS s z (by rw [hs]; linarith) (by rw [hz]; linarith) (by rw [hz]; linarith))
    apply hb.trans
    have hsH : |s.im| ≤ H := by simpa [s, vertical] using (abs_le.mpr hts : |ts| ≤ H)
    have hheight := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + |s.im|)
      (by linarith : 1 + |s.im| ≤ 1 + H) hA
    dsimp only [M, D]
    nlinarith [mul_le_mul_of_nonneg_left hheight
      (show 0 ≤ (2 * ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * principalTailEnvelopeMass) *
        Z ^ (5 : ℝ) * H ^ (-(N : ℝ)) by positivity)]
  have hi := FiniteTripleContour.norm_double_setIntegral_le _ H M hH0 hpoint
  change ‖(2 * (Real.pi : ℂ)) ^ (-(2 : ℤ)) * _‖ ≤ _
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hi hkappa).trans
  have hv := principal_height_volume_bound H A 2 hH0
  have hcoef : kappa * D ≤ (kappa + 1) * (D + 1) := by nlinarith
  calc
    _ = (kappa * D * Z ^ (5 : ℝ) * H ^ (-(N : ℝ))) * ((1 + H) ^ A * (2 * H) ^ 2) := by
      dsimp only [M, kappa]
      ring
    _ ≤ (kappa * D * Z ^ (5 : ℝ) * H ^ (-(N : ℝ))) *
        (4 * (1 + H) ^ (A + 2)) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hv) (by positivity)
    _ ≤ _ := by
      dsimp only [H]
      nlinarith [mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ 4 * Z ^ (5 : ℝ) * (1 + Z ^ tau) ^ (A + 2) * (Z ^ tau) ^ (-(N : ℝ)) by positivity)]

include nu in
theorem actualPrincipal_z_shift_error_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualPrincipalZShiftError K S mu P psi g Z H B e) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨A, Zd, hA, hZd, hd⟩ := exists_actualPrincipal_z_uniform_decay K S mu nu
    hcomplex P omega psi hpsi hunram g hB hB1 he he1 hboundary
  obtain ⟨Zs, hZs, hshift⟩ := actualPrincipal_z_fullLine_shift K S mu nu hcomplex P psi hunram g he he1
  refine ⟨A + 1, 5, 1, by linarith, zero_lt_one, ?_⟩
  intro tau htau _ N
  obtain ⟨C, hC, hc⟩ := hd (N + 2)
  let D : ℝ := 2 * ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * principalTailEnvelopeMass
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by positivity) principalTailEnvelopeMass_nonneg
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * (D + 1) * 2, max Zd Zs, by positivity,
    hZd.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hZD : Zd ≤ Z := (le_max_left _ _).trans hZ
  have hZS : Zs ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZd.trans hZD
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let H : ℝ := Z ^ tau
  have hH : 1 ≤ H := Real.one_le_rpow hZ1 htau.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  let M : ℝ := D * Z ^ (5 : ℝ) * (1 + H) ^ A * H ^ (-(N : ℝ))
  have hpoint (ts : ℝ) (hts : ts ∈ Icc (-H) H) :
      ‖principalFiniteVerticalIntegral (1 / 6 + e) H
        (actualPrincipalWResidueKernel K S mu P psi g Z (vertical (B + e) ts)) -
      principalFiniteVerticalIntegral (33 / 200) H
        (actualPrincipalWResidueKernel K S mu P psi g Z (vertical (B + e) ts)) -
      actualPrincipalZRegularPart K S mu P psi g Z (vertical (B + e) ts) (1 / 6) *
        (deletedZetaResidue K Sset / 6)‖ ≤ M := by
    let s := vertical (B + e) ts
    let f : ℂ → ℂ := actualPrincipalWResidueKernel K S mu P psi g Z s
    have hs : s.re = B + e := by simp [s, vertical]
    have hcont (a : ℝ) (hlo : 33 / 200 ≤ a) (ha1 : a ≠ 1 / 6) :
        Continuous (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hne : (a : ℂ) + (t : ℂ) * Complex.I ≠ 1 / 6 := by
        intro hh
        exact ha1 (by simpa using congrArg Complex.re hh)
      have hline : ContinuousAt (fun r : ℝ => (a : ℂ) + (r : ℂ) * Complex.I) t :=
        by fun_prop
      exact (differentiableAt_actualPrincipal_z_kernel K S mu nu P psi g Z hZpos s _
        (by simp; linarith) hne
        (principal_rectangle_mem_rowEulerRegion s 1 _ (by rw [hs]; linarith)
          (by norm_num) (by simpa using hlo))).continuousAt.comp hline
    have hdec (a : ℝ) (hlo : 33 / 200 ≤ a) (hhi : a ≤ 1 / 6 + e)
        (t : ℝ) (ht : 1 ≤ |t|) :
        ‖f ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A) * (1 + |t|) ^ (-((N : ℝ) + 2)) := by
      simpa only [f, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, Nat.cast_add, Nat.cast_ofNat] using
          hc Z hZD s ((a : ℂ) + (t : ℂ) * Complex.I) hs
            (by simpa using hlo) (by simpa using hhi) (by simpa using ht)
    have hb := principal_finite_shift_error_bound f (33 / 200) (1 / 6 + e)
      (C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A) H
      (actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) * (deletedZetaResidue K Sset / 6))
      N (by positivity) hH
      (hcont _ le_rfl (by norm_num)) (hcont _ (by linarith) (by linarith))
      (hdec _ le_rfl (by linarith)) (hdec _ (by linarith) le_rfl)
      (hshift Z hZS s (by rw [hs]; linarith))
    apply hb.trans
    have hsH : |s.im| ≤ H := by simpa [s, vertical] using (abs_le.mpr hts : |ts| ≤ H)
    have hheight := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + |s.im|)
      (by linarith : 1 + |s.im| ≤ 1 + H) hA
    dsimp only [M, D]
    nlinarith [mul_le_mul_of_nonneg_left hheight
      (show 0 ≤ (2 * ‖(2 * (Real.pi : ℂ))⁻¹‖ * C * principalTailEnvelopeMass) *
        Z ^ (5 : ℝ) * H ^ (-(N : ℝ)) by positivity)]
  have hi := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) isCompact_Icc.measure_lt_top hpoint
  have hvol : volume.real (Icc (-H) H) = 2 * H := by
    rw [Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  rw [hvol] at hi
  change ‖(2 * (Real.pi : ℂ))⁻¹ * _‖ ≤ _
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hi hkappa).trans
  have hv := principal_height_volume_bound H A 1 hH0
  have hcoef : kappa * D ≤ (kappa + 1) * (D + 1) := by nlinarith
  calc
    _ = (kappa * D * Z ^ (5 : ℝ) * H ^ (-(N : ℝ))) * ((1 + H) ^ A * (2 * H)) := by
      dsimp only [M, kappa]
      ring
    _ ≤ (kappa * D * Z ^ (5 : ℝ) * H ^ (-(N : ℝ))) *
        (2 * (1 + H) ^ (A + 1)) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hv) (by positivity)
    _ ≤ _ := by
      dsimp only [H]
      nlinarith [mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ 2 * Z ^ (5 : ℝ) * (1 + Z ^ tau) ^ (A + 1) * (Z ^ tau) ^ (-(N : ℝ)) by positivity)]

end Expansion.Project

#print axioms Expansion.Project.actualPrincipal_w_shift_error_tail
#print axioms Expansion.Project.actualPrincipal_z_shift_error_tail
