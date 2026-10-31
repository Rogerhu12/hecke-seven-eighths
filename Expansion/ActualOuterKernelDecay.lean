import Expansion.ActualMellinStripDecay
import Expansion.ActualOuterCorrectionStrip
import Expansion.ActualRowStripBounds
import Expansion.ActualPrimeNormalizer
import HeckeSkeleton.HighBinSupport.BoundaryRectangle

/-!
# Arbitrary height decay of the complete actual outer-row kernel

The coupled Gaussian is combined with the uniformly rapidly decreasing
actual additive Mellin profile, and the denominator Mellin transform
absorbs the numerator's height growth.  The literal full correction and
the proved prime-normalizer inverse remain in the calculation.  A coarse
fixed Z power is retained only for horizontal and truncation budgets.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeDeletedEulerControl HeckeSkeleton.Expansion.SmallRows
open HighBinBoundary
open scoped Classical BigOperators Topology

def tripleHeightWeight (n : ℕ) (s w z : ℝ) : ℝ :=
  (1 + |s|) ^ n * (1 + |w|) ^ n * (1 + |z|) ^ n

theorem tripleHeightWeight_nonneg (n : ℕ) (s w z : ℝ) :
    0 ≤ tripleHeightWeight n s w z := by unfold tripleHeightWeight; positivity

/-- Rapid z-profile decay covers the opposite-height Gaussian corner as
well as the direct z tail.  Every coordinate receives the same order. -/
theorem coupled_three_height_bound (n ms mw : ℕ) (s w z a d Ca Cd : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hCa : 0 ≤ Ca)
    (hadd : (1 + |z|) ^ (2 * n + ms) * a ≤ Ca)
    (hden : (1 + |w|) ^ (n + mw) * d ≤ Cd) :
    tripleHeightWeight n s w z *
      (Real.exp (-((s + z) ^ 2)) * a * d * (1 + |s|) ^ ms * (1 + |w|) ^ mw) ≤
      HighBinBoundary.gaussianMoment (n + ms) * Ca * Cd := by
  have hp : (1 + |s|) ^ (n + ms) ≤
      (1 + |s + z|) ^ (n + ms) * (1 + |z|) ^ (n + ms) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (HighBinBoundary.coupled_height_le s z) _
  calc
    _ = ((1 + |s|) ^ (n + ms) * Real.exp (-((s + z) ^ 2))) *
        ((1 + |z|) ^ n * a) * ((1 + |w|) ^ (n + mw) * d) := by
      unfold tripleHeightWeight
      simp only [pow_add]
      ring
    _ ≤ (((1 + |s + z|) ^ (n + ms) * (1 + |z|) ^ (n + ms)) *
        Real.exp (-((s + z) ^ 2))) * ((1 + |z|) ^ n * a) *
          ((1 + |w|) ^ (n + mw) * d) := by gcongr
    _ = ((1 + |s + z|) ^ (n + ms) * Real.exp (-((s + z) ^ 2))) *
        ((1 + |z|) ^ (2 * n + ms) * a) * ((1 + |w|) ^ (n + mw) * d) := by
      rw [show 2 * n + ms = (n + ms) + n by omega, pow_add]
      ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul (HighBinBoundary.gaussian_weighted_bound (n + ms) (s + z)) hadd
        (by positivity) (HighBinBoundary.gaussianMoment_pos _).le)
      hden (by positivity) (mul_nonneg (HighBinBoundary.gaussianMoment_pos _).le hCa)

def outerBoundaryScalePower (sUpper wUpper zUpper : ℝ) : ℝ :=
  17 / 96 + (sUpper + zUpper) + (23 / 48) * wUpper + zUpper / 6 + 1

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
local notation "muS" => (fun p : Sset => mu p.val)

include nu in
/-- Arithmetic converter for the actual kernel.  Its only varying
factor premises are the separate actual L numerator and reciprocal;
the Mellin, full-correction and normalizer estimates are proved sources.
The subsequent two outer-range theorems supply both L premises. -/
theorem exists_actual_outer_kernel_rapid_of_L_bounds
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry)
    (sLower sUpper wLower wUpper zLower zUpper : ℝ)
    (hsLower : 7 / 8 ≤ sLower) (hsRange : sLower ≤ sUpper)
    (hwLower : 1 / 2 ≤ wLower) (hwRange : wLower ≤ wUpper)
    (hzLower : 17 / 50 ≤ zLower) (hzRange : zLower ≤ zUpper) (hzUpper : 1 ≤ zUpper)
    (pnum prec eta Cnum Crec : ℝ) (kn kr : ℕ)
    (heta : 0 < eta) (hCnum : 0 < Cnum) (hCrec : 0 < Crec)
    (hnum : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ w : ℂ, wLower ≤ w.re → w.re ≤ wUpper →
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u)
          (exceptionalPrimes K Sset) w‖ ≤
          Cnum * frequencyRowNorm K Sset u ^ pnum * (1 + |w.im|) ^ kn)
    (hrec : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ s : ℂ, sLower ≤ s.re → s.re ≤ sUpper →
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖ ≤
          Crec * frequencyRowNorm K Sset u ^ prec * (1 + |s.im|) ^ kr)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u → ∀ s w z : ℂ,
        sLower ≤ s.re → s.re ≤ sUpper → wLower ≤ w.re → w.re ≤ wUpper →
        zLower ≤ z.re → z.re ≤ zUpper →
        tripleHeightWeight n s.im w.im z.im *
          ‖compensatedRowMellinKernel K Sset muS P psi
            (arithmeticHighEulerData K Sset P psi) g ∅ u Z s w z‖ ≤
          C * Z ^ (outerBoundaryScalePower sUpper wUpper zUpper) *
            frequencyRowNorm K Sset u ^ (pnum + prec + eta - zLower) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_strip_rapid_bound K S mu nu
    P.additive zLower zUpper (by linarith) hzRange (2 * n + kr)
  obtain ⟨Cd, hCd, hd⟩ := ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest wLower wUpper (n + kn)
  obtain ⟨Ch, Zh, hCh, hZh, hh⟩ := exists_actual_outer_fullCorrection_strip_bound
    K Sset g hzUpper heta
  obtain ⟨Zn, hZn, hn⟩ := exists_actual_primeNormalizer_inverse_bound K Sset hcomplex g
    1 zero_lt_one
  obtain ⟨Cl, hCl, hl⟩ := exists_uniform_rightHalfPlane_bound K 2 (by norm_num)
  let Fz : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hFz : 0 < Fz := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  let Cg : ℝ := Real.exp ((sUpper + zUpper + 1) ^ 2)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let C0 : ℝ := Cp * Cg * (Fz * Cl) * Cnum * Crec * Ch * Cm
  have hC0 : 0 ≤ C0 := by dsimp [C0, Cp, Cg, Cm]; positivity
  let D : ℝ := HighBinBoundary.gaussianMoment (n + kr) * Ca * Cd
  have hD : 0 < D := mul_pos (mul_pos (HighBinBoundary.gaussianMoment_pos _) hCa) hCd
  refine ⟨(C0 + 1) * D, max Zh Zn, by positivity, hZh.trans (le_max_left _ _), ?_⟩
  intro Z hZ u hu s w z hs hs' hw hw' hz hz'
  have hZ1 : 1 ≤ Z := hZh.trans ((le_max_left _ _).trans hZ)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hN1 : 1 ≤ frequencyRowNorm K Sset u := one_le_idealNorm K u.ideal.val
  have hNpos : 0 < frequencyRowNorm K Sset u := zero_lt_one.trans_le hN1
  have hnormal : ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ ≤ Z := by
    simpa only [Real.rpow_one] using (hn Z ((le_max_right _ _).trans hZ)).2
  have hc := hh Z ((le_max_left _ _).trans hZ) P psi hcal hunram ∅ u s w z
    (hsLower.trans hs) (hwLower.trans hw) (hzLower.trans hz) hz'
  have hnum' := hnum u hu w hw hw'
  have hrec' := hrec u hu s hs hs'
  have hadd : (1 + |z.im|) ^ (2 * n + kr) * ‖additiveMellin K Sset muS P.additive z‖ ≤ Ca := by
    simpa only [Complex.re_add_im] using ha z.re ⟨hz, hz'⟩ z.im
  have hden : (1 + |w.im|) ^ (n + kn) * ‖mellin P.denominator.toFun w‖ ≤ Cd := by
    simpa only [Complex.re_add_im] using hd w.re w.im hw hw'
  have hzet : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤ Fz * Cl := by
    have hz2 : 2 ≤ (6 * z).re := by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) 1 (6 * z) (by linarith))
      (hl 1 (6 * z) hz2) (norm_nonneg _) hFz.le
  have hgauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤
      Cg * Real.exp (-((s.im + z.im) ^ 2)) := by
    have hsum : 0 ≤ s.re + z.re - 1 := by linarith
    have hsquare : (s.re + z.re - 1) ^ 2 ≤ (sUpper + zUpper + 1) ^ 2 :=
      pow_le_pow_left₀ hsum (by linarith) 2
    have heq : ((s + z - 1) ^ 2).re =
        (s.re + z.re - 1) ^ 2 - (s.im + z.im) ^ 2 := by
      simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re,
        Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero]
    rw [Complex.norm_exp, heq, sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsquare) (Real.exp_nonneg _)
  have hNpow : ‖(frequencyRowNorm K Sset u : ℂ) ^ (-z)‖ ≤
      frequencyRowNorm K Sset u ^ (-zLower) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hXpow : ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ ≤ Z ^ (17 / 96 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _),
      ← Real.rpow_mul hZpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hZpow : ‖(Z : ℂ) ^ (s + z - 1)‖ ≤ Z ^ (sUpper + zUpper) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    linarith
  have hYpow : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ ≤ Z ^ ((23 / 48) * wUpper) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _),
      ← Real.rpow_mul hZpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ1
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hZscale : Z ^ (17 / 96 : ℝ) * Z ^ (sUpper + zUpper) *
      Z ^ ((23 / 48) * wUpper) * Z ^ (zUpper / 6) * Z =
      Z ^ (outerBoundaryScalePower sUpper wUpper zUpper) := by
    calc
      _ = Z ^ (17 / 96 : ℝ) * Z ^ (sUpper + zUpper) *
          Z ^ ((23 / 48) * wUpper) * Z ^ (zUpper / 6) * Z ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos,
          ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
        rfl
  have hNscale : frequencyRowNorm K Sset u ^ (-zLower) *
      frequencyRowNorm K Sset u ^ pnum * frequencyRowNorm K Sset u ^ prec *
      frequencyRowNorm K Sset u ^ eta = frequencyRowNorm K Sset u ^ (pnum + prec + eta - zLower) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  let A : ℝ := outerBoundaryScalePower sUpper wUpper zUpper
  let p : ℝ := pnum + prec + eta - zLower
  let V : ℝ := Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K Sset muS P.additive z‖ *
    ‖mellin P.denominator.toFun w‖ * (1 + |s.im|) ^ kr * (1 + |w.im|) ^ kn
  have hraw : ‖compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ∅ u Z s w z‖ ≤
      (C0 * Z ^ A * frequencyRowNorm K Sset u ^ p) * V := by
    rw [compensatedRowMellinKernel_factorization K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ∅ u Z hZpos s w z]
    simp only [div_eq_mul_inv, mul_inv, norm_mul]
    calc
      _ ≤ Cp * (Cg * Real.exp (-((s.im + z.im) ^ 2))) *
          ‖additiveMellin K Sset muS P.additive z‖ * ‖mellin P.denominator.toFun w‖ *
          frequencyRowNorm K Sset u ^ (-zLower) * Z ^ (17 / 96 : ℝ) *
          Z ^ (sUpper + zUpper) * Z ^ ((23 / 48) * wUpper) *
          ((Fz * Cl) * (Cnum * frequencyRowNorm K Sset u ^ pnum * (1 + |w.im|) ^ kn) *
            (Crec * frequencyRowNorm K Sset u ^ prec * (1 + |s.im|) ^ kr)) *
          (Ch * frequencyRowNorm K Sset u ^ eta * Z ^ (zUpper / 6)) * (Cm * Z) := by gcongr
      _ = C0 *
          (Z ^ (17 / 96 : ℝ) * Z ^ (sUpper + zUpper) * Z ^ ((23 / 48) * wUpper) *
            Z ^ (zUpper / 6) * Z) *
          (frequencyRowNorm K Sset u ^ (-zLower) * frequencyRowNorm K Sset u ^ pnum *
            frequencyRowNorm K Sset u ^ prec * frequencyRowNorm K Sset u ^ eta) * V := by
        dsimp [C0, V]
        ring
      _ = _ := by rw [hZscale, hNscale]
  have hweighted : tripleHeightWeight n s.im w.im z.im * V ≤ D :=
    coupled_three_height_bound n kr kn s.im w.im z.im _ _ Ca Cd
      (norm_nonneg _) (norm_nonneg _) hCa.le hadd hden
  calc
    _ ≤ tripleHeightWeight n s.im w.im z.im *
        ((C0 * Z ^ A * frequencyRowNorm K Sset u ^ p) * V) :=
      mul_le_mul_of_nonneg_left hraw (tripleHeightWeight_nonneg _ _ _ _)
    _ = (C0 * Z ^ A * frequencyRowNorm K Sset u ^ p) *
        (tripleHeightWeight n s.im w.im z.im * V) := by ring
    _ ≤ (C0 * Z ^ A * frequencyRowNorm K Sset u ^ p) * D :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ ((C0 + 1) * D) * Z ^ A * frequencyRowNorm K Sset u ^ p := by
      calc
        _ = C0 * (D * Z ^ A * frequencyRowNorm K Sset u ^ p) := by ring
        _ ≤ (C0 + 1) * (D * Z ^ A * frequencyRowNorm K Sset u ^ p) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

/-- A fixed real height degree can be increased to an integer before any
row, real part, or imaginary part is chosen. -/
theorem shifted_height_rpow_le_nat (c k : ℝ) (n : ℕ) (hc : 1 ≤ c)
    (hk : 0 ≤ k) (hkn : k ≤ n) (t : ℝ) :
    (c + |t|) ^ k ≤ c ^ k * (1 + |t|) ^ n := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have ht0 : 0 ≤ |t| := abs_nonneg t
  calc
    _ ≤ (c * (1 + |t|)) ^ k :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hk
    _ = c ^ k * (1 + |t|) ^ k := Real.mul_rpow hc0 (by positivity)
    _ ≤ c ^ k * (1 + |t|) ^ (n : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hkn) (by positivity)
    _ = _ := by rw [Real.rpow_natCast]

include nu in
/-- Uniform arbitrary height decay on the whole small-row swept tube.
The original packet boundary supplies the actual denominator bound, and
the original arithmetic nonprincipal row supplies the numerator bound.
The constant and scale threshold precede every row and all three heights. -/
theorem exists_actual_small_sweep_kernel_rapid
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u → ∀ s w z : ℂ,
        B + e ≤ s.re → s.re ≤ 5 → 1 / 2 ≤ w.re → w.re ≤ 5 →
        17 / 50 ≤ z.re → z.re ≤ 3 →
        tripleHeightWeight n s.im w.im z.im *
          ‖compensatedRowMellinKernel K Sset muS P psi
            (arithmeticHighEulerData K Sset P psi) g ∅ u Z s w z‖ ≤
          C * Z ^ (outerBoundaryScalePower 5 5 3) *
            frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
  obtain ⟨Cn, hCn, hn⟩ := exists_actual_nonprincipal_numerator_rightStrip K Sset hcomplex
  obtain ⟨Cr, k, hCr, hk, hr⟩ := exists_actual_row_reciprocal_rightStrip K Sset hcomplex
    omega psi hpsi hB hB1 he he1 (eta := 1) zero_lt_one hboundary
  obtain ⟨kr, hkr⟩ := exists_nat_ge k
  let kn : ℕ := 2 * Fintype.card (InfinitePlace K)
  have hnum : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 5 →
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u)
          (exceptionalPrimes K Sset) w‖ ≤
          (Cn * (2 : ℝ) ^ kn) * frequencyRowNorm K Sset u ^ (3 / 5 : ℝ) *
            (1 + |w.im|) ^ kn := by
    intro u hu w hw _hw'
    have hb := hn P (arithmeticRowCharacterInput K Sset P) hAllowed u hu w hw
    have hp : (2 + |w.im|) ^ kn ≤ (2 : ℝ) ^ kn * (1 + |w.im|) ^ kn := by
      simpa only [Real.rpow_natCast] using
        shifted_height_rpow_le_nat 2 (kn : ℝ) kn (by norm_num)
          (Nat.cast_nonneg _) le_rfl w.im
    exact hb.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring))
  have hrec : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ s : ℂ, B + e ≤ s.re → s.re ≤ 5 →
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖ ≤
          (Cr * (4 : ℝ) ^ k) * frequencyRowNorm K Sset u ^ (1 : ℝ) *
            (1 + |s.im|) ^ kr := by
    intro u _hu s hs _hs'
    have hb := hr P (arithmeticRowCharacterInput K Sset P) u s hs
    have hp := shifted_height_rpow_le_nat 4 k kr (by norm_num) hk hkr s.im
    exact hb.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring))
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_outer_kernel_rapid_of_L_bounds
    K S mu nu hcomplex P psi hcal hunram g (B + e) 5 (1 / 2) 5 (17 / 50) 3
    (by linarith) (by linarith) le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
    (3 / 5) 1 1 (Cn * (2 : ℝ) ^ kn) (Cr * (4 : ℝ) ^ k) kn kr
    zero_lt_one (by positivity) (by positivity) hnum hrec n
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  simpa only [show (3 / 5 : ℝ) + 1 + 1 - 17 / 50 = 113 / 50 by norm_num] using hb

def largeSweepLower (zeta : ℝ) : ℝ := min 3 (1 + 3 / zeta)
def largeSweepUpper (zeta : ℝ) : ℝ := max 3 (1 + 3 / zeta)
def largeSweepRowPower (zeta : ℝ) : ℝ := -(largeSweepLower zeta + 1) / 2

theorem one_lt_largeSweepLower {zeta : ℝ} (hzeta : 0 < zeta) :
    1 < largeSweepLower zeta := by
  unfold largeSweepLower
  apply lt_min (by norm_num)
  have hq : 0 < 3 / zeta := div_pos (by norm_num) hzeta
  linarith

theorem largeSweepRowPower_lt_neg_one {zeta : ℝ} (hzeta : 0 < zeta) :
    largeSweepRowPower zeta < -1 := by
  have hl := one_lt_largeSweepLower hzeta
  unfold largeSweepRowPower
  linarith

include nu in
/-- On the whole large-row swept tube both actual L factors lie in the
absolute Euler region.  The resulting row power is strictly below -1,
so the same uniform bound also supplies the genuine infinite row sum. -/
theorem exists_actual_large_sweep_kernel_rapid
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u → ∀ s w z : ℂ,
        2 ≤ s.re → s.re ≤ 5 → 2 ≤ w.re → w.re ≤ 5 →
        largeSweepLower zeta ≤ z.re → z.re ≤ largeSweepUpper zeta →
        tripleHeightWeight n s.im w.im z.im *
          ‖compensatedRowMellinKernel K Sset muS P psi
            (arithmeticHighEulerData K Sset P psi) g ∅ u Z s w z‖ ≤
          C * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
            frequencyRowNorm K Sset u ^ largeSweepRowPower zeta := by
  obtain ⟨Cl, hCl, hl⟩ := exists_uniform_rightHalfPlane_bound K 2 (by norm_num)
  obtain ⟨Cr, hCr, hr⟩ := exists_deleted_reciprocal_right_bound K Sset
    (sigma := 2) (by norm_num)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  have hnum : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ w : ℂ, 2 ≤ w.re → w.re ≤ 5 →
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u)
          (exceptionalPrimes K Sset) w‖ ≤
          (F * Cl) * frequencyRowNorm K Sset u ^ (0 : ℝ) * (1 + |w.im|) ^ (0 : ℕ) := by
    intro u _hu w hw _hw'
    simp only [Real.rpow_zero, pow_zero, mul_one]
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset)
        (arithmeticRowCharacter K Sset P u) w (by linarith))
      (hl _ w hw) (norm_nonneg _) hF.le
  have hrec : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 →
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖ ≤
          Cr * frequencyRowNorm K Sset u ^ (0 : ℝ) * (1 + |s.im|) ^ (0 : ℕ) := by
    intro u _hu s hs _hs'
    simpa only [Real.rpow_zero, pow_zero, mul_one] using hr _ s hs
  have hlower := one_lt_largeSweepLower hzeta
  have hupper : 3 ≤ largeSweepUpper zeta := le_max_left _ _
  have hrange : largeSweepLower zeta ≤ largeSweepUpper zeta :=
    (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_outer_kernel_rapid_of_L_bounds
    K S mu nu hcomplex P psi hcal hunram g 2 5 2 5
    (largeSweepLower zeta) (largeSweepUpper zeta)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) hrange (by linarith)
    0 0 ((largeSweepLower zeta - 1) / 2) (F * Cl) Cr 0 0
    (by linarith) (mul_pos hF hCl) hCr hnum hrec n
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  simpa only [show (0 : ℝ) + 0 + (largeSweepLower zeta - 1) / 2 - largeSweepLower zeta =
    largeSweepRowPower zeta by unfold largeSweepRowPower; ring] using hb

end Expansion.Project

#print axioms Expansion.Project.exists_actual_small_sweep_kernel_rapid
#print axioms Expansion.Project.exists_actual_large_sweep_kernel_rapid
