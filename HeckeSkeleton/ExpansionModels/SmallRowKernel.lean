import HeckeSkeleton.ExpansionModels.SmallRowMellin
import HeckeSkeleton.ExpansionModels.SmallRowReciprocal
import HeckeSkeleton.ExpansionModels.SmallRowCorrectionSums
import HeckeGeneral.Analysis.FixedBinPointwiseIntegration

/-!
# Actual small-row kernel with its literal prime normalizer

Every factor in the physical three-variable kernel is retained.  The
numerator uses the actual row character and conductor, the reciprocal
includes the bounded pure norm exceptions, and the full correction is the
literal finite-subset arithmetic correction.  The only remaining varying
factor on the right is the inverse of the original prime normalizer.  No
normalizer estimate or final small-row estimate is an input here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeDeletedEulerControl
open scoped Classical BigOperators Topology

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

private theorem small_scale_product (Z B e : ℝ) (hZ : 0 < Z) :
    Z ^ (17 / 300 : ℝ) * Z ^ (B + e - 33 / 50) * Z ^ (-(23 / 96 : ℝ)) *
      Z ^ (17 / 300 : ℝ) = Z ^ (B + e - 629 / 800) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

private theorem small_row_product (N eta : ℝ) (hN : 0 < N) :
    N ^ (-(17 / 50 : ℝ)) * N ^ (3 / 5 : ℝ) * N ^ eta * N ^ eta =
      N ^ (13 / 50 + 2 * eta) := by
  rw [← Real.rpow_add hN, ← Real.rpow_add hN, ← Real.rpow_add hN]
  congr 1
  ring

include nu in
/-- The exact physical small-row kernel, before summing rows or integrating.
Its scale exponent includes the full correction's 17/300 contribution. -/
theorem exists_actual_small_kernel_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧
      ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H → ∀ u : FrequencyRow K Sset,
      ¬principalFrequencyRow K Sset u → ∀ s w z : ℂ,
      s.re = B + e → w.re = 1 / 2 → z.re = 17 / 50 →
      |s.im| ≤ H → |w.im| ≤ H → |z.im| ≤ H →
        ‖compensatedRowMellinKernel K Sset muS P psi
          (arithmeticHighEulerData K Sset P psi) g T u Z s w z‖ ≤
          C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
            Z ^ (B + e - 629 / 800) * frequencyRowNorm K Sset u ^ (13 / 50 + 2 * eta) *
              (1 + H) ^ A := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_line_bound K S mu nu
    P.additive (sigma := 17 / 50) (by norm_num) (by norm_num)
  obtain ⟨Cd, hCd, hd⟩ := exists_actual_denominatorMellin_small_line_bound P.denominator
  obtain ⟨Cn, hCn, hn⟩ := exists_nonprincipal_row_numerator_bound K Sset hcomplex
  obtain ⟨Cr, kr, hCr, hkr, hr⟩ := exists_common_line_row_reciprocal_bound K Sset hcomplex
    omega psi hpsi hB hB1 he he1 heta hboundary
  obtain ⟨Ch, Z0, hCh, hZ0, hh⟩ := exists_actual_small_fullCorrection_bound K Sset g heta
  obtain ⟨Cz, hCz, hzeta⟩ := exists_uniform_rightHalfPlane_bound K 2 (by norm_num)
  let Fz : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hFz : 0 < Fz := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  let kn : ℕ := 2 * Fintype.card (InfinitePlace K)
  let Cg : ℝ := Real.exp ((B + e + 17 / 50 - 1) ^ 2)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let C0 : ℝ := Cp * Cg * Ca * Cd * (Fz * Cz) * Cn * Cr * Ch *
    (2 : ℝ) ^ kn * (4 : ℝ) ^ kr * Cm
  have hC0 : 0 ≤ C0 := by dsimp [C0, Cp, Cg, Cm]; positivity
  refine ⟨C0 + 1, Z0, (kn : ℝ) + kr, by linarith, hZ0, by positivity, ?_⟩
  intro Z H hZ hH u hu s w z hs hw hz hsh hwh _hzh
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hHpos : 0 < 1 + H := by linarith
  have hgauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Cg := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    dsimp only [Cg]
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, hs, hz]
    nlinarith [sq_nonneg (s.im + z.im)]
  have hadd := (ha z hz).2
  have hden := hd w hw
  have hzetare : 2 ≤ (6 * z).re := by simp [hz]; norm_num
  have hzet : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤ Fz * Cz := by
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) 1 (6 * z) (by linarith))
      (hzeta 1 (6 * z) hzetare) (norm_nonneg _) hFz.le
  have hnum0 := hn P (arithmeticRowCharacterInput K Sset P) hAllowed u hu w hw
  have hnum : ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u)
      (exceptionalPrimes K Sset) w‖ ≤
        Cn * frequencyRowNorm K Sset u ^ (3 / 5 : ℝ) *
          ((2 : ℝ) ^ kn * (1 + H) ^ (kn : ℝ)) := by
    apply hnum0.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.rpow_natCast, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity) _ kn
    linarith
  have hrec0 := hr P (arithmeticRowCharacterInput K Sset P) u s hs
  have hrec : ‖(heckeDeletedContinuation K
      (psi * conjugate (arithmeticRowCharacter K Sset P u))
      (exceptionalPrimes K Sset) s)⁻¹‖ ≤
        Cr * frequencyRowNorm K Sset u ^ eta * ((4 : ℝ) ^ kr * (1 + H) ^ kr) := by
    apply hrec0.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.mul_rpow (by norm_num) hHpos.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hkr
  have hcorr := hh Z hZ P psi hcal hunram T u s w z (by linarith) hw.ge hz
  have hNpow : ‖(frequencyRowNorm K Sset u : ℂ) ^ (-z)‖ =
      frequencyRowNorm K Sset u ^ (-(17 / 50 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp only [Complex.neg_re, hz]
  have hXpow : ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ = Z ^ (17 / 300 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, hz]
    rw [← Real.rpow_mul hZpos.le]
    congr 1
    norm_num
  have hZpow : ‖(Z : ℂ) ^ (s + z - 1)‖ = Z ^ (B + e - 33 / 50) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos]
    congr 1
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hs, hz]
    ring
  have hYpow : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ = Z ^ (-(23 / 96 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    norm_num only [Complex.sub_re, Complex.one_re, hw]
    rw [← Real.rpow_mul hZpos.le]
    congr 1
    norm_num
  rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZpos s w z]
  simp only [div_eq_mul_inv, mul_inv, norm_mul, hNpow, hXpow, hZpow, hYpow]
  change Cp * ‖Complex.exp ((s + z - 1) ^ 2)‖ * ‖additiveMellin K Sset muS P.additive z‖ *
      ‖mellin P.denominator.toFun w‖ * frequencyRowNorm K Sset u ^ (-(17 / 50 : ℝ)) *
      Z ^ (17 / 300 : ℝ) * Z ^ (B + e - 33 / 50) * Z ^ (-(23 / 96 : ℝ)) *
      (‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ *
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u) (exceptionalPrimes K Sset) w‖ *
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖) *
      ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z s w z‖ *
      (Cm * ‖(primeNormalizer K Sset g T Z)⁻¹‖) ≤ _
  calc
    _ ≤ Cp * Cg * Ca * Cd * frequencyRowNorm K Sset u ^ (-(17 / 50 : ℝ)) *
        Z ^ (17 / 300 : ℝ) * Z ^ (B + e - 33 / 50) * Z ^ (-(23 / 96 : ℝ)) *
        ((Fz * Cz) * (Cn * frequencyRowNorm K Sset u ^ (3 / 5 : ℝ) *
          ((2 : ℝ) ^ kn * (1 + H) ^ (kn : ℝ))) *
          (Cr * frequencyRowNorm K Sset u ^ eta * ((4 : ℝ) ^ kr * (1 + H) ^ kr))) *
        (Ch * frequencyRowNorm K Sset u ^ eta * Z ^ (17 / 300 : ℝ)) *
        (Cm * ‖(primeNormalizer K Sset g T Z)⁻¹‖) := by
      gcongr
    _ = C0 * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        (Z ^ (17 / 300 : ℝ) * Z ^ (B + e - 33 / 50) * Z ^ (-(23 / 96 : ℝ)) *
          Z ^ (17 / 300 : ℝ)) *
        (frequencyRowNorm K Sset u ^ (-(17 / 50 : ℝ)) *
          frequencyRowNorm K Sset u ^ (3 / 5 : ℝ) * frequencyRowNorm K Sset u ^ eta *
            frequencyRowNorm K Sset u ^ eta) *
        ((1 + H) ^ (kn : ℝ) * (1 + H) ^ kr) := by dsimp only [C0]; ring
    _ = C0 * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        Z ^ (B + e - 629 / 800) * frequencyRowNorm K Sset u ^ (13 / 50 + 2 * eta) *
          (1 + H) ^ ((kn : ℝ) + kr) := by
      rw [small_scale_product Z B e hZpos, small_row_product _ eta hNpos,
        ← Real.rpow_add hHpos]
    _ ≤ _ := by gcongr; linarith

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_small_kernel_bound
