import HeckeSkeleton.ExpansionModels.LargeRowMellin
import HeckeSkeleton.ExpansionModels.LargeRowAllScales
import HeckeSkeleton.ExpansionModels.SmallRowReciprocal
import HeckeGeneral.Analysis.FixedBinPointwiseIntegration

/-!
# The literal absolute large-row kernel

On (2,2,sigma), all three deleted L-factors are uniformly controlled by
their actual Euler series and logarithm.  Both fixed Mellin factors are
proved integrable and bounded.  The true physical Poisson scalar and
normalizer are retained, as is the original full correction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.LargeRows

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeDeletedEulerControl HeckeSkeleton.Expansion.SmallRows
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

include nu in
/-- All scalar factors of the actual kernel, uniformly on the complete
three vertical lines.  The remaining correction is displayed literally. -/
theorem exists_actual_large_kernel_scalar_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z → ∀ (u : FrequencyRow K Sset) (s w z : ℂ),
      s.re = 2 → w.re = 2 → z.re = sigma →
        ‖compensatedRowMellinKernel K Sset muS P psi
          (arithmeticHighEulerData K Sset P psi) g T u Z s w z‖ ≤
          C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
            Z ^ (53 / 32 + (31 / 48) * sigma) * frequencyRowNorm K Sset u ^ (-sigma) *
              ‖compensatedRowFullCorrection K Sset P psi
                (arithmeticHighEulerData K Sset P psi) g T u Z s w z‖ := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_positive_line_bound K S mu nu
    P.additive (lt_of_lt_of_le zero_lt_one hsigma)
  obtain ⟨Cd, hCd, hd⟩ := exists_actual_denominatorMellin_line_bound P.denominator 2
  obtain ⟨Cl, hCl, hl⟩ := exists_uniform_rightHalfPlane_bound K 2 (by norm_num)
  obtain ⟨Cr, hCr, hr⟩ := exists_deleted_reciprocal_right_bound K Sset (sigma := 2) (by norm_num)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  have hdel (chi : HeckeCharacter K) (s : ℂ) (hs : 2 ≤ s.re) :
      ‖heckeDeletedContinuation K chi (exceptionalPrimes K Sset) s‖ ≤ F * Cl := by
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) chi s (by linarith))
      (hl chi s hs) (norm_nonneg _) hF.le
  let Cg : ℝ := Real.exp ((sigma + 1) ^ 2)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let C0 : ℝ := Cp * Cg * Ca * Cd * ((F * Cl) * (F * Cl) * Cr) * Cm
  have hC0 : 0 ≤ C0 := by dsimp [C0, Cp, Cg, Cm]; positivity
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro Z hZ u s w z hs hw hz
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hgauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Cg := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    dsimp only [Cg]
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, hs, hz]
    nlinarith [sq_nonneg (s.im + z.im)]
  have hadd := (ha z hz).2
  have hden := hd w hw
  have hzet := hdel 1 (6 * z) (by simp [hz]; linarith)
  have hnum := hdel (arithmeticRowCharacter K Sset P u) w hw.ge
  have hrec := hr (psi * conjugate (arithmeticRowCharacter K Sset P u)) s hs.ge
  have hNpow : ‖(frequencyRowNorm K Sset u : ℂ) ^ (-z)‖ = frequencyRowNorm K Sset u ^ (-sigma) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp only [Complex.neg_re, hz]
  have hXpow : ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ =
      Z ^ ((17 / 48) * (1 / 2 - sigma)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZ _)]
    norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, hz]
    rw [← Real.rpow_mul hZ.le]
  have hZpow : ‖(Z : ℂ) ^ (s + z - 1)‖ = Z ^ (1 + sigma) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    congr 1
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hs, hz]
    ring
  have hYpow : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ = Z ^ (23 / 48 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZ _)]
    rw [show (w - 1).re = 1 by simp [hw], Real.rpow_one]
  have hscale : Z ^ ((17 / 48) * (1 / 2 - sigma)) * Z ^ (1 + sigma) *
      Z ^ (23 / 48 : ℝ) = Z ^ (53 / 32 + (31 / 48) * sigma) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z hZ s w z]
  simp only [div_eq_mul_inv, mul_inv, norm_mul, hNpow, hXpow, hZpow, hYpow]
  change Cp * ‖Complex.exp ((s + z - 1) ^ 2)‖ * ‖additiveMellin K Sset muS P.additive z‖ *
      ‖mellin P.denominator.toFun w‖ * frequencyRowNorm K Sset u ^ (-sigma) *
      Z ^ ((17 / 48) * (1 / 2 - sigma)) * Z ^ (1 + sigma) * Z ^ (23 / 48 : ℝ) *
      (‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ *
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u) (exceptionalPrimes K Sset) w‖ *
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖) *
      ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z s w z‖ * (Cm * ‖(primeNormalizer K Sset g T Z)⁻¹‖) ≤ _
  calc
    _ ≤ Cp * Cg * Ca * Cd * frequencyRowNorm K Sset u ^ (-sigma) *
        Z ^ ((17 / 48) * (1 / 2 - sigma)) * Z ^ (1 + sigma) * Z ^ (23 / 48 : ℝ) *
        ((F * Cl) * (F * Cl) * Cr) *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g T u Z s w z‖ * (Cm * ‖(primeNormalizer K Sset g T Z)⁻¹‖) := by gcongr
    _ = C0 * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        (Z ^ ((17 / 48) * (1 / 2 - sigma)) * Z ^ (1 + sigma) * Z ^ (23 / 48 : ℝ)) *
        frequencyRowNorm K Sset u ^ (-sigma) *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g T u Z s w z‖ := by dsimp only [C0]; ring
    _ ≤ _ := by rw [hscale]; gcongr; linarith

include nu in
/-- The complete pointwise large-row estimate, including the exact full
correction power and the original prime-normalizer inverse. -/
theorem exists_actual_large_kernel_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {sigma eta : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (u : FrequencyRow K Sset) (s w z : ℂ), s.re = 2 → w.re = 2 → z.re = sigma →
        ‖compensatedRowMellinKernel K Sset muS P psi
          (arithmeticHighEulerData K Sset P psi) g T u Z s w z‖ ≤
          C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
            Z ^ (53 / 32 + (13 / 16) * sigma) * frequencyRowNorm K Sset u ^ (eta - sigma) := by
  obtain ⟨Ca, hCa, hscalar⟩ := exists_actual_large_kernel_scalar_bound K S mu nu hcomplex P psi g T hsigma
  obtain ⟨Ch, Z0, hCh, hZ0, hc⟩ := exists_actual_large_fullCorrection_bound K Sset g hsigma heta
  refine ⟨Ca * Ch, Z0, mul_pos hCa hCh, hZ0, ?_⟩
  intro Z hZ u s w z hs hw hz
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hh := hc Z hZ P psi hcal hunram T u s w z (by linarith) (by linarith) hz
  apply (hscalar Z hZpos u s w z hs hw hz).trans
  calc
    _ ≤ Ca * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        Z ^ (53 / 32 + (31 / 48) * sigma) * frequencyRowNorm K Sset u ^ (-sigma) *
        (Ch * frequencyRowNorm K Sset u ^ eta * Z ^ (sigma / 6)) := by gcongr
    _ = (Ca * Ch) * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        (Z ^ (53 / 32 + (31 / 48) * sigma) * Z ^ (sigma / 6)) *
        (frequencyRowNorm K Sset u ^ (-sigma) * frequencyRowNorm K Sset u ^ eta) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZpos, ← Real.rpow_add hNpos]
      rw [show (53 / 32 : ℝ) + (31 / 48) * sigma + sigma / 6 =
        53 / 32 + (13 / 16) * sigma by ring,
        show -sigma + eta = eta - sigma by ring]

include nu in
/-- A row-subpower bound at every original positive scale, sufficient for
actual infinite summability even before the common asymptotic cutoff. -/
theorem exists_actual_large_kernel_all_scales_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {sigma eta : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 0 < Z →
      ∀ (u : FrequencyRow K Sset) (s w z : ℂ), s.re = 2 → w.re = 2 → z.re = sigma →
        ‖compensatedRowMellinKernel K Sset muS P psi
          (arithmeticHighEulerData K Sset P psi) g T u Z s w z‖ ≤
          (C * largeCorrectionMass K Sset g T Z sigma * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
            Z ^ (53 / 32 + (31 / 48) * sigma)) * frequencyRowNorm K Sset u ^ (eta - sigma) := by
  obtain ⟨Ca, hCa, hscalar⟩ := exists_actual_large_kernel_scalar_bound K S mu nu hcomplex P psi g T hsigma
  obtain ⟨Ch, hCh, hc⟩ := exists_actual_large_fullCorrection_all_scales_bound K Sset heta
  refine ⟨Ca * Ch, mul_pos hCa hCh, ?_⟩
  intro Z hZ u s w z hs hw hz
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  have hh := hc g T Z sigma hsigma P psi u s w z hs hw hz
  apply (hscalar Z hZ u s w z hs hw hz).trans
  calc
    _ ≤ Ca * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        Z ^ (53 / 32 + (31 / 48) * sigma) * frequencyRowNorm K Sset u ^ (-sigma) *
        ((Ch * largeCorrectionMass K Sset g T Z sigma) * frequencyRowNorm K Sset u ^ eta) := by gcongr
    _ = ((Ca * Ch) * largeCorrectionMass K Sset g T Z sigma *
        ‖(primeNormalizer K Sset g T Z)⁻¹‖ * Z ^ (53 / 32 + (31 / 48) * sigma)) *
        (frequencyRowNorm K Sset u ^ (-sigma) * frequencyRowNorm K Sset u ^ eta) := by ring
    _ = _ := by rw [← Real.rpow_add hNpos, show -sigma + eta = eta - sigma by ring]

end HeckeSkeleton.Expansion.LargeRows

#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_kernel_scalar_bound
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_kernel_bound
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_kernel_all_scales_bound
