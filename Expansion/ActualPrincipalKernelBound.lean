import Expansion.ActualPrincipalSlotRemainder
import Expansion.PhysicalFrequencyReindex
import HeckeSkeleton.ExpansionModels.PrincipalRowCorrection
import HeckeSkeleton.ExpansionModels.SmallRowMellin

/-!
# The literal principal kernels on the two residue contours

The common core below is the exact factorization of the original principal
row, with only its w-zeta numerator exposed.  The unresidued contour inserts
the actual deleted zeta; the w-residue contour inserts its actual residue.
Every other original Mellin, Euler, Gaussian and normalizer factor remains.
The bound is derived from these primitive factors, with no principal-row
estimate among the hypotheses.  The final residue computation is separate.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.SmallRows
open HeckeSkeleton.Expansion.PrincipalRows HeckeSkeleton.HeckeDeletedEulerControl
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

/-- A fixed line distinct from the actual pole.  The entire norm numerator
provides polynomial growth; the distance to the pole is retained explicitly. -/
theorem exists_actual_deletedZeta_line_bound
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (sigma : ℝ) (hsigma : 1 / 2 ≤ sigma) (hsigma4 : sigma ≤ 4)
    (hsigma1 : sigma ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, s.re = sigma →
      ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) s‖ ≤
        C * (2 + |s.im|) ^ k := by
  obtain ⟨C, k, hC, hk, hbound⟩ := exists_normPoleNumerator_strip_bound K hcomplex 0
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K S)
  have hd : 0 < |sigma - 1| := abs_pos.mpr (sub_ne_zero.mpr hsigma1)
  refine ⟨F * C / |sigma - 1|, k, div_pos (mul_pos hF hC) hd, hk, ?_⟩
  intro s hs
  have hq := hbound s (by linarith) (by linarith)
  have hden : |sigma - 1| ≤ ‖s - 1‖ := by
    simpa only [Complex.sub_re, Complex.one_re, hs] using Complex.abs_re_le_norm (s - 1)
  have hformula : heckeContinuation K (1 : HeckeCharacter K) s =
      normPoleNumerator K 0 s / (s - 1) := by
    simpa [heckeNormTwist, heckeNormPole] using congrFun (heckeContinuation_normTwist_eq K 0) s
  have hfull : ‖heckeContinuation K (1 : HeckeCharacter K) s‖ ≤
      (C * (2 + |s.im|) ^ k) / |sigma - 1| := by
    rw [hformula, norm_div]
    exact div_le_div₀ (by positivity) hq hd hden
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul
    (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K S) 1 s (by linarith))
    hfull (norm_nonneg _) hF.le).trans_eq (by dsimp only [F]; ring)

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

/-- The exact principal-row core; `Wvalue` is the one numerator whose
simple pole is crossed in the first residue step. -/
def actualPrincipalKernelCore (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s w z Wvalue : ℂ) : ℂ :=
  (physicalPoissonScalar K : ℂ) *
    Complex.exp ((s + z - 1) ^ 2) * additiveMellin K Sset muS P.additive z *
    mellin P.denominator.toFun w *
    ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) *
    (Z : ℂ) ^ (s + z - 1) * ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1) *
    (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z) * Wvalue /
      heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s) *
    compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s w z /
    (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z)

theorem actualPrincipalKernel_eq_core (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s w z : ℂ) :
    compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s w z =
        actualPrincipalKernelCore K S mu P psi g Z s w z
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w) := by
  rw [compensatedRowMellinKernel_factorization K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset) Z hZ]
  simp only [physicalPrincipalRow_norm, Complex.ofReal_one, Complex.one_cpow, mul_one,
    arithmeticHighEulerData_character, physicalPrincipalRow_character K Sset P hAllowed,
    map_one]
  rfl

/-- The exact exponents from X=Z^(17/48), Y=Z^(23/48), and all prime slots. -/
theorem actual_principal_scale_product (Z B e w z : ℝ) (hZ : 0 < Z) :
    Z ^ ((17 / 48 : ℝ) * (1 / 2 - z)) * Z ^ (B + e + z - 1) *
      Z ^ ((23 / 48 : ℝ) * (w - 1)) * Z ^ (z / 6) =
        Z ^ (B + e - 79 / 96 + (13 / 16) * z + (23 / 48) * (w - 1)) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

include nu in
/-- Uniform primitive-factor bound.  The w-numerator premise is used only
to specialize to the actual zeta or its fixed arithmetic residue below. -/
theorem exists_actual_principalCore_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e eta wLine zLine : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (heta : 0 < eta) (hwLine : 19 / 20 ≤ wLine)
    (hzLine : 33 / 200 ≤ zLine) (hzLine1 : zLine ≤ 2 / 3)
    (hzPole : 6 * zLine ≠ 1)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (W : ℂ → ℂ) (Cw kw : ℝ) (hCw : 0 < Cw) (hkw : 0 ≤ kw)
    (hW : ∀ w : ℂ, w.re = wLine → ‖W w‖ ≤ Cw * (2 + |w.im|) ^ kw) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ∀ s w z : ℂ,
      s.re = B + e → w.re = wLine → z.re = zLine →
      |s.im| ≤ H → |w.im| ≤ H → |z.im| ≤ H →
      ‖actualPrincipalKernelCore K S mu P psi g Z s w z (W w)‖ ≤
        C * Z ^ (B + e - 79 / 96 + (13 / 16) * zLine +
          (23 / 48) * (wLine - 1) + eta) * (1 + H) ^ A := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_line_bound K S mu nu P.additive
    (sigma := zLine) (by linarith) (by linarith)
  obtain ⟨Cd, hCd, hd⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest wLine wLine 0
  obtain ⟨Cz, kz, hCz, hkz, hzeta⟩ := exists_actual_deletedZeta_line_bound K Sset hcomplex
    (6 * zLine) (by linarith) (by linarith) hzPole
  obtain ⟨Cr, kr, hCr, hkr, hrecip⟩ := exists_actual_target_common_line_reciprocal_bound
    K Sset hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨Ch, Zh, hCh, hZh, hcorr⟩ := exists_actual_principal_fullCorrection_bound K Sset g
  obtain ⟨Zn, hZn, hnorm⟩ := exists_actual_primeNormalizer_inverse_bound K Sset hcomplex g eta heta
  let Cg : ℝ := Real.exp ((B + e + zLine - 1) ^ 2)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let C0 : ℝ := Cp * Cg * Ca * Cd * Cz * (6 : ℝ) ^ kz *
    Cw * (2 : ℝ) ^ kw * Cr * (4 : ℝ) ^ kr * Ch * Cm
  have hC0 : 0 ≤ C0 := by dsimp [C0, Cp, Cg, Cm]; positivity
  refine ⟨C0 + 1, max Zh Zn, kz + kw + kr, by linarith,
    hZh.trans (le_max_left _ _), by linarith, ?_⟩
  intro Z H hZ hH s w z hs hw hz hsh hwh hzh
  have hZ1 : 1 ≤ Z := hZh.trans ((le_max_left _ _).trans hZ)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hHpos : 0 < 1 + H := by linarith
  have hg : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Cg := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    dsimp only [Cg]
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, hs, hz]
    nlinarith [sq_nonneg (s.im + z.im)]
  have had := (ha z hz).2
  have hwd : ‖mellin P.denominator.toFun w‖ ≤ Cd := by
    have heq : (wLine : ℂ) + (w.im : ℂ) * Complex.I = w := by
      apply Complex.ext <;> simp [hw]
    simpa only [pow_zero, one_mul, heq] using hd wLine w.im le_rfl le_rfl
  have hzet : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤
      Cz * (6 : ℝ) ^ kz * (1 + H) ^ kz := by
    have hb := hzeta (6 * z) (by simp [hz])
    apply hb.trans
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hHpos.le]
    apply mul_le_mul_of_nonneg_left _ hCz.le
    apply Real.rpow_le_rpow (by positivity) _ hkz
    have hi : |(6 * z).im| = 6 * |z.im| := by simp [abs_mul]
    rw [hi]
    linarith
  have hwv : ‖W w‖ ≤ Cw * (2 : ℝ) ^ kw * (1 + H) ^ kw := by
    apply (hW w hw).trans
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hHpos.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hkw) hCw.le
  have hr : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s)⁻¹‖ ≤
      Cr * (4 : ℝ) ^ kr * (1 + H) ^ kr := by
    apply (hrecip s hs).trans
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hHpos.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hkr) hCr.le
  have hh := hcorr Z ((le_max_left _ _).trans hZ) P psi hunram ∅
    (physicalPrincipalRow K Sset) (physicalPrincipalRow_support K Sset) s w z
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hz] at hh
  have hn := (hnorm Z ((le_max_right _ _).trans hZ)).2
  have hx : ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ =
      Z ^ ((17 / 48 : ℝ) * (1 / 2 - zLine)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, hz]
    exact (Real.rpow_mul hZpos.le _ _).symm
  have hzpow : ‖(Z : ℂ) ^ (s + z - 1)‖ = Z ^ (B + e + zLine - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hs, hz]
  have hy : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ =
      Z ^ ((23 / 48 : ℝ) * (wLine - 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    simp only [Complex.sub_re, Complex.one_re, hw]
    exact (Real.rpow_mul hZpos.le _ _).symm
  simp only [actualPrincipalKernelCore, div_eq_mul_inv, mul_inv, norm_mul, hx, hzpow, hy]
  calc
    _ ≤ Cp * Cg * Ca * Cd * Z ^ ((17 / 48 : ℝ) * (1 / 2 - zLine)) *
        Z ^ (B + e + zLine - 1) * Z ^ ((23 / 48 : ℝ) * (wLine - 1)) *
        ((Cz * 6 ^ kz * (1 + H) ^ kz) * (Cw * 2 ^ kw * (1 + H) ^ kw) *
          (Cr * 4 ^ kr * (1 + H) ^ kr)) * (Ch * Z ^ (zLine / 6)) *
        (Cm * Z ^ eta) := by
      change Cp * _ * _ * _ * _ * _ * _ * (_ * _ * _) * _ * (Cm * _) ≤ _
      gcongr
    _ = C0 *
        (Z ^ ((17 / 48 : ℝ) * (1 / 2 - zLine)) * Z ^ (B + e + zLine - 1) *
          Z ^ ((23 / 48 : ℝ) * (wLine - 1)) * Z ^ (zLine / 6)) * Z ^ eta *
        (((1 + H) ^ kz * (1 + H) ^ kw) * (1 + H) ^ kr) := by dsimp [C0]; ring
    _ = C0 * Z ^ (B + e - 79 / 96 + (13 / 16) * zLine +
        (23 / 48) * (wLine - 1) + eta) * (1 + H) ^ (kz + kw + kr) := by
      rw [actual_principal_scale_product Z B e wLine zLine hZpos,
        ← Real.rpow_add hHpos, ← Real.rpow_add hHpos, mul_assoc C0,
        ← Real.rpow_add hZpos]
    _ ≤ _ := by gcongr; linarith

end Expansion.Project

#print axioms Expansion.Project.exists_actual_deletedZeta_line_bound
#print axioms Expansion.Project.actualPrincipalKernel_eq_core
#print axioms Expansion.Project.exists_actual_principalCore_bound
