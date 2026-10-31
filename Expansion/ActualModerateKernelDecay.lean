import Expansion.ActualModerateCorrectionBound
import Expansion.ActualModerateSweepHolomorphy
import Expansion.ActualOuterKernelDecay

/-!
# Uniform complete-kernel height decay on every moderate initial sweep

All constants precede the bin endpoint a.  The genuinely negative w
strip uses the original nonprincipal arithmetic numerator, while the
complete finite correction is bounded directly by its actual tuple mass.
The rough fixed Z power is reserved for horizontal and truncation terms.
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

def moderateBoundaryScalePower : ℝ := 17 / 96 + 8 + (23 / 48) * 5 + 19 / 6 + 1

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
/-- Actual arbitrary height decay, uniform before the moderate bin and
its selected rows.  Its only zero premise is the original common packet. -/
theorem exists_actual_moderate_sweep_kernel_rapid
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ B →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u → ∀ s w z : ℂ,
        B + 20 * e ≤ s.re → s.re ≤ 5 → 1 - a - 6 * e ≤ w.re → w.re ≤ 5 →
        17 / 50 ≤ z.re → z.re ≤ 3 →
        tripleHeightWeight n s.im w.im z.im *
          ‖compensatedRowMellinKernel K Sset muS P psi
            (arithmeticHighEulerData K Sset P psi) g ∅ u Z s w z‖ ≤
          C * Z ^ moderateBoundaryScalePower * frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
  obtain ⟨Cn, hCn, hn⟩ := exists_actual_nonprincipal_numerator_moderateStrip K Sset hcomplex
  obtain ⟨Cr, k, hCr, hk, hr⟩ := exists_actual_row_reciprocal_rightStrip K Sset hcomplex
    omega psi hpsi hB hB1 he (by linarith) (eta := 1) zero_lt_one hboundary
  obtain ⟨kr, hkr⟩ := exists_nat_ge k
  let kn : ℕ := 2 * Fintype.card (InfinitePlace K)
  let Cnum : ℝ := Cn * (2 : ℝ) ^ kn
  let Crec : ℝ := Cr * (4 : ℝ) ^ k
  have hCnum : 0 < Cnum := by dsimp [Cnum]; positivity
  have hCrec : 0 < Crec := by dsimp [Crec]; positivity
  let pnum : ℝ := 3 / 5
  let prec : ℝ := 1
  let eta : ℝ := 1
  let sLower : ℝ := B + e
  let sUpper : ℝ := 5
  let wLower : ℝ := -(1 / 1000)
  let wUpper : ℝ := 5
  let zLower : ℝ := 17 / 50
  let zUpper : ℝ := 3
  have hzRange : zLower ≤ zUpper := by norm_num [zLower, zUpper]
  have hnum : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ w : ℂ, wLower ≤ w.re → w.re ≤ wUpper →
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K Sset P u)
          (exceptionalPrimes K Sset) w‖ ≤
          Cnum * frequencyRowNorm K Sset u ^ pnum * (1 + |w.im|) ^ kn := by
    intro u hu w hw _hw'
    have hb := hn P (arithmeticRowCharacterInput K Sset P) hAllowed u hu w hw
    have hp : (2 + |w.im|) ^ kn ≤ (2 : ℝ) ^ kn * (1 + |w.im|) ^ kn := by
      simpa only [Real.rpow_natCast] using shifted_height_rpow_le_nat 2 (kn : ℝ) kn
        (by norm_num) (Nat.cast_nonneg _) le_rfl w.im
    exact hb.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
      (by dsimp [Cnum, pnum]; ring))
  have hrec : ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
      ∀ s : ℂ, sLower ≤ s.re → s.re ≤ sUpper →
        ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K Sset P u))
          (exceptionalPrimes K Sset) s)⁻¹‖ ≤
          Crec * frequencyRowNorm K Sset u ^ prec * (1 + |s.im|) ^ kr := by
    intro u _hu s hs _hs'
    have hb := hr P (arithmeticRowCharacterInput K Sset P) u s hs
    have hp := shifted_height_rpow_le_nat 4 k kr (by norm_num) hk hkr s.im
    exact hb.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
      (by dsimp [Crec, prec]; ring))
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Ca, hCa, hadditive⟩ := exists_actual_additiveMellin_strip_rapid_bound K S mu nu
    P.additive zLower zUpper (by norm_num [zLower]) hzRange (2 * n + kr)
  obtain ⟨Cd, hCd, hd⟩ := ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest wLower wUpper (n + kn)
  obtain ⟨Ch, Zh, hCh, hZh, hh⟩ := exists_actual_moderate_fullCorrection_bound
    K Sset g he he1 zero_lt_one
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
  intro Z hZ a ha haB u hu s w z hs hs' hw hw' hz hz'
  have hwl : wLower ≤ w.re := by dsimp only [wLower]; linarith
  have hsl : sLower ≤ s.re := by dsimp only [sLower]; linarith
  have hZ1 : 1 ≤ Z := hZh.trans ((le_max_left _ _).trans hZ)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hN1 : 1 ≤ frequencyRowNorm K Sset u := one_le_idealNorm K u.ideal.val
  have hNpos : 0 < frequencyRowNorm K Sset u := zero_lt_one.trans_le hN1
  have hnormal : ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ ≤ Z := by
    simpa only [Real.rpow_one] using (hn Z ((le_max_right _ _).trans hZ)).2
  have hv := (moderate_swept_mem_actualModerateRowRegion haB he s w z hs hw hz).2.2
  have hc := hh Z ((le_max_left _ _).trans hZ) P psi ∅ u a ha (haB.trans hB1)
    s w z hv hs' hwl hz'
  have hnum' := hnum u hu w hwl hw'
  have hrec' := hrec u hu s hsl hs'
  have hadd : (1 + |z.im|) ^ (2 * n + kr) * ‖additiveMellin K Sset muS P.additive z‖ ≤ Ca := by
    simpa only [Complex.re_add_im] using hadditive z.re ⟨hz, hz'⟩ z.im
  have hden : (1 + |w.im|) ^ (n + kn) * ‖mellin P.denominator.toFun w‖ ≤ Cd := by
    simpa only [Complex.re_add_im] using hd w.re w.im hwl hw'
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
      Z ^ ((23 / 48) * wUpper) * Z ^ (19 / 6 : ℝ) * Z =
      Z ^ (moderateBoundaryScalePower) := by
    calc
      _ = Z ^ (17 / 96 : ℝ) * Z ^ (sUpper + zUpper) *
          Z ^ ((23 / 48) * wUpper) * Z ^ (19 / 6 : ℝ) * Z ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos,
          ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
        congr 1
        norm_num [moderateBoundaryScalePower, sUpper, wUpper, zUpper]
  have hNscale : frequencyRowNorm K Sset u ^ (-zLower) *
      frequencyRowNorm K Sset u ^ pnum * frequencyRowNorm K Sset u ^ prec *
      frequencyRowNorm K Sset u ^ eta = frequencyRowNorm K Sset u ^ (pnum + prec + eta - zLower) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  let A : ℝ := moderateBoundaryScalePower
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
          (Ch * frequencyRowNorm K Sset u ^ eta * Z ^ (19 / 6 : ℝ)) * (Cm * Z) := by gcongr
      _ = C0 *
          (Z ^ (17 / 96 : ℝ) * Z ^ (sUpper + zUpper) * Z ^ ((23 / 48) * wUpper) *
            Z ^ (19 / 6 : ℝ) * Z) *
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

    _ = _ := by norm_num [p, pnum, prec, eta, zLower]

end Expansion.Project

#print axioms Expansion.Project.exists_actual_moderate_sweep_kernel_rapid
