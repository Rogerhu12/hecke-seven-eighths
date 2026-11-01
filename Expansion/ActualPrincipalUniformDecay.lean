import Expansion.ActualPrincipalTruncatedShifts

/-!
# Uniform principal decay with the polynomial degrees fixed first

The original target reciprocal fixes one height degree.  The physical and
prime normalizers, Gaussian, and scale powers give a fixed coarse power of
Z.  Only the actual Mellin decay order is increased when a stronger tail
is requested.  In particular neither polynomial degree depends on that
request, on the scale, or on the outer integration variables.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeDeletedEulerControl
open scoped Classical Topology

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

private theorem principal_residue_scale_bounds
    {B e Z : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hZ : 1 ≤ Z)
    (s z : ℂ) (hs : s.re = B + e)
    (hz : 33 / 200 ≤ z.re) (hz1 : z.re ≤ 1 / 6 + e) :
    ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Real.exp 1 ∧
      ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ ≤ Z ∧
        ‖(Z : ℂ) ^ (s + z - 1)‖ ≤ Z := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hreal0 : 0 ≤ s.re + z.re - 1 := by rw [hs]; linarith
  have hreal1 : s.re + z.re - 1 ≤ 1 := by rw [hs]; linarith
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hsq := pow_le_pow_left₀ hreal0 hreal1 2
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero]
    nlinarith [sq_nonneg (s.im + z.im)]
  constructor
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    have hre : ((1 / 2 : ℂ) - z).re = (1 / 2 : ℝ) - z.re := by simp
    rw [hre, ← Real.rpow_mul hZpos.le]
    calc
      _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z := Real.rpow_one _
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos,
      Complex.sub_re, Complex.add_re, Complex.one_re]
    exact (Real.rpow_le_rpow_of_exponent_le hZ hreal1).trans_eq (Real.rpow_one _)

include nu in
/-- The actual factors fixed during the w and z moves.  Their common
height degree and scale threshold precede every later tail order. -/
theorem exists_actualPrincipal_fixedScalar_bounds
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega) (g : PrimeWindowGeometry)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ A Cw Cz Z0 : ℝ, 0 ≤ A ∧ 0 < Cw ∧ 0 < Cz ∧ 1 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ s : ℂ, s.re = B + e →
        (∀ z : ℂ, z.re = 1 / 6 + e →
          ‖actualPrincipalWFixedScalar K S mu P psi g Z s z‖ ≤
            Cw * Z ^ (3 : ℝ) * (1 + |s.im|) ^ A) ∧
        ‖actualPrincipalZFixedScalar K S mu P psi g Z s‖ ≤
          Cz * Z * (1 + |s.im|) ^ A := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Cr, k, hCr, hk, hr⟩ := exists_actual_target_common_line_reciprocal_bound
    K Sset hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨Zn, hZn, hn⟩ := exists_actual_primeNormalizer_inverse_bound
    K Sset hcomplex g 1 zero_lt_one
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_line_bound K S mu nu
    P.additive (sigma := 1 / 6 + e) (by linarith) (by linarith)
  obtain ⟨Cl, hCl, hl⟩ := exists_uniform_rightHalfPlane_bound
    K (1 + 6 * e) (by linarith)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let Cw : ℝ := Cp * Real.exp 1 * Ca * (F * Cl) * (Cr * (4 : ℝ) ^ k) * Cm
  let Cz : ℝ := Cp * ‖mellin P.denominator.toFun 1‖ * ‖deletedZetaResidue K Sset‖ *
    (Cr * (4 : ℝ) ^ k) * Cm
  have hCw : 0 ≤ Cw := by dsimp [Cw, Cp, Cm]; positivity
  have hCz : 0 ≤ Cz := by dsimp [Cz, Cp, Cm]; positivity
  refine ⟨k, Cw + 1, Cz + 1, Zn, hk, by linarith, by linarith, hZn, ?_⟩
  intro Z hZ s hs
  have hZ1 : 1 ≤ Z := hZn.trans hZ
  have hnormal : ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ ≤ Z := by
    simpa only [Real.rpow_one] using (hn Z hZ).2
  have hrec : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s)⁻¹‖ ≤
      (Cr * (4 : ℝ) ^ k) * (1 + |s.im|) ^ k := by
    apply (hr s hs).trans
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hCr.le
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hk
  constructor
  · intro z hz
    obtain ⟨hgauss, hxpow, hzpow⟩ := principal_residue_scale_bounds
      hB hB1 he he1 hZ1 s z hs (by linarith) hz.le
    have hadd := (ha z hz).2
    have hzet : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤ F * Cl := by
      have hzre : 1 + 6 * e ≤ (6 * z).re := by simp [hz]; linarith
      rw [heckeDeletedContinuation, norm_mul]
      exact mul_le_mul
        (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) 1 (6 * z) (by linarith))
        (hl 1 (6 * z) hzre) (norm_nonneg _) hF.le
    rw [actualPrincipalWFixedScalar,
      div_eq_mul_inv _
        (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z),
      div_eq_mul_inv _ (heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s)]
    simp only [mul_inv, norm_mul]
    calc
      _ ≤ Cp * Real.exp 1 * Ca * Z * Z *
          ((F * Cl) * ((Cr * 4 ^ k) * (1 + |s.im|) ^ k)) * (Cm * Z) := by
        change Cp * _ * _ * _ * _ * (_ * _) * (Cm * _) ≤ _
        gcongr
      _ = Cw * Z ^ (3 : ℝ) * (1 + |s.im|) ^ k := by
        norm_num only [Real.rpow_ofNat]
        dsimp only [Cw]
        ring
      _ ≤ _ := by gcongr; linarith
  · simp only [actualPrincipalZFixedScalar, div_eq_mul_inv, mul_inv, norm_mul]
    calc
      _ ≤ Cp * ‖mellin P.denominator.toFun 1‖ *
          (‖deletedZetaResidue K Sset‖ * ((Cr * 4 ^ k) * (1 + |s.im|) ^ k)) * (Cm * Z) := by
        change Cp * _ * (_ * _) * (Cm * _) ≤ _
        gcongr
      _ = Cz * Z * (1 + |s.im|) ^ k := by dsimp only [Cz]; ring
      _ ≤ _ := by gcongr; linarith

include nu in
/-- The complete principal w strip has any requested rapid decay, with
the same polynomial Z power and outer-height degree for all orders. -/
theorem exists_actualPrincipal_w_uniform_decay
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ A Z0 : ℝ, 0 ≤ A ∧ 1 ≤ Z0 ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ s w z : ℂ,
        s.re = B + e → z.re = 1 / 6 + e →
        19 / 20 ≤ w.re → w.re ≤ 1 + e → 1 ≤ |w.im| →
        ‖actualPrincipalKernelCore K S mu P psi g Z s w z
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)‖ ≤
          C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A * (1 + |w.im|) ^ (-(N : ℝ)) := by
  obtain ⟨A, Cw, Cz, Za, hA, hCw, hCz, hZa, hscalar⟩ :=
    exists_actualPrincipal_fixedScalar_bounds K S mu nu hcomplex P omega psi hpsi g
      hB hB1 he he1 hboundary
  obtain ⟨Ch, Zh, hCh, hZh, hcorr⟩ := exists_actual_principal_fullCorrection_bound K Sset g
  obtain ⟨Czeta, k, hCzeta, hk, hzet⟩ := exists_actual_deletedZeta_midStrip_height_bound K Sset hcomplex
  refine ⟨A, max Za Zh, hA, hZa.trans (le_max_left _ _), ?_⟩
  intro N
  obtain ⟨n, hn⟩ := exists_nat_ge (k + (N : ℝ))
  obtain ⟨Dm, hDm, hm⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest (19 / 20) (1 + e) n
  refine ⟨Cw * Ch * Dm * Czeta, by positivity, ?_⟩
  intro Z hZ s w z hs hz hw hw1 hwh
  have hZA : Za ≤ Z := (le_max_left _ _).trans hZ
  have hZH : Zh ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZa.trans hZA
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hAs := (hscalar Z hZA s hs).1 z hz
  have hM : (1 + |w.im|) ^ n * ‖mellin P.denominator.toFun w‖ ≤ Dm := by
    simpa only [Complex.re_add_im] using hm w.re w.im hw hw1
  have hL := hzet w (by linarith) (by linarith) hwh
  have hML := rapid_mul_polynomial_bound
    (by linarith [abs_nonneg w.im] : 1 ≤ 1 + |w.im|) hDm.le hCzeta.le hn hM hL
  have hY : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ ≤ Z := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _),
      Complex.sub_re, Complex.one_re, ← Real.rpow_mul hZpos.le]
    exact (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)).trans_eq (Real.rpow_one _)
  have hH0 := hcorr Z hZH P psi hunram ∅ (physicalPrincipalRow K Sset)
    (physicalPrincipalRow_support K Sset) s w z (by rw [hs]; linarith) hw
      (by rw [hz]; linarith) (by rw [hz]; linarith)
  have hH : ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s w z‖ ≤ Ch * Z := by
    apply hH0.trans
    apply mul_le_mul_of_nonneg_left _ hCh.le
    exact (Real.rpow_le_rpow_of_exponent_le hZ1 (by rw [hz]; linarith)).trans_eq (Real.rpow_one _)
  have hfront := mul_le_mul
    (mul_le_mul hAs hY (norm_nonneg _) (by positivity)) hH (norm_nonneg _) (by positivity)
  rw [actualPrincipalKernelCore_w_factorization K S mu P psi g Z s w z]
  simp only [norm_mul]
  calc
    _ = (‖actualPrincipalWFixedScalar K S mu P psi g Z s z‖ *
        ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s w z‖) *
        (‖mellin P.denominator.toFun w‖ *
          ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w‖) := by ring
    _ ≤ ((Cw * Z ^ (3 : ℝ) * (1 + |s.im|) ^ A) * Z * (Ch * Z)) *
        (Dm * Czeta * (1 + |w.im|) ^ (-(N : ℝ))) :=
      mul_le_mul hfront hML (by positivity) (by positivity)
    _ = _ := by norm_num only [Real.rpow_ofNat]; ring

include nu in
/-- The residue kernel on the z strip has the same fixed outer-height
degree.  Its tail order changes only the proved additive Mellin constant. -/
theorem exists_actualPrincipal_z_uniform_decay
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ A Z0 : ℝ, 0 ≤ A ∧ 1 ≤ Z0 ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ s z : ℂ,
        s.re = B + e → 33 / 200 ≤ z.re → z.re ≤ 1 / 6 + e → 1 ≤ |z.im| →
        ‖actualPrincipalWResidueKernel K S mu P psi g Z s z‖ ≤
          C * Z ^ (5 : ℝ) * (1 + |s.im|) ^ A * (1 + |z.im|) ^ (-(N : ℝ)) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨A, Cw, Cz, Za, hA, hCw, hCz, hZa, hscalar⟩ :=
    exists_actualPrincipal_fixedScalar_bounds K S mu nu hcomplex P omega psi hpsi g
      hB hB1 he he1 hboundary
  obtain ⟨Ch, Zh, hCh, hZh, hcorr⟩ := exists_actual_principal_fullCorrection_bound K Sset g
  obtain ⟨Czeta, k, hCzeta, hk, hzet⟩ := exists_actual_deletedZeta_midStrip_height_bound K Sset hcomplex
  refine ⟨A, max Za Zh, hA, hZa.trans (le_max_left _ _), ?_⟩
  intro N
  obtain ⟨n, hn⟩ := exists_nat_ge (k + (N : ℝ))
  obtain ⟨Dm, hDm, hm⟩ := exists_actual_additiveMellin_strip_rapid_bound K S mu nu
    P.additive (33 / 200) (1 / 6 + e) (by norm_num) (by linarith) n
  refine ⟨Cz * Real.exp 1 * Ch * Dm * (Czeta * (6 : ℝ) ^ k), by positivity, ?_⟩
  intro Z hZ s z hs hz hz1 hzh
  have hZA : Za ≤ Z := (le_max_left _ _).trans hZ
  have hZH : Zh ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZa.trans hZA
  have hAs := (hscalar Z hZA s hs).2
  obtain ⟨hG, hX, hZp⟩ := principal_residue_scale_bounds hB hB1 he he1 hZ1 s z hs hz hz1
  have hM : (1 + |z.im|) ^ n * ‖additiveMellin K Sset muS P.additive z‖ ≤ Dm := by
    simpa only [Complex.re_add_im] using hm z.re ⟨hz, hz1⟩ z.im
  have him : |(6 * z).im| = 6 * |z.im| := by simp [abs_mul]
  have hL0 := hzet (6 * z) (by simp; linarith) (by simp; linarith) (by rw [him]; linarith)
  have hL : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤
      (Czeta * (6 : ℝ) ^ k) * (1 + |z.im|) ^ k := by
    apply hL0.trans
    rw [him, mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg z.im]) hk) hCzeta.le
  have hML := rapid_mul_polynomial_bound
    (by linarith [abs_nonneg z.im] : 1 ≤ 1 + |z.im|)
    hDm.le (by positivity : 0 ≤ Czeta * (6 : ℝ) ^ k) hn hM hL
  have hH0 := hcorr Z hZH P psi hunram ∅ (physicalPrincipalRow K Sset)
    (physicalPrincipalRow_support K Sset) s 1 z (by rw [hs]; linarith) (by norm_num)
      hz (by linarith)
  have hH : ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖ ≤ Ch * Z := by
    apply hH0.trans
    apply mul_le_mul_of_nonneg_left _ hCh.le
    exact (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)).trans_eq (Real.rpow_one _)
  have hfront : ‖actualPrincipalZFixedScalar K S mu P psi g Z s‖ *
      ‖Complex.exp ((s + z - 1) ^ 2)‖ *
      ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ * ‖(Z : ℂ) ^ (s + z - 1)‖ *
      ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖ ≤
      (Cz * Z * (1 + |s.im|) ^ A) * Real.exp 1 * Z * Z * (Ch * Z) := by gcongr
  rw [actualPrincipalWResidueKernel_z_factorization K S mu P psi g Z s z]
  simp only [norm_mul]
  calc
    _ = (‖actualPrincipalZFixedScalar K S mu P psi g Z s‖ *
        ‖Complex.exp ((s + z - 1) ^ 2)‖ *
        ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ * ‖(Z : ℂ) ^ (s + z - 1)‖ *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖) *
        (‖additiveMellin K Sset muS P.additive z‖ *
          ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖) := by ring
    _ ≤ ((Cz * Z * (1 + |s.im|) ^ A) * Real.exp 1 * Z * Z * (Ch * Z)) *
        (Dm * (Czeta * (6 : ℝ) ^ k) * (1 + |z.im|) ^ (-(N : ℝ))) :=
      mul_le_mul hfront hML (by positivity) (by positivity)
    _ = (Cz * Real.exp 1 * Ch * Dm * (Czeta * (6 : ℝ) ^ k)) *
        Z ^ (4 : ℝ) * (1 + |s.im|) ^ A * (1 + |z.im|) ^ (-(N : ℝ)) := by
      norm_num only [Real.rpow_ofNat]
      ring
    _ ≤ _ := by
      have hZ45 : Z ^ (4 : ℝ) ≤ Z ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      gcongr

end Expansion.Project

#print axioms Expansion.Project.exists_actualPrincipal_fixedScalar_bounds
#print axioms Expansion.Project.exists_actualPrincipal_w_uniform_decay
#print axioms Expansion.Project.exists_actualPrincipal_z_uniform_decay
