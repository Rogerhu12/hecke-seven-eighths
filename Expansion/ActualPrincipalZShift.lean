import Expansion.ActualPrincipalWShift
import Expansion.ActualMellinStripDecay
import Expansion.ActualPrincipalResidueIdentification

/-!
# The actual second principal residue shift

The real z-strip from 33/200 to 1/6+e stays in the original positive Mellin
and Euler regions.  Uniform rapid decay of the actual additive Mellin
transform absorbs the proved polynomial growth of zeta(6z).  This proves
the complete vertical contour identity and the actual double residue,
including the original factor-six Jacobian and physical normalization.
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

def actualPrincipalZFixedScalar (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s : ℂ) : ℂ :=
  (physicalPoissonScalar K : ℂ) * mellin P.denominator.toFun 1 *
    (deletedZetaResidue K Sset / heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s) /
    (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z)

theorem actualPrincipalWResidueKernel_z_factorization
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s z : ℂ) :
    actualPrincipalWResidueKernel K S mu P psi g Z s z =
      actualPrincipalZFixedScalar K S mu P psi g Z s * Complex.exp ((s + z - 1) ^ 2) *
        additiveMellin K Sset muS P.additive z *
        ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) *
        heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z) *
        compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s 1 z := by
  rw [actualPrincipalWResidueKernel_factorization]
  simp only [actualPrincipalZRegularPart, actualPrincipalZFixedScalar, div_eq_mul_inv]
  ring

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu

theorem exists_actualPrincipal_z_strip_decay
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000)
    (loss : ℝ) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s : ℂ,
      7 / 8 ≤ s.re → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        33 / 200 ≤ z.re → z.re ≤ 1 / 6 + e → 1 ≤ |z.im| →
        ‖actualPrincipalWResidueKernel K S mu P psi g Z s z‖ ≤
          C * (1 + |z.im|) ^ (-loss) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Cz, k, hCz, hk, hzet⟩ := exists_actual_deletedZeta_midStrip_height_bound K Sset hcomplex
  obtain ⟨n, hn⟩ := exists_nat_ge (k + loss)
  obtain ⟨Dm, hDm, hm⟩ := exists_actual_additiveMellin_strip_rapid_bound K S mu nu
    P.additive (33 / 200) (1 / 6 + e) (by norm_num) (by linarith) n
  obtain ⟨Ch, Z0, hCh, hZ0, hh⟩ := exists_actual_principal_fullCorrection_bound K Sset g
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ s hs
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let upper : ℝ := 1 / 6 + e
  let X : ℝ := Z ^ (17 / 48 : ℝ)
  have hX1 : 1 ≤ X := Real.one_le_rpow hZ1 (by norm_num)
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  let A := actualPrincipalZFixedScalar K S mu P psi g Z s
  let G : ℝ := Real.exp ((s.re + upper - 1) ^ 2)
  let C0 : ℝ := ‖A‖ * G * X ^ (1 / 2 - (33 / 200 : ℝ)) *
    Z ^ (s.re + upper - 1) * (Ch * Z ^ (upper / 6)) * (Dm * (Cz * (6 : ℝ) ^ k))
  have hC0 : 0 ≤ C0 := by dsimp only [C0, G]; positivity
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro z hz hz1 hzh
  have hM : (1 + |z.im|) ^ n * ‖additiveMellin K Sset muS P.additive z‖ ≤ Dm := by
    simpa only [Complex.re_add_im] using hm z.re ⟨hz, hz1⟩ z.im
  have him : |(6 * z).im| = 6 * |z.im| := by simp [abs_mul]
  have hL0 := hzet (6 * z) (by simp; linarith) (by simp; linarith) (by rw [him]; linarith)
  have hL : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤
      (Cz * (6 : ℝ) ^ k) * (1 + |z.im|) ^ k := by
    apply hL0.trans
    rw [him, mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hCz.le
    apply Real.rpow_le_rpow (by positivity) _ hk
    nlinarith [abs_nonneg z.im]
  have hML := rapid_mul_polynomial_bound
    (by have := abs_nonneg z.im; linarith : 1 ≤ 1 + |z.im|)
    hDm.le (by positivity : 0 ≤ Cz * (6 : ℝ) ^ k) hn hM hL
  have hG : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ G := by
    have hreal0 : 0 ≤ s.re + z.re - 1 := by linarith
    have hreal1 : s.re + z.re - 1 ≤ s.re + upper - 1 := by dsimp [upper]; linarith
    have hsquare := pow_le_pow_left₀ hreal0 hreal1 2
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero]
    dsimp only [G]
    nlinarith [sq_nonneg (s.im + z.im)]
  have hXPow : ‖(X : ℂ) ^ (1 / 2 - z)‖ ≤ X ^ (1 / 2 - (33 / 200 : ℝ)) := by
    have hre : ((1 / 2 : ℂ) - z).re = (1 / 2 : ℝ) - z.re := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hre]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hZPow : ‖(Z : ℂ) ^ (s + z - 1)‖ ≤ Z ^ (s.re + upper - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos, Complex.sub_re, Complex.add_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by dsimp [upper]; linarith)
  have hH0 := hh Z hZ P psi hunram ∅ (physicalPrincipalRow K Sset)
    (physicalPrincipalRow_support K Sset) s 1 z hs (by norm_num) hz (by linarith)
  have hH : ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖ ≤ Ch * Z ^ (upper / 6) :=
    hH0.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by dsimp [upper]; linarith)) hCh.le)
  have hfront : ‖A‖ * ‖Complex.exp ((s + z - 1) ^ 2)‖ *
      ‖(X : ℂ) ^ (1 / 2 - z)‖ * ‖(Z : ℂ) ^ (s + z - 1)‖ *
      ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖ ≤
      ‖A‖ * G * X ^ (1 / 2 - (33 / 200 : ℝ)) *
        Z ^ (s.re + upper - 1) * (Ch * Z ^ (upper / 6)) := by
    gcongr
  rw [actualPrincipalWResidueKernel_z_factorization K S mu P psi g Z s z]
  simp only [norm_mul]
  calc
    _ = (‖A‖ * ‖Complex.exp ((s + z - 1) ^ 2)‖ *
        ‖(X : ℂ) ^ (1 / 2 - z)‖ * ‖(Z : ℂ) ^ (s + z - 1)‖ *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s 1 z‖) *
        (‖additiveMellin K Sset muS P.additive z‖ *
          ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖) := by
      dsimp only [A, X]
      ring
    _ ≤ (‖A‖ * G * X ^ (1 / 2 - (33 / 200 : ℝ)) *
        Z ^ (s.re + upper - 1) * (Ch * Z ^ (upper / 6))) *
        (Dm * (Cz * (6 : ℝ) ^ k) * (1 + |z.im|) ^ (-loss)) :=
      mul_le_mul hfront hML (by positivity) (by dsimp [G]; positivity)
    _ = C0 * (1 + |z.im|) ^ (-loss) := by dsimp only [C0]; ring
    _ ≤ (C0 + 1) * (1 + |z.im|) ^ (-loss) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (by positivity) _)

theorem actualPrincipal_z_fullLine_shift
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s : ℂ, 7 / 8 ≤ s.re →
      comparisonVerticalIntegral (1 / 6 + e) (actualPrincipalWResidueKernel K S mu P psi g Z s) -
        comparisonVerticalIntegral (33 / 200) (actualPrincipalWResidueKernel K S mu P psi g Z s) =
          actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) *
            (deletedZetaResidue K Sset / 6) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Z0, hZ0, hdecay⟩ := exists_actualPrincipal_z_strip_decay K S mu nu hcomplex
    P psi hunram g he he1 2
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ s hs
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  obtain ⟨C, _, hb⟩ := hdecay Z hZ s hs
  apply verticalIntegral_sub_eq_residue_of_decay
    (p := (1 / 6 : ℂ)) (by norm_num) (by simpa using he)
    (C := C) (T0 := 1)
  · intro z hz
    exact (differentiableAt_actualPrincipal_z_kernel K S mu nu P psi g Z hZpos s z
      (by have := hz.1.1; linarith) hz.2
      (principal_rectangle_mem_rowEulerRegion s 1 z hs (by norm_num) hz.1.1)).differentiableWithinAt
  · exact actualPrincipal_z_residue K S mu nu P psi g Z hZpos s
      (principal_rectangle_mem_rowEulerRegion s 1 (1 / 6) hs (by norm_num) (by norm_num))
  · intro x hx y hy
    simpa using hb ((x : ℂ) + (y : ℂ) * Complex.I)
      (by simpa using hx.1) (by simpa using hx.2) (by simpa using hy)

/-- The complete z contour difference is the literal normalized double
residue integrand, with the already corrected physical normalization. -/
theorem actualPrincipal_z_fullLine_shift_normalized
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s : ℂ, 7 / 8 < s.re →
      comparisonVerticalIntegral (1 / 6 + e) (actualPrincipalWResidueKernel K S mu P psi g Z s) -
        comparisonVerticalIntegral (33 / 200) (actualPrincipalWResidueKernel K S mu P psi g Z s) =
          actualPrincipalWeightedTerm K Sset psi Z s
            (actualNormalizedPrincipalCorrection K Sset P psi g Z s) := by
  obtain ⟨Z0, hZ0, hh⟩ := actualPrincipal_z_fullLine_shift K S mu nu hcomplex P psi hunram g he he1
  refine ⟨Z0, hZ0, fun Z hZ s hs => ?_⟩
  exact (hh Z hZ s hs.le).trans (actualPrincipal_double_residue_eq K S mu P psi hAllowed hN
    g Z (zero_lt_one.trans_le (hZ0.trans hZ)) s hs)

end Expansion.Project

#print axioms Expansion.Project.exists_actualPrincipal_z_strip_decay
#print axioms Expansion.Project.actualPrincipal_z_fullLine_shift
#print axioms Expansion.Project.actualPrincipal_z_fullLine_shift_normalized
