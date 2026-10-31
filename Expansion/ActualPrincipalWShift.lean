import Expansion.ActualPrincipalPoleLimits
import Expansion.ActualZetaHeightBounds
import DedekindZetaZeroFree.Analysis.ContourIntegration.SimplePoleShift

/-!
# The actual first principal residue shift

On the original principal rectangle, the finite correction is uniformly
bounded in all imaginary variables.  The actual annular denominator
Mellin transform has arbitrarily rapid decay throughout the w-strip.
It absorbs the proved polynomial growth of the deleted zeta numerator.
Consequently the literal principal kernel is integrable on both complete
w-lines, its horizontal edges vanish, and crossing w=1 contributes exactly
the previously identified actual w-residue kernel.
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
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

/-- The exact factors held fixed while moving only the w coordinate. -/
def actualPrincipalWFixedScalar (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s z : ℂ) : ℂ :=
  (physicalPoissonScalar K : ℂ) * Complex.exp ((s + z - 1) ^ 2) *
    additiveMellin K Sset muS P.additive z *
    ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) *
    (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z) /
      heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s) /
    (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z)

theorem actualPrincipalKernelCore_w_factorization
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s w z Wvalue : ℂ) :
    actualPrincipalKernelCore K S mu P psi g Z s w z Wvalue =
      actualPrincipalWFixedScalar K S mu P psi g Z s z * mellin P.denominator.toFun w *
        ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1) * Wvalue *
        compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s w z := by
  simp only [actualPrincipalKernelCore, actualPrincipalWFixedScalar, div_eq_mul_inv]
  ring

/-- Arbitrary w-height decay of the actual kernel on the complete residue
strip.  No Mellin, Euler, or kernel estimate is assumed. -/
theorem exists_actualPrincipal_w_strip_decay
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000)
    (loss : ℝ) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s z : ℂ,
      7 / 8 ≤ s.re → 33 / 200 ≤ z.re → z.re ≤ 1 →
      ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 19 / 20 ≤ w.re → w.re ≤ 1 + e → 1 ≤ |w.im| →
        ‖actualPrincipalKernelCore K S mu P psi g Z s w z
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)‖ ≤
            C * (1 + |w.im|) ^ (-loss) := by
  obtain ⟨Cz, k, hCz, hk, hzet⟩ := exists_actual_deletedZeta_midStrip_height_bound K Sset hcomplex
  obtain ⟨n, hn⟩ := exists_nat_ge (k + loss)
  obtain ⟨Dm, hDm, hm⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest (19 / 20) (1 + e) n
  obtain ⟨Ch, Z0, hCh, hZ0, hh⟩ := exists_actual_principal_fullCorrection_bound K Sset g
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ s z hs hz hz1
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let Y : ℝ := Z ^ (23 / 48 : ℝ)
  have hY1 : 1 ≤ Y := Real.one_le_rpow hZ1 (by norm_num)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  let A := actualPrincipalWFixedScalar K S mu P psi g Z s z
  let C0 : ℝ := ‖A‖ * Y ^ e * (Ch * Z ^ (z.re / 6)) * (Dm * Cz)
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro w hw hw1 hwh
  have hM : (1 + |w.im|) ^ n * ‖mellin P.denominator.toFun w‖ ≤ Dm := by
    simpa only [Complex.re_add_im] using hm w.re w.im hw hw1
  have hL := hzet w (by linarith) (by linarith) hwh
  have hML := rapid_mul_polynomial_bound
    (by positivity : 1 ≤ 1 + |w.im|) hDm.le hCz.le hn hM hL
  have hYPow : ‖(Y : ℂ) ^ (w - 1)‖ ≤ Y ^ e := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos, Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hH := hh Z hZ P psi hunram ∅ (physicalPrincipalRow K Sset)
    (physicalPrincipalRow_support K Sset) s w z hs hw hz hz1
  have hfront : ‖A‖ * ‖(Y : ℂ) ^ (w - 1)‖ *
      ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ (physicalPrincipalRow K Sset) Z s w z‖ ≤
      ‖A‖ * Y ^ e * (Ch * Z ^ (z.re / 6)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hYPow (norm_nonneg _)) hH
      (norm_nonneg _) (by positivity)
  rw [actualPrincipalKernelCore_w_factorization K S mu P psi g Z s w z]
  simp only [norm_mul]
  calc
    _ = (‖A‖ * ‖(Y : ℂ) ^ (w - 1)‖ *
        ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ (physicalPrincipalRow K Sset) Z s w z‖) *
        (‖mellin P.denominator.toFun w‖ *
          ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w‖) := by
      dsimp only [A, Y]
      ring
    _ ≤ (‖A‖ * Y ^ e * (Ch * Z ^ (z.re / 6))) *
        (Dm * Cz * (1 + |w.im|) ^ (-loss)) := by
      exact mul_le_mul hfront hML (by positivity) (by positivity)
    _ = C0 * (1 + |w.im|) ^ (-loss) := by dsimp only [C0]; ring
    _ ≤ (C0 + 1) * (1 + |w.im|) ^ (-loss) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (by positivity) _)

/-- The exact first principal contour move, with the actual residue.
Both complete vertical integrals and the vanishing horizontal edges are
proved from the actual rapid decay above. -/
theorem actualPrincipal_w_fullLine_shift
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {e : ℝ} (he : 0 < e) (he1 : e < 1 / 1000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → ∀ s z : ℂ,
      7 / 8 ≤ s.re → 33 / 200 ≤ z.re → z.re ≤ 1 →
      comparisonVerticalIntegral (1 + e)
        (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
          (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) -
        comparisonVerticalIntegral (19 / 20)
          (fun w => actualPrincipalKernelCore K S mu P psi g Z s w z
            (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w)) =
          actualPrincipalWResidueKernel K S mu P psi g Z s z := by
  obtain ⟨Z0, hZ0, hdecay⟩ := exists_actualPrincipal_w_strip_decay K S mu hcomplex P psi
    hunram g he he1 2
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ s z hs hz hz1
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  obtain ⟨C, _, hb⟩ := hdecay Z hZ s z hs hz hz1
  apply verticalIntegral_sub_eq_residue_of_decay
    (p := (1 : ℂ)) (by norm_num) (by simpa using he)
    (C := C) (T0 := 1)
  · intro w hw
    exact (differentiableAt_actualPrincipal_w_kernel K S mu P psi g Z hZpos s z w hw.2
      (principal_rectangle_mem_rowEulerRegion s w z hs hw.1.1 hz)).differentiableWithinAt
  · exact actualPrincipal_w_residue K S mu P psi g Z hZpos s z
      (principal_rectangle_mem_rowEulerRegion s 1 z hs (by norm_num) hz)
  · intro x hx y hy
    simpa using hb ((x : ℂ) + (y : ℂ) * Complex.I)
      (by simpa using hx.1) (by simpa using hx.2) (by simpa using hy)

end Expansion.Project

#print axioms Expansion.Project.exists_actualPrincipal_w_strip_decay
#print axioms Expansion.Project.actualPrincipal_w_fullLine_shift
