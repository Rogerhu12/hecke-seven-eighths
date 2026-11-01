import Expansion.ActualLogDividedContour
import Expansion.ActualPrimeArithmetic

/-!
# Actual unweighted prime cancellation from a finite-height zero buffer

The exact divided-window identity removes the logarithmic weight. The
positive higher-prime-power tail is bounded using the actual ideal count,
leaving a square-root term. No all-height zero-free datum, prime cancellation
hypothesis, kernel/slot identification or amplitude inequality is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionInterfaces.Mellin
open PrimeCancellationPrimeSeries
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The three retained finite-contour terms, with constants before P and H. -/
def actualPrimeCancellationEnvelope (C A CW : ℝ) (order : ℕ)
    (U β δ H P : ℝ) : ℝ :=
  let M := actualPrimeLogRectangleBound K C A U δ 0 H
  (1 / (2 * Real.pi)) *
    ((M * P ^ (β + δ)) * CW +
      2 * (CW / (1 + H) ^ order) * M * P ^ (2 : ℝ) * (2 - (β + δ)) +
      (actualPrimeLogMass K 2 * P ^ (2 : ℝ)) * (CW / H ^ order))

theorem actualLogDividedPrimePowerSum_eq_prime_add_tail (χ : HeckeCharacter K)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (P : ℝ) (hP : 2 ≤ P) :
    actualLogDividedPrimePowerSum K χ W P =
      primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P +
        tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P := by
  simpa only [actualLogDividedPrimePowerSum, smoothedTerm, logDividedAnnularProfile,
    vertical, Complex.ofReal_zero, zero_mul, zero_add, neg_zero,
    Complex.cpow_zero, mul_one] using
    actual_logDivided_finite_sum_eq_primeSum_add_tailSum K χ W hW hs P hP

/-- A genuine prime sum is bounded by its finite contour terms and a uniform
square-root prime-power tail. All constants precede the character and scale. -/
theorem exists_actual_finite_height_prime_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧
      ∀ (χ : HeckeCharacter K) (U β δ H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ ≤
          actualPrimeCancellationEnvelope K C A CW order U β δ H P + B * Real.sqrt P := by
  obtain ⟨C, A, P₀, CW, hC, hA, hP₀, hCW, hbound⟩ :=
    exists_actual_logDivided_primePower_bound K hcomplex arch weight R hR W hW hs order
  obtain ⟨B, hB, htail⟩ := exists_actual_primePower_tail_bound K W hW hs
  refine ⟨C, A, P₀, CW, B, hC, hA, hP₀, hCW, hB, ?_⟩
  intro χ U β δ H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP
    hpadding hupper
  have hPtwo := hP₀.trans hP
  have heq := actualLogDividedPrimePowerSum_eq_prime_add_tail K χ W hW hs P hPtwo
  have hmain : ‖actualLogDividedPrimePowerSum K χ W P‖ ≤
      actualPrimeCancellationEnvelope K C A CW order U β δ H P :=
    hbound χ U β δ H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP hpadding hupper
  have hid : primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P =
      actualLogDividedPrimePowerSum K χ W P -
        tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P := by
    rw [heq, add_sub_cancel_right]
  calc
    _ = ‖actualLogDividedPrimePowerSum K χ W P -
        tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ := congrArg norm hid
    _ ≤ ‖actualLogDividedPrimePowerSum K χ W P‖ +
        ‖tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hmain (htail χ P (by linarith))

end Expansion.Project

#print axioms Expansion.Project.actualLogDividedPrimePowerSum_eq_prime_add_tail
#print axioms Expansion.Project.exists_actual_finite_height_prime_bound
