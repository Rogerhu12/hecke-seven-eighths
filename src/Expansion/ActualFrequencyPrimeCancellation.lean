import Expansion.ActualPrimeCancellation

/-!
# Prime cancellation uniform in the physical frequency

The center frequency is retained in the finite rectangle. Its phase is
removed from the logarithmic weight by the actual arithmetic norm twist,
whose prime-power tail has the same uniform bound.  Thus the profile
constant is chosen before ν; no derivatives of a ν-dependent window are
used, and no all-height zero control is inferred.
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

/-- Three genuine finite-contour terms with the physical center retained. -/
def actualPrimeFrequencyEnvelope (C A CW : ℝ) (order : ℕ)
    (U β δ ν H P : ℝ) : ℝ :=
  let M := actualPrimeLogRectangleBound K C A U δ ν H
  (1 / (2 * Real.pi)) *
    ((M * P ^ (β + δ)) * CW +
      2 * (CW / (1 + H) ^ order) * M * P ^ (2 : ℝ) * (2 - (β + δ)) +
      (actualPrimeLogMass K 2 * P ^ (2 : ℝ)) * (CW / H ^ order))

/-- The norm-twisted arithmetic sum equals the original character's
frequency-centered finite Mellin polynomial, term for term. -/
theorem actualLogDividedPrimePowerSum_normTwist (χ : HeckeCharacter K)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (P ν : ℝ) (hP : 2 ≤ P) :
    actualLogDividedPrimePowerSum K (χ * heckeNormTwist K (-ν)) W P =
      actualAnnularPrimePowerSum K χ (logDividedAnnularProfile W hW hs P hP) P ν := by
  unfold actualLogDividedPrimePowerSum actualAnnularPrimePowerSum
  apply Finset.sum_congr rfl
  intro np _
  rw [actualPrimeLogCoefficient_normTwist]
  rfl

/-- A single divided-window Mellin constant works for every frequency and
every sufficiently large scale. The zero buffer concerns χ itself. -/
theorem exists_actual_logDivided_primePower_frequency_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧
      ∀ (χ : HeckeCharacter K) (U β δ ν H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖actualLogDividedPrimePowerSum K (χ * heckeNormTwist K (-ν)) W P‖ ≤
          actualPrimeFrequencyEnvelope K C A CW order U β δ ν H P := by
  obtain ⟨C, A, hC, hA, hb⟩ :=
    exists_actual_primePower_bound_of_contour_data K hcomplex arch weight R hR
  obtain ⟨P₀, CW, hP₀, hCW, hprofile⟩ :=
    exists_uniform_logDivided_contour_data W hW hs (1 / 2) 2 order
  refine ⟨C, A, P₀, CW, hC, hA, hP₀, hCW, ?_⟩
  intro χ U β δ ν H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hP hpadding hupper
  rw [actualLogDividedPrimePowerSum_normTwist K χ W hW hs P ν (hP₀.trans hP)]
  exact hb χ (logDividedAnnularProfile W hW hs P (hP₀.trans hP)) order CW hCW
    (hprofile P hP) U β δ ν H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH (by linarith) hpadding hupper

/-- Unweighted primes with arbitrary physical frequency, using the actual
finite zero buffer and a frequency-independent square-root tail constant. -/
theorem exists_actual_finite_height_prime_frequency_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧
      ∀ (χ : HeckeCharacter K) (U β δ ν H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        ‖primeSum (actualPrimeNorm K)
          (primeCoefficient K (χ * heckeNormTwist K (-ν))) W P‖ ≤
          actualPrimeFrequencyEnvelope K C A CW order U β δ ν H P + B * Real.sqrt P := by
  obtain ⟨C, A, P₀, CW, hC, hA, hP₀, hCW, hb⟩ :=
    exists_actual_logDivided_primePower_frequency_bound K hcomplex arch weight R hR
      W hW hs order
  obtain ⟨B, hB, htail⟩ := exists_actual_primePower_tail_bound K W hW hs
  refine ⟨C, A, P₀, CW, B, hC, hA, hP₀, hCW, hB, ?_⟩
  intro χ U β δ ν H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hP hpadding hupper
  let χν := χ * heckeNormTwist K (-ν)
  have heq := actualLogDividedPrimePowerSum_eq_prime_add_tail K χν W hW hs P (hP₀.trans hP)
  have hid : primeSum (actualPrimeNorm K) (primeCoefficient K χν) W P =
      actualLogDividedPrimePowerSum K χν W P -
        tailSum (actualPrimeNorm K) (primeCoefficient K χν) W P := by
    rw [heq, add_sub_cancel_right]
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add
    (hb χ U β δ ν H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP hpadding hupper)
    (htail χν P (by linarith)))

end Expansion.Project

#print axioms Expansion.Project.actualLogDividedPrimePowerSum_normTwist
#print axioms Expansion.Project.exists_actual_logDivided_primePower_frequency_bound
#print axioms Expansion.Project.exists_actual_finite_height_prime_frequency_bound
