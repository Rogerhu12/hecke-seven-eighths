import Expansion.ActualPrimeContour
import ExpansionInterfaces.LogDividedAnnularProfile

/-!
# A scale-uniform finite contour estimate for the exact divided prime window

The original smooth window is fixed before P. Its logarithmic division uses
one Mellin constant for every sufficiently large P, including both horizontal
faces and the arbitrary-order initial-line tail. The remaining arithmetic
and zero-buffer assumptions are those of the actual Hecke character.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionInterfaces.Mellin
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The exact finite logarithmically divided prime-power sum, with no phase. -/
def actualLogDividedPrimePowerSum (χ : HeckeCharacter K) (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  ∑ np ∈ actualPrimeLogWindow K (2 * P), actualPrimeLogCoefficient K χ np *
    PrimeCancellationLogWindow.logWindow P W (actualPrimePowerNorm K np / P)

/-- All constants, including the divided-window Mellin constant, precede
P, the row character, the zero buffer and the contour height. -/
theorem exists_actual_logDivided_primePower_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧
      ∀ (χ : HeckeCharacter K) (U β δ H P Hupper : ℝ),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        let M := actualPrimeLogRectangleBound K C A U δ 0 H
        ‖actualLogDividedPrimePowerSum K χ W P‖ ≤ (1 / (2 * Real.pi)) *
          ((M * P ^ (β + δ)) * CW +
            2 * (CW / (1 + H) ^ order) * M * P ^ (2 : ℝ) * (2 - (β + δ)) +
            (actualPrimeLogMass K 2 * P ^ (2 : ℝ)) * (CW / H ^ order)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ :=
    exists_actual_primePower_bound_of_contour_data K hcomplex arch weight R hR
  obtain ⟨P₀, CW, hP₀, hCW, hprofile⟩ :=
    exists_uniform_logDivided_contour_data W hW hs (1 / 2) 2 order
  refine ⟨C, A, P₀, CW, hC, hA, hP₀, hCW, ?_⟩
  intro χ U β δ H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP
    hpadding hupper
  have hPtwo : 2 ≤ P := hP₀.trans hP
  have h := hbound χ (logDividedAnnularProfile W hW hs P hPtwo) order CW hCW
    (hprofile P hP) U β δ 0 H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH (by linarith) (by simpa only [abs_zero, zero_add] using hpadding) hupper
  simpa only [actualLogDividedPrimePowerSum, actualAnnularPrimePowerSum,
    logDividedAnnularProfile, smoothedTerm, vertical, Complex.ofReal_zero,
    zero_mul, add_zero, neg_zero, Complex.cpow_zero, mul_one] using h

end Expansion.Project

#print axioms Expansion.Project.exists_actual_logDivided_primePower_bound
