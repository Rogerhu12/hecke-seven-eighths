import Expansion.ActualFrequencyPrimeCancellation
import Expansion.ActualMaskedPrimeCancellation

/-!
# Physical prime-profile phases and the centered analytic estimate

The imaginary profile twist is transferred exactly to the same prime
coefficient's norm twist; the residual scale phase has norm one. This avoids
selecting a new Mellin constant for each physical height. Original common
mask values are retained term by term.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.Analysis.ExpansionRecipe HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.HeckeBufferedReciprocal ExpansionInterfaces.Mellin
open PrimeCancellationPrimeSeries
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Literal imaginary profile twist, before taking norms or estimating. -/
theorem actualOriginalMaskedPrimeSum_profilePower (χ : HeckeCharacter K)
    (u : NonzeroIdeal K) (W : ℝ → ℂ) (P ν : ℝ) (hP : 0 < P)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    actualOriginalMaskedPrimeSum K S χ u
      (fun y => W y * profilePower (-vertical 0 ν) y) P pool =
      (P : ℂ) ^ vertical 0 ν *
        actualOriginalMaskedPrimeSum K S (χ * heckeNormTwist K (-ν)) u W P pool := by
  unfold actualOriginalMaskedPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hq : 0 < actualPrimeNorm K p := lt_of_lt_of_le (by norm_num) (actualPrimeNorm_ge_two K p)
  have he : ((-ν : ℝ) : ℂ) * Complex.I = -vertical 0 ν := by simp [vertical]
  have hc : primeCoefficient K (χ * heckeNormTwist K (-ν)) p =
      primeCoefficient K χ p * (actualPrimeNorm K p : ℂ) ^ (-vertical 0 ν) := by
    rw [primeCoefficient_normTwist, he]
    simp only [actualPrimeNorm, residueCard, Complex.ofReal_natCast]
  dsimp only
  rw [hc, profilePower_eq_cpow _ (div_pos hq hP), Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hq.le hP.le]
  simp only [div_eq_mul_inv]
  rw [← Complex.cpow_neg, neg_neg]
  ring

/-- The extracted scale factor has unit norm, uniformly in physical height. -/
theorem norm_actualOriginalMaskedPrimeSum_profilePower (χ : HeckeCharacter K)
    (u : NonzeroIdeal K) (W : ℝ → ℂ) (P ν : ℝ) (hP : 0 < P)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖actualOriginalMaskedPrimeSum K S χ u
      (fun y => W y * profilePower (-vertical 0 ν) y) P pool‖ =
      ‖actualOriginalMaskedPrimeSum K S (χ * heckeNormTwist K (-ν)) u W P pool‖ := by
  rw [actualOriginalMaskedPrimeSum_profilePower K S χ u W P ν hP pool,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP, vertical_re,
    Real.rpow_zero, one_mul]

/-- The fixed window determines every constant before the physical
frequency; its prime phase is controlled by the original finite zero buffer. -/
theorem exists_actual_finite_height_masked_frequency_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B M : ℝ,
      1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧ 0 < M ∧
      ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K)
        (U β δ ν H P Hupper : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K))),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → |ν| + H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        (∀ p, W (actualPrimeNorm K p / P) ≠ 0 → p ∈ pool) →
        ‖actualOriginalMaskedPrimeSum K S χ u
          (fun y => W y * profilePower (-vertical 0 ν) y) P pool‖ ≤
          actualPrimeFrequencyEnvelope K C A CW order U β δ ν H P + B * Real.sqrt P +
          (Real.log ((Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * idealNorm K u) /
            Real.log 2) * M := by
  obtain ⟨C, A, P₀, CW, B, hC, hA, hP₀, hCW, hB, hb⟩ :=
    exists_actual_finite_height_prime_frequency_bound K hcomplex arch weight R hR W hW hs order
  obtain ⟨M, hM, hwin⟩ := exists_actualPrimeWindowBound W hW hs
  refine ⟨C, A, P₀, CW, B, M, hC, hA, hP₀, hCW, hB, hM, ?_⟩
  intro χ u U β δ ν H P Hupper pool hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hP hpadding hupper hcover
  rw [norm_actualOriginalMaskedPrimeSum_profilePower K S χ u W P ν (by linarith) pool]
  exact (actualOriginalMaskedPrimeSum_le K S (χ * heckeNormTwist K (-ν))
    u W P M pool hM.le hwin.bound hcover).trans
      (add_le_add
        (hb χ U β δ ν H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP hpadding hupper)
        le_rfl)

end Expansion.Project

#print axioms Expansion.Project.actualOriginalMaskedPrimeSum_profilePower
#print axioms Expansion.Project.norm_actualOriginalMaskedPrimeSum_profilePower
#print axioms Expansion.Project.exists_actual_finite_height_masked_frequency_bound
