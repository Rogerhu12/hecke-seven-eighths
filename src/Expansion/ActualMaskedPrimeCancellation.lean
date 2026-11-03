import Expansion.ActualPrimeCancellation
import HeckeSkeleton.ExpansionModels.OriginalMaskBounds
import PrimeCancellationMaskCount

/-!
# Finite-height prime cancellation with the original complete-row mask

The deleted primes divide the fixed S/6 ideal times the complete row ideal.
The cost is consequently logarithmic in that actual ideal norm, including
unramified primes of the row.  The analytic estimate keeps the same finite
zero buffer and all three contour terms.  This supplies the literal masked
prime polynomial without an all-height zero-free input.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HeckeBufferedReciprocal
open PrimeCancellationPrimeSeries
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The exact prime mask used in the actual moment polynomials. -/
theorem completePrimeMask_eq_originalMask (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) :
    completeIdealCommonMask K S u p.asIdeal =
      HeckeSkeleton.PrimeCancellationIdealMask.originalMask S u.val p.asIdeal := by
  by_cases h : (∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ p.asIdeal →
      q ∉ S ∧ (6 : 𝓞 K) ∉ q.asIdeal) ∧ IsCoprime p.asIdeal u.val
  <;> simp [completeIdealCommonMask,
    HeckeSkeleton.PrimeCancellationIdealMask.originalMask, h]

theorem deleted_completePrimeMask_dvd_envelope (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : completeIdealCommonMask K S u p.asIdeal = false) :
    p.asIdeal ∣ originalDeletionEnvelope K S u := by
  rw [completePrimeMask_eq_originalMask] at hp
  apply originalDeletedPrimes_dvd_envelope K S u p
  exact (mem_originalDeletedPrimes K S u p).mpr
    (HeckeSkeleton.PrimeCancellationIdealMask.deleted_prime_cases S u.val p hp)

/-- No prime is discarded on account of its being unramified in χ. -/
def actualOriginalMaskedPrimeSum (χ : HeckeCharacter K) (u : NonzeroIdeal K)
    (W : ℝ → ℂ) (P : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∑ p ∈ pool, primeCoefficient K χ p * W (actualPrimeNorm K p / P) *
    (if completeIdealCommonMask K S u p.asIdeal then 1 else 0)

/-- A complete finite support represents the actual prime sum exactly. -/
theorem actual_finite_prime_sum_eq (χ : HeckeCharacter K) (W : ℝ → ℂ)
    (P : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K)))
    (hcover : ∀ p, W (actualPrimeNorm K p / P) ≠ 0 → p ∈ pool) :
    (∑ p ∈ pool, primeCoefficient K χ p * W (actualPrimeNorm K p / P)) =
      primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P := by
  symm
  unfold primeSum
  apply tsum_eq_sum
  intro p hp
  have hz : W (actualPrimeNorm K p / P) = 0 := by
    by_contra hn
    exact hp (hcover p hn)
  simp only [hz, mul_zero]

/-- The finite deletion error is proved from genuine ideal divisibility.
The bound is valid uniformly in the character, profile scale and prime pool. -/
theorem actualOriginalMaskedPrimeSum_le (χ : HeckeCharacter K) (u : NonzeroIdeal K)
    (W : ℝ → ℂ) (P M : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K)))
    (hM : 0 ≤ M) (hW : ∀ y, ‖W y‖ ≤ M)
    (hcover : ∀ p, W (actualPrimeNorm K p / P) ≠ 0 → p ∈ pool) :
    ‖actualOriginalMaskedPrimeSum K S χ u W P pool‖ ≤
      ‖primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ +
        (Real.log ((Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * idealNorm K u) /
          Real.log 2) * M := by
  have hD : 0 < Ideal.absNorm (originalDeletionEnvelope K S u) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (originalDeletionEnvelope_ne_zero K S u))
  have hf (p : HeightOneSpectrum (𝓞 K)) :
      ‖primeCoefficient K χ p * W (actualPrimeNorm K p / P)‖ ≤ M := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_primeCoefficient_le_one K χ p)
      (norm_nonneg _)).trans (by simpa only [one_mul] using hW (actualPrimeNorm K p / P))
  have h := PrimeCancellation.MaskCount.norm_maskedSum_le_log Ideal.absNorm pool
    (fun p => primeCoefficient K χ p * W (actualPrimeNorm K p / P))
    (fun p => completeIdealCommonMask K S u p.asIdeal)
    (originalDeletionEnvelope K S u) 2 M hD (by norm_num) hM
    (fun p _ _ => hf p) (fun p _ _ => actualPrimeNorm_ge_two K p)
    (fun p _ hp => deleted_completePrimeMask_dvd_envelope K S u p hp)
  rw [actual_finite_prime_sum_eq K χ W P pool hcover,
    originalDeletionEnvelope_norm] at h
  exact h

/-- Constants precede the row, character, scale and height.  The complete
original deletion is paid for explicitly and the zero hypothesis is finite. -/
theorem exists_actual_finite_height_masked_prime_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B M : ℝ,
      1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧ 0 < M ∧
      ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K)
        (U β δ H P Hupper : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K))),
        (∀ v : ℝ, χ ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v χ) = arch →
        heckeArchWeight K χ = weight → 1 ≤ U →
        heckeConductorScale K χ ≤ R * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ P → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K χ Hupper β →
        (∀ p, W (actualPrimeNorm K p / P) ≠ 0 → p ∈ pool) →
        ‖actualOriginalMaskedPrimeSum K S χ u W P pool‖ ≤
          actualPrimeCancellationEnvelope K C A CW order U β δ H P + B * Real.sqrt P +
          (Real.log ((Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * idealNorm K u) /
            Real.log 2) * M := by
  obtain ⟨C, A, P₀, CW, B, hC, hA, hP₀, hCW, hB, hb⟩ :=
    exists_actual_finite_height_prime_bound K hcomplex arch weight R hR W hW hs order
  obtain ⟨M, hM, hwin⟩ := exists_actualPrimeWindowBound W hW hs
  refine ⟨C, A, P₀, CW, B, M, hC, hA, hP₀, hCW, hB, hM, ?_⟩
  intro χ u U β δ H P Hupper pool hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hP hpadding hupper hcover
  exact (actualOriginalMaskedPrimeSum_le K S χ u W P M pool hM.le hwin.bound hcover).trans
    (add_le_add
      (hb χ U β δ H P Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP hpadding hupper)
      le_rfl)

end Expansion.Project

#print axioms Expansion.Project.completePrimeMask_eq_originalMask
#print axioms Expansion.Project.deleted_completePrimeMask_dvd_envelope
#print axioms Expansion.Project.actualOriginalMaskedPrimeSum_le
#print axioms Expansion.Project.exists_actual_finite_height_masked_prime_bound
