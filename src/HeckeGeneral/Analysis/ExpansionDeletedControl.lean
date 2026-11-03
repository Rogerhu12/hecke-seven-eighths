import ExpansionDetector.EulerDeletionSpectrum
import HeckeGeneral.Analysis.ExpansionDetectorInitial
import HeckeGeneral.Analysis.HeckeConjugateZeros
import HeckeSkeleton.HeckeUniformBufferedControl
import HeckeSkeleton.HeckeConductorNorm

/-!
# Actual deleted Hecke control in the buffered zero-free rectangle

The deletion set is an arbitrary finite set of height-one primes dividing
the complete nonzero row ideal. In particular the statement does not remove
ramified primes from the row. Both the Euler deletion cost and the buffered
ordinary/reciprocal bound are consequences of existing theorems.

All constants occur before the character, row ideal, deletion set, heights,
abscissa, and evaluation point. No polynomial upper estimate is an input.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionDeletedControl

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Bridge ExpansionDetector.EulerDeletion
open HeckeSkeleton.HeckeUniformBufferedControl HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]

/-- Actual finite Euler deletion, uniformly over all primes dividing a row. -/
theorem exists_deleted_euler_subpower {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ (E : Finset (HeightOneSpectrum (𝓞 K))), (∀ p ∈ E, p.asIdeal ∣ I) →
      ∀ (χ : HeckeCharacter K) (s : ℂ), δ ≤ s.re →
        ‖heckeEulerDeletionPolynomial K χ E s‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε ∧
        ‖(heckeEulerDeletionPolynomial K χ E s)⁻¹‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := spectrum_euler_positive_subpower (K := K) δ ε hδ hε
  refine ⟨C, hC, ?_⟩
  intro I hI E hE χ s hs
  simpa only [heckeEulerDeletionPolynomial, finiteEulerPolynomial, eulerPolynomial,
    residueCard, Complex.ofReal_natCast] using
    hb I hI E hE (primeCoefficient K χ) (fun p _ => norm_primeCoefficient_le_one K χ p) s hs

/-- Negative-line deletion has the explicit additional exponent η. -/
theorem exists_deleted_euler_negative_subpower {η ε : ℝ}
    (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ 0 →
      ∀ (E : Finset (HeightOneSpectrum (𝓞 K))), (∀ p ∈ E, p.asIdeal ∣ I) →
      ∀ (χ : HeckeCharacter K) (s : ℂ), -η ≤ s.re →
        ‖heckeEulerDeletionPolynomial K χ E s‖ ≤
          C * (Ideal.absNorm I : ℝ) ^ (η + ε) := by
  obtain ⟨C, hC, hb⟩ := spectrum_euler_negative_subpower (K := K) η ε hη hε
  refine ⟨C, hC, ?_⟩
  intro I hI E hE χ s hs
  simpa only [heckeEulerDeletionPolynomial, finiteEulerPolynomial, eulerPolynomial,
    residueCard, Complex.ofReal_natCast] using
    hb I hI E hE (primeCoefficient K χ) (fun p _ => norm_primeCoefficient_le_one K χ p) s hs

def bufferedCost (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
    (C ε Hupper : ℝ) : ℝ :=
  C * (Ideal.absNorm I : ℝ) ^ ε * heckeConductorScale K χ ^ ε *
    (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε)

/-- A single constant controls the actual deleted continuation and its
inverse. Only the genuine zero upper bound is supplied by the selected row. -/
theorem exists_actual_deleted_buffered_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
      (E : Finset (HeightOneSpectrum (𝓞 K))) (a H Hupper : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ s : ℂ, a + 6 * e ≤ s.re → s.re ≤ 2 → |s.im| ≤ H →
        ‖heckeDeletedContinuation K χ E s‖ + ‖(heckeDeletedContinuation K χ E s)⁻¹‖ ≤
          bufferedCost K χ I C ε Hupper := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_fixedType_buffered_control K hcomplex τ m he he' hε
  obtain ⟨F, hF, hEuler⟩ := exists_deleted_euler_subpower K (δ := 1 / 2) (by norm_num) hε
  refine ⟨F * D, mul_pos hF hD, ?_⟩
  intro χ I E a H Hupper hχ hτ hm hI hE ha ha' hH hpadding hupper s hs hs' hheight
  have hL := hbound χ a H Hupper hχ hτ hm ha ha' hH hpadding hupper s hs hs' hheight
  have hP := hEuler I hI E hE χ s (by linarith)
  have hFnonneg : 0 ≤ F * (Ideal.absNorm I : ℝ) ^ ε := by positivity
  unfold heckeDeletedContinuation
  rw [norm_mul, mul_inv, norm_mul]
  calc
    _ ≤ (F * (Ideal.absNorm I : ℝ) ^ ε) *
        (‖heckeContinuation K χ s‖ + ‖(heckeContinuation K χ s)⁻¹‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hP.1 (norm_nonneg (heckeContinuation K χ s)),
        mul_le_mul_of_nonneg_right hP.2 (norm_nonneg (heckeContinuation K χ s)⁻¹)]
    _ ≤ (F * (Ideal.absNorm I : ℝ) ^ ε) *
        (D * heckeConductorScale K χ ^ ε *
          (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε)) :=
      mul_le_mul_of_nonneg_left hL hFnonneg
    _ = bufferedCost K χ I (F * D) ε Hupper := by unfold bufferedCost; ring

theorem deleted_ne_zero_of_upper (χ : HeckeCharacter K)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (E : Finset (HeightOneSpectrum (𝓞 K))) {a e Hupper : ℝ}
    (ha : 1 / 2 ≤ a) (he : 0 < e)
    (hupper : ZeroUpperBound K χ Hupper (a + 2 * e))
    (s : ℂ) (hs : a + 6 * e ≤ s.re) (hh : |s.im| ≤ Hupper) :
    heckeDeletedContinuation K χ E s ≠ 0 := by
  apply mul_ne_zero
  · exact heckeEulerDeletionPolynomial_ne_zero K χ E (by linarith)
  · exact continuation_ne_zero_of_upper K χ hχ Hupper (a + 2 * e)
      (by linarith) hupper s (by linarith) hh

/-- The selected upper-zero bound is invariant under the actual dual.
The proof uses the existing conjugation theorem for meromorphic orders. -/
theorem zeroUpperBound_inv (χ : HeckeCharacter K) {H a : ℝ}
    (h : ZeroUpperBound K χ H a) : ZeroUpperBound K χ⁻¹ H a := by
  intro ρ hρ hleft hright hheight
  have horder := meromorphicOrderAt_heckeContinuation_inv K χ (conj ρ)
  simp only [Complex.conj_conj] at horder
  have hb := h (conj ρ) (by rwa [← horder]) (by simpa using hleft)
    (by simpa using hright) (by simpa only [Complex.conj_im, abs_neg] using hheight)
  simpa only [Complex.conj_re] using hb

theorem fixedType_inv
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : (fun v => heckeRadialParameter K v χ) = τ) (hm : heckeArchWeight K χ = m) :
    (fun v => heckeRadialParameter K v χ⁻¹) = -τ ∧ heckeArchWeight K χ⁻¹ = -m := by
  constructor
  · funext v
    simp only [heckeRadialParameter_inv, ← hτ, Pi.neg_apply]
  · funext v
    simp only [heckeArchWeight_of_complex K χ⁻¹ v (hcomplex v),
      heckeComplexWeight_inv, ← hm, Pi.neg_apply,
      heckeArchWeight_of_complex K χ v (hcomplex v)]

end HeckeGeneral.Analysis.ExpansionDeletedControl
