import HeckeGeneral.Analysis.HeckeSeries

/-!
# Coefficient bridge for the Mathlib-only Hecke challenge

The challenge and solution declare their own identical coefficient definitions.
This module does not import either declaration.  Its lemmas compare the underlying
expressions with the library's actual local components and ideal coefficients.
The last lemma extends the convergent series over nonzero ideals to all ideals,
with the zero ideal contributing zero.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Mathlib's local integral-unit formulation is the library's unramified condition. -/
theorem unramifiedAt_iff_integral_units_ofAdicCompletion
    (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ u ∈ (v.adicCompletionIntegers K).units,
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) = 1) ↔
      UnramifiedAt K χ v := by
  exact (unramifiedAt_iff_integral_units K χ v).symm

/-- Choosing any element with valuation `exp (-1)` gives the same prime coefficient.
The proposition `U` permits using a definitionally different unramified predicate. -/
theorem primeValue_eq_primeCoefficient (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (U : Prop) (hU : U ↔ UnramifiedAt K χ v) :
    (if h : U ∧ ∃ ϖ : (v.adicCompletion K)ˣ,
        Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) then
      (χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v (Classical.choose h.2)) : ℂ)
    else 0) = primeCoefficient K χ v := by
  by_cases h : U ∧ ∃ ϖ : (v.adicCompletion K)ˣ,
      Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)
  · rw [dite_eq_left h]
    exact (primeCoefficient_eq_of_norm K χ v (hU.mp h.1) (Classical.choose h.2)
      (localNorm_eq_inv_residueCard_of_valuation K v _ (Classical.choose_spec h.2))).symm
  · have hχ : ¬UnramifiedAt K χ v := by
      intro hχ
      apply h
      refine ⟨hU.mpr hχ, localUniformizerUnit K v, ?_⟩
      exact localUniformizer_valuation K v
    rw [dite_eq_right h, primeCoefficient_of_ramified K χ v hχ]

/-- The challenge's factorization expression agrees with the multiplicative
ideal coefficient. Only prime ideals occur in `normalizedFactors`, so the
different unused branches of the two prime-value extensions do not matter. -/
theorem normalizedFactors_coefficient_eq (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (I : Ideal (𝓞 K)) :
    (if I = ⊥ then 0 else
      ((normalizedFactors I).map fun P =>
        if h : P.IsPrime ∧ P ≠ ⊥ then a ⟨P, h.1, h.2⟩ else 0).prod) =
      idealCoefficient a I := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCoefficient]
  · rw [ite_eq_right hI, idealCoefficient, ite_eq_right hI]
    congr 1
    apply Multiset.map_congr rfl
    intro P hP
    have hp : Prime P := prime_of_normalized_factor P hP
    have hPP : P.IsPrime ∧ P ≠ ⊥ := ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    rw [dite_eq_left hPP, primeIdealValue, dite_eq_left hp]
    exact congrArg a (HeightOneSpectrum.ext rfl)

/-- The coefficient bridge on the nonzero ideal index type used by the library. -/
theorem normalizedFactors_coefficient_eq_heckeIdealCoefficient
    (χ : HeckeCharacter K) (I : NonzeroIdeal K) :
    (if I.val = ⊥ then 0 else
      ((normalizedFactors I.val).map fun P =>
        if h : P.IsPrime ∧ P ≠ ⊥ then primeCoefficient K χ ⟨P, h.1, h.2⟩ else 0).prod) =
      heckeIdealCoefficient K χ I :=
  normalizedFactors_coefficient_eq K (primeCoefficient K χ) I.val

/-- The genuine Hecke series also sums over all ideals when zero is assigned
coefficient zero, exactly as in the challenge statement. -/
theorem hasSum_heckeIdealCoefficient_all (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) =>
      idealCoefficient (primeCoefficient K χ) I * (Ideal.absNorm I : ℂ) ^ (-s))
      (heckeLSeries K χ s) := by
  let f : Ideal (𝓞 K) → ℂ := fun I =>
    idealCoefficient (primeCoefficient K χ) I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hsupport : Function.support f ⊆ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    apply hI
    subst I
    simp only [f, Ideal.zero_eq_bot, idealCoefficient_zero, zero_mul]
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  apply (hasSum_heckeLSeries K χ hs).congr_fun
  intro I
  change idealCoefficient (primeCoefficient K χ) I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) =
    heckeIdealCoefficient K χ I * (idealNorm K I : ℂ) ^ (-s)
  simp only [idealNorm, heckeIdealCoefficient, nonzeroIdealCoefficient, Complex.ofReal_natCast]

end HeckeGeneral.Bridge
