import HeckePort.Moments.ReflectionDeletion

/-!
# Reflection of a character through its natural primitive

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/NaturalReflection.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, together with `polynomial_natural_deletion` of
`NaturalPrimitive.lean`.

openai's three theorems are stated for `HeckeFamily.Character`.  They combine
(i) the existence of the natural primitive `ψ` of `χ` (`exists_natural_primitive`, built on
`IdealCharacter.exists_primitive_associate`), (ii) the Gauss-sum reflection of a primitive
character with deleted primes (`primitive_deleted_reflection`, built on the `ℤ[ω]` radial Poisson
formula and the finite unit group of order six), and (iii) the formal step that transports (ii)
to `χ` through `idealCoeff χ = idealCoeff (ψ.excludePrimes S)`.  Only (iii) is domain-free and is
ported, with (i) and (ii) as hypotheses:

* `natural_coeff_excl`: `a = excl S b` on nonzero ideals, for `S = redundantSet M C`
  (openai `idealCoeff_natural_deletion`, combined with `deleted_coefficient`);
* `polynomial_natural_deletion` and `polynomial_coeff_congr`;
* `original_natural_reflection`: the reflection identity of `χ` with the sum over
  `S.powerset` and `SmoothIdeal S`, from the primitive pair's reflection identity `hreflect`
  and the coefficient relation `hcoeff`.

Not ported: `exists_natural_primitive`, `primitive_character_deleted`, `inverse_deletion_coeff`
(these use `exists_primitive_character`, `TraceCharacter.normalizedGauss` and
`idealCoeff_inverse_conj`), and `original_inverse_reflection`, which is
`original_natural_reflection` with `reflectedTerm` unfolded.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

lemma polynomial_coeff_congr {a b : Ideal (𝓞 K) → ℂ} (h : ∀ I, a I = b I) (W : ℝ → ℂ) (X : ℝ) :
    plainPoly a W X = plainPoly b W X := by
  unfold plainPoly
  congr 1
  apply tsum_congr
  intro I
  rw [h]

/-- openai `idealCoeff_natural_deletion` in the form `a = excl S b` on nonzero ideals. -/
theorem natural_coeff_excl (M C : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hC : C ≠ ⊥) (hCM : C ∣ M)
    (a b : Ideal (𝓞 K) → ℂ)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (hsrc : ∀ I, b I = if IsCoprime I C then b I else 0) (I : NI K) :
    a I.val = excl (redundantSet M C) b I.val := by
  rw [idealCoeff_natural_deletion M C hM hC hCM a b hmask hsrc I.val, excl]
  exact if_congr (outside_iff_coprime (redundantSet M C) (redundantSet_prime M C) I).symm rfl rfl

/-- openai `polynomial_natural_deletion`. -/
theorem polynomial_natural_deletion {a : Ideal (𝓞 K) → ℂ} (b : Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K)))
    (hcoeff : ∀ I : NI K, a I.val = excl S b I.val) (W : ℝ → ℂ) (X : ℝ) :
    plainPoly a W X = plainPoly (excl S b) W X := by
  unfold plainPoly
  congr 1
  apply tsum_congr
  intro I
  rw [hcoeff I]

/-- openai `original_natural_reflection`, formal part: the reflection identity of the
primitive pair `(b, bi)` (`hreflect`) transfers to `a`, which equals `b` with the primes `S`
deleted (`hcoeff`). -/
theorem original_natural_reflection {a b bi : Ideal (𝓞 K) → ℂ} (hb : IdealCoeff b)
    (hbi : IdealCoeff bi) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (hcoeff : ∀ I : NI K, a I.val = excl S b I.val)
    (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hreflect : ∀ Y : ℝ, 0 < Y → plainPoly b W Y = G * plainPoly bi F (Q / Y))
    (X : ℝ) (hX : 0 < X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm b bi S F X Q D)) ∧
    plainPoly a W X =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm b bi S F X Q D H := by
  obtain ⟨hsum, hid⟩ := deletion_reflection hbi S hb hS W F hW hF G Q hQ hreflect X hX
  exact ⟨hsum, (polynomial_natural_deletion b S hcoeff W X).trans hid⟩

end HeckePort.Moments

end
