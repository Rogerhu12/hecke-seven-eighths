import HeckeGeneral.Arithmetic.SIntegerModulusCRT
import HeckeGeneral.Arithmetic.ResidueTraceCharacters
import HeckeGeneral.Characters.LocalCanonicalFrequency

/-!
# Standard local additive pairings on an actual S-integer quotient

The prime places and exponents are those of the contraction of the actual
principal modulus. Their standard local characters, including the actual
different exponents, are transported through the actual CRT. Primitivity
is proved from the local primitive characters.

A frequency satisfying the inverse-modulus inverse-different valuation
bounds is reduced to an actual CRT frequency. Its phase formula applies
to every S-integer and does not require the frequency to be a unit. This
does not identify the resulting frequency with a proposed global `h/c`.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open NumberField.StandardAddChar
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- The actual quotient character, with standard local trace normalization. -/
def sIntegerModulusAddCharacter (c : S.integer K) (hc : c ≠ 0) :
    AddChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ :=
  transportCharacter (sIntegerModulusCRT K S c hc)
    (productCharacter fun v : sIntegerModulusPlaces K S c hc =>
      localCanonicalAddCharacter K v.val (sIntegerModulusPrimeExponents K S c hc v.val))

@[simp] theorem sIntegerModulusAddCharacter_apply (c : S.integer K) (hc : c ≠ 0)
    (a : S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) :
    sIntegerModulusAddCharacter K S c hc a =
      ∏ v : sIntegerModulusPlaces K S c hc,
        localCanonicalAddCharacter K v.val (sIntegerModulusPrimeExponents K S c hc v.val)
          (sIntegerModulusCRT K S c hc a v) := rfl

/-- Nondegeneracy is a conclusion of the actual local constructions. -/
theorem sIntegerModulusAddCharacter_isPrimitive (c : S.integer K) (hc : c ≠ 0) :
    (sIntegerModulusAddCharacter K S c hc).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (productCharacter_isPrimitive _ (fun v => localCanonicalAddCharacter_isPrimitive K v.val _))

theorem sIntegerModulusAddCharacter_norm (c : S.integer K) (hc : c ≠ 0)
    (a : S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) :
    ‖sIntegerModulusAddCharacter K S c hc a‖ = 1 := by
  rw [sIntegerModulusAddCharacter_apply, norm_prod]
  simp only [localCanonicalAddCharacter_norm, Finset.prod_const_one]

/-- Literal local phase formula, including for S-integers with denominators. -/
theorem sIntegerModulusAddCharacter_mk (c : S.integer K) (hc : c ≠ 0)
    (a : S.integer K) :
    sIntegerModulusAddCharacter K S c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a) =
      ∏ v : sIntegerModulusPlaces K S c hc,
        psiLocal K v.val
          (localUniformizer K v.val ^
            (-((sIntegerModulusPrimeExponents K S c hc v.val : ℤ) +
              localDifferentExponent K v.val)) *
            algebraMap K (v.val.adicCompletion K) a.val) := by
  rw [sIntegerModulusAddCharacter_apply]
  apply Finset.prod_congr rfl
  intro v _
  rw [sIntegerModulusCRT_mk]
  exact localCanonicalAddCharacter_mk K v.val _
    (sIntegerToLocalInteger K S v.val (sIntegerModulusPlaces_not_mem K S c hc v) a)

/-- The actual quotient frequency, without an assumption of invertibility. -/
def sIntegerModulusFrequency (c : S.integer K) (hc : c ≠ 0)
    (ξ : ∀ v : sIntegerModulusPlaces K S c hc, v.val.adicCompletion K)
    (hξ : ∀ v, Valued.v (ξ v) ≤ WithZero.exp
      ((sIntegerModulusPrimeExponents K S c hc v.val : ℤ) +
        localDifferentExponent K v.val)) :
    S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)) :=
  (sIntegerModulusCRT K S c hc).symm
    (fun v => localCanonicalFrequencyResidue K v.val
      (sIntegerModulusPrimeExponents K S c hc v.val) (ξ v) (hξ v))

@[simp] theorem sIntegerModulusCRT_frequency (c : S.integer K) (hc : c ≠ 0)
    (ξ : ∀ v : sIntegerModulusPlaces K S c hc, v.val.adicCompletion K)
    (hξ : ∀ v, Valued.v (ξ v) ≤ WithZero.exp
      ((sIntegerModulusPrimeExponents K S c hc v.val : ℤ) +
        localDifferentExponent K v.val)) (v : sIntegerModulusPlaces K S c hc) :
    sIntegerModulusCRT K S c hc (sIntegerModulusFrequency K S c hc ξ hξ) v =
      localCanonicalFrequencyResidue K v.val
        (sIntegerModulusPrimeExponents K S c hc v.val) (ξ v) (hξ v) := by
  simp only [sIntegerModulusFrequency, RingEquiv.apply_symm_apply]

/-- Exact finite standard-character phase for arbitrary completed frequencies
in the inverse-modulus inverse-different balls. The minus sign is retained. -/
theorem sIntegerModulusAddCharacter_frequency_mk (c : S.integer K) (hc : c ≠ 0)
    (ξ : ∀ v : sIntegerModulusPlaces K S c hc, v.val.adicCompletion K)
    (hξ : ∀ v, Valued.v (ξ v) ≤ WithZero.exp
      ((sIntegerModulusPrimeExponents K S c hc v.val : ℤ) +
        localDifferentExponent K v.val)) (a : S.integer K) :
    sIntegerModulusAddCharacter K S c hc
        (sIntegerModulusFrequency K S c hc ξ hξ *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a) =
      ∏ v : sIntegerModulusPlaces K S c hc,
        psiLocal K v.val (-(ξ v * algebraMap K (v.val.adicCompletion K) a.val)) := by
  rw [sIntegerModulusAddCharacter_apply]
  apply Finset.prod_congr rfl
  intro v _
  rw [map_mul, Pi.mul_apply, sIntegerModulusCRT_frequency, sIntegerModulusCRT_mk]
  exact localCanonicalAddCharacter_frequency_mk K v.val _ (ξ v) (hξ v)
    (sIntegerToLocalInteger K S v.val (sIntegerModulusPlaces_not_mem K S c hc v) a)

end HeckeGeneral.Characters
