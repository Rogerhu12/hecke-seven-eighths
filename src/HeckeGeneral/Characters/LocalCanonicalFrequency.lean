import HeckeGeneral.Characters.LocalCanonicalAdditive
import Mathlib.Tactic.Ring

/-! Encode actual local frequencies for the standard trace-normalized residue character.

The valuation bound is an intermediate arithmetic input,
not a primitivity assumption. The construction and identity apply also at residue depth zero.

The global arithmetic bound is supplied by `ConductorFrequencyMembership`, and
`ConductorTraceFrequency` assembles the positive trace phase by CRT after eliminating
the factors outside the conductor.
The minus sign below matches the positive archimedean trace phase, since the standard finite
character on principal finite adèles has the negative trace sign.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The genuine local different exponent in the fixed standard additive normalization. -/
abbrev localDifferentExponent (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v
    (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)

/-- A frequency within the inverse-modulus inverse-different ball becomes a local integer. -/
def localCanonicalFrequencyInteger (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ξ : v.adicCompletion K)
    (hξ : Valued.v ξ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v)) :
    LocalIntegerRing K v :=
  ⟨-ξ * localUniformizer K v ^ ((n : ℤ) + localDifferentExponent K v), by
    rw [mem_adicCompletionIntegers]
    have hπ : Valued.v (localUniformizer K v ^ ((n : ℤ) + localDifferentExponent K v)) =
        WithZero.exp (-((n : ℤ) + localDifferentExponent K v)) := by
      rw [map_zpow₀, localUniformizer_valuation, ← WithZero.exp_zsmul]
      congr 1
      simp
    rw [map_mul, Valuation.map_neg, hπ]
    calc
      _ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v) *
          WithZero.exp (-((n : ℤ) + localDifferentExponent K v)) :=
        mul_le_mul_of_nonneg_right hξ zero_le
      _ = 1 := by rw [← WithZero.exp_add]; simp⟩

@[simp] theorem localCanonicalFrequencyInteger_coe (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (ξ : v.adicCompletion K)
    (hξ : Valued.v ξ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v)) :
    (localCanonicalFrequencyInteger K v n ξ hξ : v.adicCompletion K) =
      -ξ * localUniformizer K v ^ ((n : ℤ) + localDifferentExponent K v) := rfl

/-- The actual class in the completed prime-power residue ring, without any unit condition. -/
def localCanonicalFrequencyResidue (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (ξ : v.adicCompletion K)
    (hξ : Valued.v ξ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v)) :
    LocalResidueRing K v n :=
  Ideal.Quotient.mk _ (localCanonicalFrequencyInteger K v n ξ hξ)

/-- Exact local phase identification, valid whether the frequency residue is a unit or not. -/
theorem localCanonicalAddCharacter_frequency_mk (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (ξ : v.adicCompletion K)
    (hξ : Valued.v ξ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v))
    (a : LocalIntegerRing K v) :
    localCanonicalAddCharacter K v n
      (localCanonicalFrequencyResidue K v n ξ hξ * Ideal.Quotient.mk _ a) =
      psiLocal K v (-(ξ * (a : v.adicCompletion K))) := by
  rw [localCanonicalFrequencyResidue, ← map_mul, localCanonicalAddCharacter_mk]
  apply congrArg (psiLocal K v)
  change localUniformizer K v ^ (-((n : ℤ) + localDifferentExponent K v)) *
    ((-ξ * localUniformizer K v ^ ((n : ℤ) + localDifferentExponent K v)) *
      (a : v.adicCompletion K)) = _
  calc
    _ = (-ξ) * (localUniformizer K v ^ (-((n : ℤ) + localDifferentExponent K v)) *
        localUniformizer K v ^ ((n : ℤ) + localDifferentExponent K v)) * a := by ring
    _ = -(ξ * (a : v.adicCompletion K)) := by
      rw [← zpow_add₀ (localUniformizer_ne_zero K v)]
      simp

end HeckeGeneral.Characters
