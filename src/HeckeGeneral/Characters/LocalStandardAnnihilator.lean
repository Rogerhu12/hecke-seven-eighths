import HeckeGeneral.Characters.LocalCanonicalFrequency
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! The genuine standard local annihilator and the finite support of the different. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The annihilator of the local integers for the standard trace character is
the inverse-different ball, with the actual different exponent. -/
theorem standardLocalAnnihilator_iff (v : HeightOneSpectrum (𝓞 K))
    (w : v.adicCompletion K) :
    (∀ z : v.adicCompletion K, z ∈ v.adicCompletionIntegers K →
      psiLocal K v (z * w) = 1) ↔
      Valued.v w ≤ WithZero.exp (localDifferentExponent K v) := by
  have hlevel : addCharLevel (psiLocal K v) = localDifferentExponent K v :=
    addCharLevel_psiLocal_eq_count_differentIdeal K v
  constructor
  · intro h
    by_contra hw
    have hwv : (Valued.v w : WithZero (Multiplicative ℤ)) ≠ 0 := by
      intro hz
      exact hw (hz ▸ zero_le)
    have hw0 : w ≠ 0 := by
      intro hz
      exact hwv (by rw [hz, map_zero])
    have hlog : localDifferentExponent K v < WithZero.log (Valued.v w) :=
      (WithZero.lt_log_iff_exp_lt hwv).mpr (lt_of_not_ge hw)
    have hstep : WithZero.exp (localDifferentExponent K v + 1) ≤ Valued.v w := by
      rw [← WithZero.exp_log hwv]
      exact WithZero.exp_le_exp.mpr (by omega)
    obtain ⟨y, hy, hyne⟩ := (standardLocalAddCharacter_level K v).2
    rw [hlevel] at hy
    have hz : y * w⁻¹ ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ (hy.trans hstep) zero_le
    have he := h (y * w⁻¹) hz
    rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at he
    exact hyne he
  · intro hw z hz
    apply (standardLocalAddCharacter_level K v).1
    rw [hlevel, map_mul]
    rw [mem_adicCompletionIntegers] at hz
    calc
      Valued.v z * Valued.v w ≤ 1 * WithZero.exp (localDifferentExponent K v) :=
        mul_le_mul hz hw zero_le zero_le
      _ = _ := one_mul _

/-- Every prescribed finite set can be enlarged to contain the support of the
actual different, without a nonvanishing assumption on the ideal. -/
theorem exists_finiteS_localDifferentExponent_eq_zero
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0 := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | localDifferentExponent K v ≠ 0}.Finite := by
    simpa only [Filter.eventually_cofinite, localDifferentExponent] using
      (FractionalIdeal.finite_factors
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))
  refine ⟨S₀ ∪ hf.toFinset, Finset.subset_union_left, ?_⟩
  intro v hv
  by_contra hne
  exact hv (Finset.mem_union.mpr (Or.inr (hf.mem_toFinset.mpr hne)))

end HeckeGeneral.Characters
