import HeckeGeneral.Characters.LocalCanonicalFrequency
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! Arithmetic membership bounds for actual conductor frequencies.

All inputs below are actual fractional-ideal membership;
no local valuation bound, additive primitivity, or principal ideal hypothesis is assumed.
The principal-fraction calculation is adapted from the FLT Project's
`valuation_eq_exp_neg_count_spanSingleton`, preserved locally in
`vendor/flt/FLTReuse/Mbbd20d45a2a367d5.lean` (Apache 2.0).
Only that short calculation is reused; this file has no new FLT module dependency.

`StandardFiniteFactorization` supplies the finite-character product formula, and
`ConductorTraceFrequency` eliminates outside factors and proves the CRT phase identity.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The discrete valuation of a nonzero field element equals the negative principal-ideal count. -/
theorem valuation_eq_exp_neg_principal_count (v : HeightOneSpectrum (𝓞 K))
    (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-(FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x))) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hx hab.symm
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hprincipal : (spanSingleton (𝓞 K)⁰ x : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    spanSingleton_ne_zero_iff.mpr hx
  have hrepresentation : (spanSingleton (𝓞 K)⁰ x : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) b)⁻¹ *
        (Ideal.span {a} : Ideal (𝓞 K)) := by
    rw [coeIdeal_span_singleton, ← hab, div_eq_inv_mul, ← spanSingleton_mul_spanSingleton]
  rw [FractionalIdeal.count_well_defined K v hprincipal hrepresentation]
  have hmk : IsLocalization.mk' K a (⟨b, hb⟩ : (𝓞 K)⁰) = x := by
    rw [IsFractionRing.mk'_eq_div]
    exact hab
  rw [← hmk, HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg ha,
    v.intValuation_if_neg hb0, ← WithZero.exp_sub, WithZero.exp_inj, neg_sub, neg_sub_neg]

/-- Fractional-ideal membership gives the valuation bound, including membership of zero. -/
theorem valuation_le_exp_neg_count_of_mem (v : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) (x : K) (hx : x ∈ I) :
    v.valuation K x ≤ WithZero.exp (-(FractionalIdeal.count K v I)) := by
  by_cases hx0 : x = 0
  · subst x
    rw [map_zero]
    exact zero_le
  · rw [valuation_eq_exp_neg_principal_count K v x hx0]
    apply WithZero.exp_le_exp.mpr
    exact neg_le_neg (FractionalIdeal.count_mono K v
      (spanSingleton_ne_zero_iff.mpr hx0) (spanSingleton_le_iff_mem.mpr hx))

/-- The fractional-ideal count of the actual finite conductor is its constructed local depth. -/
theorem count_finiteConductor (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K) =
      (localConductorExponent K χ v : ℤ) := by
  have hc : (finiteConductor K χ).val ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (finiteConductor K χ)
  rw [FractionalIdeal.count_coe K v hc,
    Ideal.count_associates_factors_eq hc v.isPrime v.ne_bot,
    ← Arithmetic.primeExponents_apply, primeExponents_finiteConductor,
    conductorExponents_apply]

/-- Every actual inverse-conductor inverse-different frequency satisfies the local encoding bound. -/
theorem conductorFrequency_valuation_bound (χ : HeckeCharacter K) (ξ : K)
    (hξ : ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (ξ : v.adicCompletion K) ≤
      WithZero.exp ((localConductorExponent K χ v : ℤ) + localDifferentExponent K v) := by
  have hd : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have hc : ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero (finiteConductor K χ))
  have hbound := valuation_le_exp_neg_count_of_mem K v _ ξ hξ
  rw [FractionalIdeal.count_mul K v (inv_ne_zero hd) (inv_ne_zero hc),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_finiteConductor] at hbound
  rw [adicCompletion.valued_coe]
  simpa only [localDifferentExponent, neg_add, neg_neg, add_comm] using hbound

end HeckeGeneral.Characters
