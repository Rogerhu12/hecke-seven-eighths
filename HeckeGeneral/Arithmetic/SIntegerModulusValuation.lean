import HeckeGeneral.Arithmetic.SIntegerModulusNorm
import HeckeGeneral.Arithmetic.SIntegerModulusCRT

/-! The actual exterior valuation of an S-integer modulus and its completed
frequency bound, with exponents from its genuine contracted ideal. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem sIntegerModulus_valuation
    (c : S.integer K) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    v.valuation K (c : K) =
      WithZero.exp (-(sIntegerModulusPrimeExponents K S c hc v : ℤ)) := by
  obtain ⟨d, hd, u, hfield, hspan⟩ :=
    exists_integer_sUnit_modulus_representative K S c hc
  let I := nonzeroIntegralPrincipalIdeal K d hd
  have hmap : I.val.map (algebraMap (𝓞 K) (S.integer K)) =
      Ideal.span ({c} : Set (S.integer K)) := by
    change (Ideal.span ({d} : Set (𝓞 K))).map (algebraMap (𝓞 K) (S.integer K)) = _
    rw [Ideal.map_span, Set.image_singleton]
    exact hspan
  have hcontraction : sIntegerModulusContraction K S c =
      (outsideSIdeal K S I).val := by
    unfold sIntegerModulusContraction
    rw [← hmap]
    exact under_map_ideal_eq_outsideSIdeal K S I
  have hexponent : sIntegerModulusPrimeExponents K S c hc v = primeExponents I v := by
    let J : (Ideal (𝓞 K))⁰ :=
      ⟨sIntegerModulusContraction K S c,
        mem_nonZeroDivisors_of_ne_zero (sIntegerModulusContraction_ne_bot K S c hc)⟩
    have hJ : J = outsideSIdeal K S I := Subtype.ext hcontraction
    change primeExponents J v = _
    rw [hJ, outsideSIdeal, primeExponents_idealOfPrimeExponents,
      outsideSPrimeExponents, Finsupp.filter_apply_pos (fun v => v ∉ S) _ hv]
  have hval : v.valuation K (d : K) = v.valuation K (c : K) := by
    rw [hfield, map_mul, Set.unit_valuation_eq_one S K u hv, one_mul]
  rw [← hval, hexponent]
  change v.valuation K (algebraMap (𝓞 K) K d) =
    WithZero.exp (-((normalizedFactors (Ideal.span ({d} : Set (𝓞 K)))).count v.asIdeal : ℤ))
  rw [valuation_of_algebraMap, v.intValuation_if_neg hd,
    Ideal.count_associates_factors_eq
      (I := Ideal.span ({d} : Set (𝓞 K)))
      (nonZeroDivisors.coe_ne_zero I) v.isPrime v.ne_bot]

/-- The completed valuation has exactly the same normalization. -/
theorem sIntegerModulus_completion_valuation
    (c : S.integer K) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    Valued.v (algebraMap K (v.adicCompletion K) (c : K)) =
      WithZero.exp (-(sIntegerModulusPrimeExponents K S c hc v : ℤ)) := by
  change Valued.v ((c : K) : v.adicCompletion K) = _
  rw [valuedAdicCompletion_eq_valuation']
  exact sIntegerModulus_valuation K S c hc v hv

/-- Every actual h/c frequency lies in the inverse-modulus local ball. -/
theorem sInteger_div_modulus_valuation_le
    (c : S.integer K) (hc : c ≠ 0) (h : S.integer K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    v.valuation K ((h : K) / (c : K)) ≤
      WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ) := by
  rw [div_eq_mul_inv, map_mul, map_inv₀, sIntegerModulus_valuation K S c hc v hv,
    ← WithZero.exp_neg, neg_neg]
  calc
    _ ≤ 1 * WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ) :=
      mul_le_mul_of_nonneg_right (h.property v hv) zero_le
    _ = _ := one_mul _

theorem sInteger_div_modulus_completion_valuation_le
    (c : S.integer K) (hc : c ≠ 0) (h : S.integer K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    Valued.v (algebraMap K (v.adicCompletion K) ((h : K) / (c : K))) ≤
      WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ) := by
  rw [map_div₀]
  change Valued.v (((h : K) / (c : K)) : v.adicCompletion K) ≤ _
  rw [map_div₀, valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation']
  simpa only [map_div₀] using sInteger_div_modulus_valuation_le K S c hc h v hv

end HeckeGeneral.Arithmetic
