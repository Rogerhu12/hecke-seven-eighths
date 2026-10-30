import HeckeGeneral.Characters.ConductorFrequencyMembership
import HeckeGeneral.Characters.ConductorCanonicalTrace
import HeckeGeneral.Characters.StandardFiniteFactorization

/-! The actual positive trace phase as a frequency of the canonical conductor character.

Frequencies belong to the genuine inverse different times
the inverse conductor. Their residue coefficients have the negative sign required by the
standard finite character normalization. No unit condition or additive primitivity is imposed.
`Analysis.ConductorLatticeGauss` specializes actual polar-frequency Gauss sums.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The actual CRT residue coefficient of an inverse-conductor inverse-different frequency. -/
def conductorTraceFrequency (χ : HeckeCharacter K) (ξ : K)
    (hξ : ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    𝓞 K ⧸ (finiteConductor K χ).val :=
  (conductorResidueCRT K χ).symm (fun v : conductorPlaces K χ =>
    localCanonicalFrequencyResidue K v.val (localConductorExponent K χ v.val)
      (ξ : v.val.adicCompletion K) (conductorFrequency_valuation_bound K χ ξ hξ v.val))

/-- At every place outside the conductor, the exact different-level bound kills the phase. -/
theorem conductorTraceFrequency_local_trivial_outside (χ : HeckeCharacter K) (ξ : K)
    (hξ : ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (a : 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ conductorPlaces K χ) :
    psiLocal K v (-((ξ : v.adicCompletion K) * ((a : K) : v.adicCompletion K))) = 1 := by
  have hn : localConductorExponent K χ v = 0 := by
    simpa only [conductorPlaces, Finsupp.mem_support_iff,
      conductorExponents_apply, ne_eq, not_not] using hv
  have hbound : Valued.v (ξ : v.adicCompletion K) ≤
      WithZero.exp (localDifferentExponent K v) := by
    simpa only [hn, Int.natCast_zero, zero_add] using
      conductorFrequency_valuation_bound K χ ξ hξ v
  have ha : Valued.v ((a : K) : v.adicCompletion K) ≤ 1 := by
    exact (coe_algebraMap_mem (𝓞 K) K v a)
  apply (standardLocalAddCharacter_level K v).1
  rw [addCharLevel_psiLocal_eq_count_differentIdeal]
  change Valued.v (-((ξ : v.adicCompletion K) * ((a : K) : v.adicCompletion K))) ≤
    WithZero.exp (localDifferentExponent K v)
  rw [Valuation.map_neg, map_mul]
  calc
    _ ≤ Valued.v (ξ : v.adicCompletion K) * 1 :=
      mul_le_mul_of_nonneg_left ha zero_le
    _ = Valued.v (ξ : v.adicCompletion K) := mul_one _
    _ ≤ WithZero.exp (localDifferentExponent K v) := hbound

/-- The standard local character support of the negative principal frequency lies in the conductor. -/
theorem conductorTraceFrequency_mulSupport_subset (χ : HeckeCharacter K) (ξ : K)
    (hξ : ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (a : 𝓞 K) :
    Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      psiLocal K v ((algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
        (-((a : K) * ξ))) v)) ⊆ (conductorPlaces K χ : Set (HeightOneSpectrum (𝓞 K))) := by
  intro v hv
  rw [Function.mem_mulSupport] at hv
  by_contra hnot
  apply hv
  have he : ((algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
      (-((a : K) * ξ))) v) =
      -((ξ : v.adicCompletion K) * ((a : K) : v.adicCompletion K)) := by
    change algebraMap K (v.adicCompletion K) (-((a : K) * ξ)) = _
    rw [map_neg, map_mul, mul_comm]
    simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
  rw [he]
  exact conductorTraceFrequency_local_trivial_outside K χ ξ hξ a v hnot

/-- The exact positive trace phase is the canonical additive character at the actual CRT frequency. -/
theorem positiveTracePhase_eq_canonicalConductor_frequency (χ : HeckeCharacter K) (ξ : K)
    (hξ : ξ ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ *
      ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (a : 𝓞 K) :
    Complex.exp ((2 * Real.pi * Complex.I) * (Algebra.trace ℚ K ((a : K) * ξ) : ℂ)) =
      canonicalConductorAddCharacter K χ
        (conductorTraceFrequency K χ ξ hξ * Ideal.Quotient.mk _ a) := by
  calc
    _ = stdAddChar K ((0 : InfiniteAdeleRing K),
        algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (-((a : K) * ξ))) := by
      rw [stdAddChar_finitePrincipal, map_neg]
      simp
    _ = ∏ v ∈ conductorPlaces K χ,
        psiLocal K v ((algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
          (-((a : K) * ξ))) v) := by
      rw [stdAddChar_finite_eq_finprod_psiLocal,
        finprod_eq_prod_of_mulSupport_subset _ (conductorTraceFrequency_mulSupport_subset K χ ξ hξ a)]
    _ = ∏ v : conductorPlaces K χ,
        psiLocal K v.val (-((ξ : v.val.adicCompletion K) *
          ((a : K) : v.val.adicCompletion K))) := by
      rw [← Finset.prod_coe_sort (conductorPlaces K χ) (fun v =>
        psiLocal K v ((algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
          (-((a : K) * ξ))) v))]
      apply Finset.prod_congr rfl
      intro v _
      congr 1
      change algebraMap K (v.val.adicCompletion K) (-((a : K) * ξ)) = _
      rw [map_neg, map_mul, mul_comm]
      simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
    _ = canonicalConductorAddCharacter K χ
        (conductorTraceFrequency K χ ξ hξ * Ideal.Quotient.mk _ a) := by
      rw [canonicalConductorAddCharacter_CRT]
      simp only [map_mul, Pi.mul_apply, conductorTraceFrequency,
        RingEquiv.apply_symm_apply, conductorResidueCRT_mk]
      apply Finset.prod_congr rfl
      intro v _
      exact (localCanonicalAddCharacter_frequency_mk K v.val
        (localConductorExponent K χ v.val) (ξ : v.val.adicCompletion K)
        (conductorFrequency_valuation_bound K χ ξ hξ v.val)
        (algebraMap (𝓞 K) (LocalIntegerRing K v.val) a)).symm

end HeckeGeneral.Characters
