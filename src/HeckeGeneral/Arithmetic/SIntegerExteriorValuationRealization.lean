import HeckeGeneral.Arithmetic.SIntegerModulusValuation
import HeckeGeneral.Arithmetic.SIntegerPrincipalization
import Lean.Elab.Tactic.Omega

/- The PID hypothesis is supplied by exists_finite_sInteger_isPrincipalIdealRing.
   No CFT modules, localized fractional ideal maps, or extra arithmetic hypotheses. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [IsPrincipalIdealRing (S.integer K)]

private theorem exists_sInteger_exterior_nat_valuation
    (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    ∃ c : S.integer K, c ≠ 0 ∧ ∀ v, v ∉ S →
      v.valuation K (c : K) = WithZero.exp (-(e v : ℤ)) := by
  let I := idealOfPrimeExponents e
  let J := I.val.map (algebraMap (𝓞 K) (S.integer K))
  have hinj : Function.Injective (algebraMap (𝓞 K) (S.integer K)) := by
    intro a b hab
    apply IsFractionRing.injective (𝓞 K) K
    exact congrArg (fun z : S.integer K => (z : K)) hab
  have hJ : J ≠ ⊥ := by
    exact (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr
      (nonZeroDivisors.coe_ne_zero I)
  let c := Submodule.IsPrincipal.generator J
  have hc : c ≠ 0 := by
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J).not.mp hJ
  have hspan : Ideal.span ({c} : Set (S.integer K)) = J :=
    Ideal.span_singleton_generator J
  have hcontraction : sIntegerModulusContraction K S c =
      (outsideSIdeal K S I).val := by
    unfold sIntegerModulusContraction
    rw [hspan]
    exact under_map_ideal_eq_outsideSIdeal K S I
  have hexponents : sIntegerModulusPrimeExponents K S c hc =
      e.filter (fun v => v ∉ S) := by
    unfold sIntegerModulusPrimeExponents
    have hsub : (⟨sIntegerModulusContraction K S c,
        mem_nonZeroDivisors_of_ne_zero
          (sIntegerModulusContraction_ne_bot K S c hc)⟩ : (Ideal (𝓞 K))⁰) =
        outsideSIdeal K S I := Subtype.ext hcontraction
    rw [hsub]
    simp only [outsideSIdeal, primeExponents_idealOfPrimeExponents,
      outsideSPrimeExponents, I, primeExponents_idealOfPrimeExponents]
  refine ⟨c, hc, fun v hv => ?_⟩
  rw [sIntegerModulus_valuation K S c hc v hv, hexponents,
    Finsupp.filter_apply_pos (fun v => v ∉ S) e hv]

theorem exists_exterior_valuation_realization
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ x : Kˣ, ∀ v, v ∉ S →
      v.valuation K (x : K) = WithZero.exp (-e v) := by
  let ep := e.mapRange Int.toNat (by decide)
  let en := e.mapRange (fun n : ℤ => (-n).toNat) (by decide)
  obtain ⟨p, hp, hpv⟩ := exists_sInteger_exterior_nat_valuation K S ep
  obtain ⟨n, hn, hnv⟩ := exists_sInteger_exterior_nat_valuation K S en
  have hpK : (p : K) ≠ 0 := fun h => hp (Subtype.ext h)
  have hnK : (n : K) ≠ 0 := fun h => hn (Subtype.ext h)
  refine ⟨Units.mk0 ((p : K) / (n : K)) (div_ne_zero hpK hnK), fun v hv => ?_⟩
  change v.valuation K ((p : K) / (n : K)) = _
  rw [map_div₀, hpv v hv, hnv v hv, ← WithZero.exp_sub]
  congr 1
  change -(Int.toNat (e v) : ℤ) - -(Int.toNat (-e v) : ℤ) = -(e v)
  omega

end HeckeGeneral.Arithmetic
