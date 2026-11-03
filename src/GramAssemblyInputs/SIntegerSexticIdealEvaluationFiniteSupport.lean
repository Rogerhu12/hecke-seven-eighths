import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation

/-! SOURCE ONLY, UNRUN. Enlarge the actual ideal-prime product to an
arbitrary finite exterior support. Extra primes have multiplicity zero;
no numerator nonvanishing is required, and the unit ideal is included. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem sIntegerSexticIdealEvaluation_eq_prod_finite_support
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hTS : ∀ p ∈ T, p ∉ S)
    (hT6 : ∀ p ∈ T, (6 : 𝓞 K) ∉ p.asIdeal)
    (hT : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∈ T)
    (a : S.integer K) :
    (∏ p : T, sIntegerSexticEvaluation K S p.val (hTS p.val p.property)
      ζ hζ σ (hT6 p.val p.property) a ^ idealPrimeMultiplicity K p.val I) =
        sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := by
  letI : Fintype (idealPrimeDivisors K I) := (idealPrimeDivisors_finite K I hI).fintype
  let f : T → ℂ := fun p => sIntegerSexticEvaluation K S p.val (hTS p.val p.property)
    ζ hζ σ (hT6 p.val p.property) a ^ idealPrimeMultiplicity K p.val I
  let U : Finset T := Finset.univ.filter (fun p => p.val.asIdeal ∣ I)
  have hreduce : (∏ p ∈ U, f p) = ∏ p : T, f p := by
    apply Finset.prod_subset (Finset.subset_univ U)
    intro p _hp hpU
    have hnot : ¬ p.val.asIdeal ∣ I := by
      intro hdiv
      exact hpU (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hdiv⟩)
    dsimp only [f]
    rw [idealPrimeMultiplicity_eq_zero_of_not_dvd K p.val I hI hnot, pow_zero]
  have hreindex : sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a =
      ∏ p ∈ U, f p := by
    unfold sIntegerSexticIdealEvaluation
    refine Finset.prod_bij
      (fun p _ => (⟨p.val, hT p.val p.property⟩ : T)) ?_ ?_ ?_ ?_
    · intro p _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩
    · intro p _ q _ hpq
      exact Subtype.ext (congrArg (fun z : T => z.val) hpq)
    · intro p hp
      have hpI : p.val.asIdeal ∣ I := (Finset.mem_filter.mp hp).2
      refine ⟨⟨p.val, hpI⟩, Finset.mem_univ _, ?_⟩
      exact Subtype.ext rfl
    · intro p _
      rfl
  exact hreduce.symm.trans hreindex.symm

end HeckeGeneral.Characters
