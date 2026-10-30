import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation
import HeckeGeneral.Characters.SexticPowerResidueComparison

/-! Composite ideal comparison on integral numerators
coprime to every prime dividing the denominator. No reciprocity is used. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

/-- The actual finite product agrees with the image of the upstream ideal
symbol. The auxiliary primitive-root and norm proofs can be any proofs;
proof irrelevance identifies them with those in the prime comparison. -/
theorem sIntegerSexticIdealEvaluation_algebraMap_eq_idealPowerResidueSymbol
    (hmu : (primitiveRoots ((6 : ℕ+) : ℕ) K).Nonempty)
    (hcoprime : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
      (Ideal.absNorm p.asIdeal).Coprime ((6 : ℕ+) : ℕ))
    (a : 𝓞 K)
    (ha : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → a ∉ p.asIdeal) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
        (algebraMap (𝓞 K) (S.integer K) a) =
      σ (algebraMap (𝓞 K) K
        ((idealPowerResidueSymbol K I hI (6 : ℕ+) hmu a hcoprime ha).val : 𝓞 K)) := by
  letI : Fintype (idealPrimeDivisors K I) :=
    (idealPrimeDivisors_finite K I hI).fintype
  let χ : rootsOfUnity ((6 : ℕ+) : ℕ) (𝓞 K) →* ℂ :=
    ((σ.comp (algebraMap (𝓞 K) K)).toMonoidHom.comp (Units.coeHom (𝓞 K))).comp
      (rootsOfUnity ((6 : ℕ+) : ℕ) (𝓞 K)).subtype
  change sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
    (algebraMap (𝓞 K) (S.integer K) a) =
    χ (idealPowerResidueSymbol K I hI (6 : ℕ+) hmu a hcoprime ha)
  rw [idealPowerResidueSymbol_eq_prod, map_prod]
  unfold sIntegerSexticIdealEvaluation
  apply Finset.prod_congr rfl
  intro p _
  rw [map_pow, sIntegerSexticEvaluation_algebraMap]
  apply congrArg (fun z : ℂ => z ^ idealPrimeMultiplicity K p.val I)
  exact sexticResidueEvaluation_eq_powerResidueSymbol K ζ hζ σ p.val
    (h6 p.val p.property) a (ha p.val p.property)

end HeckeGeneral.Characters
