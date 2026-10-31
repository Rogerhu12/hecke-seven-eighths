import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientCycle
import HeckeGeneral.Analysis.HeckeConjugation
import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra

/-!
# The same live Hecke background after each coefficient cycle

The finite calibration twists are absorbed into actual Hecke characters,
not into a new arbitrary residual coefficient on the column. Multiplication
of ideal coefficients is proved on exterior ideals from the genuine
unramified prime coefficients. A fixed subgroup of finite twists preserves
the two allowed background classes Θ and ψΘ.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.BackgroundCycle

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Multiplication is required only at the original exterior places.
The live left character can retain any of its original ramified zeros. -/
theorem exterior_coefficient_mul (ν θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (I : ExteriorIdeal K S) :
    heckeIdealCoefficient K (ν * θ) I.val =
      heckeIdealCoefficient K ν I.val * heckeIdealCoefficient K θ I.val := by
  have hI : I.val.val ≠ ⊥ := by
    simpa only [Ideal.zero_eq_bot] using nonZeroDivisors.coe_ne_zero I.val
  unfold heckeIdealCoefficient nonzeroIdealCoefficient idealCoefficient
  rw [if_neg hI, if_neg hI, if_neg hI, ← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hp : Prime P := prime_of_normalized_factor P hP
  let p : HeightOneSpectrum (𝓞 K) := HeightOneSpectrum.ofPrime hp
  have hpd : p.asIdeal ∣ I.val.val := dvd_of_mem_normalizedFactors hP
  have hu := hθ p (I.property p hpd)
  simp only [primeIdealValue, dif_pos hp]
  exact primeCoefficient_mul_right_unramified K ν θ p hu

/-- An element of the two fixed background classes; membership is
independent of the new row and the new averaged label. -/
def Admissible (Θ : Subgroup (HeckeCharacter K)) (ψ ν : HeckeCharacter K) : Prop :=
  ν ∈ Θ ∨ ∃ θ : HeckeCharacter K, θ ∈ Θ ∧ ν = ψ * θ

theorem admissible_mul (Θ : Subgroup (HeckeCharacter K)) (ψ ν θ : HeckeCharacter K)
    (hν : Admissible K Θ ψ ν) (hθ : θ ∈ Θ) : Admissible K Θ ψ (ν * θ) := by
  rcases hν with hν | ⟨ω, hω, rfl⟩
  · exact Or.inl (Θ.mul_mem hν hθ)
  · exact Or.inr ⟨ω * θ, Θ.mul_mem hω hθ, mul_assoc _ _ _⟩

theorem admissible_mul_inv (Θ : Subgroup (HeckeCharacter K)) (ψ ν θ : HeckeCharacter K)
    (hν : Admissible K Θ ψ ν) (hθ : θ ∈ Θ) : Admissible K Θ ψ (ν * θ⁻¹) :=
  admissible_mul K Θ ψ ν θ⁻¹ hν (Θ.inv_mem hθ)

theorem admissible_unramified (Θ : Subgroup (HeckeCharacter K)) (ψ ν : HeckeCharacter K)
    (hΘ : ∀ θ ∈ Θ, ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hψ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ψ p)
    (hν : Admissible K Θ ψ ν) :
    ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p := by
  intro p hp
  rcases hν with hν | ⟨θ, hθ, rfl⟩
  · exact hΘ ν hν p hp
  · exact (hψ p hp).mul K (hΘ θ hθ p hp)

variable (D : ThetaArithmeticData K S) {Λ G : HeckeCharacter K}
variable (hcal : ThetaCalibrationInput K S D Λ G)

/-- The first transform retains precisely one genuine live character
νG, with its finite calibration twist absorbed in the same class. -/
include hcal in
theorem first_cycle_single_background (ν : HeckeCharacter K)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    CoefficientCycle.canonicalCoefficient K S D Λ I *
        heckeIdealCoefficient K ν I.val * thetaGamma K S D I 1 =
      (moebius I.val.val : ℂ) * heckeIdealCoefficient K (ν * G) I.val := by
  rw [CoefficientCycle.first_cycle_background hcal I hI,
    exterior_coefficient_mul K S ν G hcal.G_unramified I]
  ring

/-- The second transform returns a₀ with a genuine background νG⁻¹.
The original ν is not conjugated or discarded in this operation. -/
include hcal in
theorem second_cycle_single_background (ν : HeckeCharacter K)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (moebius I.val.val : ℂ) * heckeIdealCoefficient K ν I.val *
        conj (thetaGamma K S D I 1) =
      CoefficientCycle.canonicalCoefficient K S D Λ I *
        heckeIdealCoefficient K (ν * G⁻¹) I.val := by
  rw [CoefficientCycle.second_cycle_background hcal I hI,
    exterior_coefficient_mul K S ν G⁻¹
      (fun p hp => (hcal.G_unramified p hp).inv K) I,
    heckeIdealCoefficient_inv]
  ring

/-- The two coefficient changes preserve the same allowed class
without any additional column-dependent coefficient. -/
theorem two_cycles_preserve_class (Θ : Subgroup (HeckeCharacter K))
    (ψ ν : HeckeCharacter K) (hν : Admissible K Θ ψ ν) (hG : G ∈ Θ) :
    Admissible K Θ ψ (ν * G) ∧ Admissible K Θ ψ (ν * G * G⁻¹) ∧
      ν * G * G⁻¹ = ν := by
  refine ⟨admissible_mul K Θ ψ ν G hν hG,
    admissible_mul_inv K Θ ψ (ν * G) G (admissible_mul K Θ ψ ν G hν hG) hG, ?_⟩
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end HeckeSkeleton.Moments.MOM_INV_STEP.BackgroundCycle

end
