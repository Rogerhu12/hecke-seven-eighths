import Expansion.CanonicalDetectorCharacters
import Expansion.PhysicalRowPoleExclusion
import HeckeGeneral.Characters.RadialNormalization

/-!
# Full model exclusion and eventual physical row eligibility

The positive-slot model's finite character filter excludes cancellation of
its plain background at every scale. Separately, the arithmetic finite-fiber
theorem makes every sufficiently large physical row eligible for this same
filter. Neither statement substitutes a high-shell assertion for a claim
about the full model ball.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (ψ : HeckeCharacter K)

theorem canonicalDetector_plain_ne_one (i : Fin 2) (χ : HeckeCharacter K)
    (hχ : FiniteOrder χ)
    (hnot : χ ∉ (canonicalDetectorPresentation K ψ i).theta) :
    (canonicalDetectorPresentation K ψ i).plainBackground * χ ≠ 1 := by
  intro h
  let η := (canonicalDetectorPresentation K ψ i).plainBackground
  have heq : χ = η⁻¹ := by
    calc
      χ = η⁻¹ * (η * χ) := by group
      _ = η⁻¹ := by rw [h, mul_one]
  have hη : FiniteOrder η := by simpa only [heq, inv_inv] using hχ.inv
  exact hnot (heq.symm ▸ canonicalDetectorPresentation_plain_inverse_mem K ψ i hη)

theorem canonicalDetector_plain_radial_zero (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w ψ = 0) (i : Fin 2)
    (χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    heckeRadialParameter K w
      ((canonicalDetectorPresentation K ψ i).plainBackground * χ) = 0 := by
  rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K w hχ, add_zero]
  by_cases hi : i = 0
  · simp [canonicalDetectorPresentation, canonicalDetectorBackground, hi]
  · simp [canonicalDetectorPresentation, canonicalDetectorBackground, hi,
      heckeRadialParameter_inv, hψ]

/-- For the full positive-slot model, the existing theta filter now gives
the norm-twist exclusion required by the functional equation. -/
theorem canonicalDetector_plain_ne_normTwist (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w ψ = 0) (i : Fin 2)
    (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (hnot : χ ∉ (canonicalDetectorPresentation K ψ i).theta) (t : ℝ) :
    (canonicalDetectorPresentation K ψ i).plainBackground * χ ≠ heckeNormTwist K t :=
  ne_normTwist_of_radial_zero K w _
    (canonicalDetector_plain_radial_zero K ψ w hψ i χ hχ)
    (canonicalDetector_plain_ne_one K ψ i χ hχ hnot) t

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- A finite family of characters has only finitely many original rows,
so its exclusion is eventual with a threshold independent of the scale. -/
theorem exists_finite_rowCharacter_cutoff (T : Finset (HeckeCharacter K)) :
    ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ u : FrequencyRow K S,
      U₀ < frequencyRowNorm K S u → R.character u ∉ T := by
  have hfinite : Set.Finite {u : FrequencyRow K S | arithmeticRowCharacter K S P u ∈ T} := by
    change Finite {u : FrequencyRow K S // arithmeticRowCharacter K S P u ∈ T}
    exact arithmeticRowCharacter_finiteFamily_finite K S P T
  obtain ⟨C, hC⟩ := (hfinite.image (frequencyRowNorm K S)).bddAbove
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro u hu hmem
  have hmem' : arithmeticRowCharacter K S P u ∈ T := by
    rwa [← rowCharacterInput_character_eq_arithmetic K S P R u]
  have hnorm : frequencyRowNorm K S u ≤ C := hC ⟨u, hmem', rfl⟩
  exact (not_lt_of_ge (hnorm.trans (le_max_right _ _))) hu

theorem exists_canonicalDetectorTheta_cutoff :
    ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ u : FrequencyRow K S,
      U₀ < frequencyRowNorm K S u → ∀ i : Fin 2,
        R.character u ∉ (canonicalDetectorPresentation K ψ i).theta := by
  obtain ⟨U₀, hU₀, h⟩ := exists_finite_rowCharacter_cutoff K S P R
    (canonicalDetectorTheta K ψ)
  exact ⟨U₀, hU₀, fun u hu _ => h u hu⟩

end Expansion.Project

#print axioms Expansion.Project.canonicalDetector_plain_ne_one
#print axioms Expansion.Project.canonicalDetector_plain_ne_normTwist
#print axioms Expansion.Project.exists_canonicalDetectorTheta_cutoff
