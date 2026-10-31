import ArithmeticFrequencyRowCharacterFibers
import RowCharacterCanonicalUniqueness
import HeckeGeneral.Analysis.TInputRanges
import Mathlib.Tactic.Group

/-!
# A common pole-exclusion threshold for the actual physical row family

The nonprincipal-row theorem only excludes norm twists for the row itself.
A fixed background can cancel a nonprincipal row. The proved finite-fiber
arithmetic theorem gives a finite exceptional set of original rows and a
norm threshold before the moving shell, zero or frequency. No exterior
unramifiedness of the backgrounds is assumed; S and the row are unchanged.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def normTwistExceptionalCharacter (η : HeckeCharacter K) : HeckeCharacter K :=
  let v : InfinitePlace K := Classical.choice inferInstance
  η⁻¹ * heckeNormTwist K (-heckeRadialParameter K v η)

/-- Finite order of the row fixes the only possible norm frequency from
its background's actual radial parameter. -/
theorem eq_exceptional_of_background_normTwist
    (η χ : HeckeCharacter K) (hχ : FiniteOrder χ) (t : ℝ)
    (h : η * χ = heckeNormTwist K t) :
    χ = normTwistExceptionalCharacter K η := by
  let v : InfinitePlace K := Classical.choice inferInstance
  have hp := congrArg (heckeRadialParameter K v) h
  rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hχ,
    heckeRadialParameter_normTwist] at hp
  have ht : t = -heckeRadialParameter K v η := by linarith
  calc
    χ = η⁻¹ * (η * χ) := by group
    _ = η⁻¹ * heckeNormTwist K (-heckeRadialParameter K v η) := by rw [h, ht]
    _ = normTwistExceptionalCharacter K η := rfl

def backgroundExceptionalCharacters (B : Finset (HeckeCharacter K)) :
    Finset (HeckeCharacter K) :=
  B.biUnion fun η => {normTwistExceptionalCharacter K η,
    (normTwistExceptionalCharacter K η)⁻¹}

theorem mem_backgroundExceptionalCharacters_of_normTwist
    (B : Finset (HeckeCharacter K)) (η χ : HeckeCharacter K)
    (hη : η ∈ B) (hχ : FiniteOrder χ) (t : ℝ)
    (h : η * χ = heckeNormTwist K t ∨ η * χ⁻¹ = heckeNormTwist K t) :
    χ ∈ backgroundExceptionalCharacters K B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨η, hη, ?_⟩
  rcases h with h | h
  · have heq := eq_exceptional_of_background_normTwist K η χ hχ t h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl heq
  · have heq := eq_exceptional_of_background_normTwist K η χ⁻¹ hχ.inv t h
    have heq' : χ = (normTwistExceptionalCharacter K η)⁻¹ := by
      simpa only [inv_inv] using congrArg Inv.inv heq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr heq'

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- The actual arithmetic fiber theorem supplies the finite exception
bound, with no assumed character injectivity or support restriction. -/
theorem exists_background_normTwist_cutoff (B : Finset (HeckeCharacter K)) :
    ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ u : FrequencyRow K S,
      U₀ < frequencyRowNorm K S u → ∀ η ∈ B, ∀ t : ℝ,
        η * R.character u ≠ heckeNormTwist K t ∧
        η * (R.character u)⁻¹ ≠ heckeNormTwist K t := by
  let T := backgroundExceptionalCharacters K B
  have hfinite : Set.Finite {u : FrequencyRow K S | arithmeticRowCharacter K S P u ∈ T} := by
    change Finite {u : FrequencyRow K S // arithmeticRowCharacter K S P u ∈ T}
    exact arithmeticRowCharacter_finiteFamily_finite K S P T
  obtain ⟨C, hC⟩ := (hfinite.image (frequencyRowNorm K S)).bddAbove
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro u hu η hη t
  have hnot : R.character u ∉ T := by
    intro hmem
    have hmem' : arithmeticRowCharacter K S P u ∈ T := by
      rwa [← rowCharacterInput_character_eq_arithmetic K S P R u]
    have hnorm : frequencyRowNorm K S u ≤ C := hC ⟨u, hmem', rfl⟩
    exact (not_lt_of_ge (hnorm.trans (le_max_right _ _))) hu
  constructor
  · intro h
    exact hnot (mem_backgroundExceptionalCharacters_of_normTwist K B η
      (R.character u) hη (R.finite_order u) t (Or.inl h))
  · intro h
    exact hnot (mem_backgroundExceptionalCharacters_of_normTwist K B η
      (R.character u) hη (R.finite_order u) t (Or.inr h))

def physicalBackgrounds (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) :
    Finset (HeckeCharacter K) :=
  Θ ∪ Θ.image (fun θ => ψ * θ) ∪ Θ.image (fun θ => conjugate ψ * θ)

/-- Uniform pole exclusion for the exact four physical presentations. -/
theorem exists_physicalRowFamily_normTwist_cutoff
    (ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K)) (E : RowEulerData K S P) :
    ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ u : FrequencyRow K S,
      U₀ < frequencyRowNorm K S u →
      ∀ χ ∈ physicalRowFamily K S ψ Θ P E u,
        ∀ t : ℝ, χ ≠ heckeNormTwist K t := by
  obtain ⟨U₀, hU₀, hbound⟩ :=
    exists_background_normTwist_cutoff K S P E.rows (physicalBackgrounds K ψ Θ)
  refine ⟨U₀, hU₀, ?_⟩
  intro u hu χ hχ t
  obtain ⟨θ, hθ, hχ⟩ := Finset.mem_biUnion.mp hχ
  have hplain : θ ∈ physicalBackgrounds K ψ Θ :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hθ)
  have htarget : ψ * θ ∈ physicalBackgrounds K ψ Θ :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨θ, hθ, rfl⟩))
  have hconjugate : conjugate ψ * θ ∈ physicalBackgrounds K ψ Θ :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨θ, hθ, rfl⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
  rcases hχ with rfl | rfl | rfl | rfl
  · exact (hbound u hu θ hplain t).1
  · exact (hbound u hu θ hplain t).2
  · exact (hbound u hu (ψ * θ) htarget t).2
  · exact (hbound u hu (conjugate ψ * θ) hconjugate t).1

end Expansion.Project

#print axioms Expansion.Project.eq_exceptional_of_background_normTwist
#print axioms Expansion.Project.exists_background_normTwist_cutoff
#print axioms Expansion.Project.exists_physicalRowFamily_normTwist_cutoff
