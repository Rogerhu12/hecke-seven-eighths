import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentMoment

/-!
# Corrections preserving the original finite theta set

The original theta set need not be a subgroup. Only the actual character
corrections must permute it. These corrections form its stabilizer
subgroup, so ratio-based exceptional partitions can use the same finite
set without imposing closure on the set itself.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]

/-- The one actual correction permutes the original finite theta set. -/
def ActualThetaAction (theta : Finset (HeckeCharacter F)) (χ : HeckeCharacter F) : Prop :=
  theta.image (fun ψ => χ * ψ) = theta

namespace ActualThetaAction

variable {theta : Finset (HeckeCharacter F)} {χ : HeckeCharacter F}

theorem mul_mem_iff (hχ : ActualThetaAction theta χ) (ψ : HeckeCharacter F) :
    χ * ψ ∈ theta ↔ ψ ∈ theta := by
  constructor
  · intro hmem
    have hi : χ * ψ ∈ theta.image (fun η => χ * η) := by
      rw [hχ]
      exact hmem
    obtain ⟨η, hη, he⟩ := Finset.mem_image.mp hi
    have hηψ : η = ψ := mul_left_cancel he
    exact hηψ ▸ hη
  · intro hmem
    have hi : χ * ψ ∈ theta.image (fun η => χ * η) :=
      Finset.mem_image.mpr ⟨ψ, hmem, rfl⟩
    rwa [hχ] at hi

theorem inv_mul_mem_iff (hχ : ActualThetaAction theta χ) (ψ : HeckeCharacter F) :
    χ⁻¹ * ψ ∈ theta ↔ ψ ∈ theta := by
  have hh := hχ.mul_mem_iff (χ⁻¹ * ψ)
  have he : χ * (χ⁻¹ * ψ) = ψ := by group
  rw [he] at hh
  exact hh.symm

theorem inv (hχ : ActualThetaAction theta χ) : ActualThetaAction theta χ⁻¹ := by
  apply Finset.ext
  intro ψ
  constructor
  · intro hmem
    obtain ⟨η, hη, he⟩ := Finset.mem_image.mp hmem
    rw [← he]
    exact (hχ.inv_mul_mem_iff η).mpr hη
  · intro hmem
    refine Finset.mem_image.mpr ⟨χ * ψ, (hχ.mul_mem_iff ψ).mpr hmem, ?_⟩
    group

theorem one : ActualThetaAction theta 1 := by
  change theta.image (fun ψ => (1 : HeckeCharacter F) * ψ) = theta
  simpa only [one_mul] using (Finset.image_id (s := theta))

theorem mul (hχ : ActualThetaAction theta χ) {η : HeckeCharacter F}
    (hη : ActualThetaAction theta η) :
    ActualThetaAction theta (χ * η) := by
  change theta.image (fun ψ => (χ * η) * ψ) = theta
  calc
    _ = (theta.image (fun ψ => η * ψ)).image (fun ψ => χ * ψ) := by
      simp only [Finset.image_image, Function.comp_def, mul_assoc]
    _ = theta := by rw [hη, hχ]

/-- Exceptional membership depends only on a ratio acting on theta. -/
theorem mem_iff_of_ratio {x y : HeckeCharacter F}
    (h : ActualThetaAction theta (x / y)) : x ∈ theta ↔ y ∈ theta := by
  simpa only [div_mul_cancel] using h.mul_mem_iff y

/-- This is a subgroup of corrections; theta itself remains a Finset. -/
def stabilizer (theta : Finset (HeckeCharacter F)) : Subgroup (HeckeCharacter F) where
  carrier := {χ | ActualThetaAction theta χ}
  one_mem' := one
  mul_mem' := by
    intro χ η hχ hη
    exact hχ.mul hη
  inv_mem' := by
    intro χ hχ
    exact hχ.inv

@[simp] theorem mem_stabilizer (theta : Finset (HeckeCharacter F)) (χ : HeckeCharacter F) :
    χ ∈ stabilizer theta ↔ ActualThetaAction theta χ := Iff.rfl

/-- Compatibility with the older, stronger subgroup presentation. -/
theorem of_subgroup (Θ : Subgroup (HeckeCharacter F))
    (hmem : ∀ ψ, ψ ∈ theta ↔ ψ ∈ Θ) (χ : HeckeCharacter F) (hχ : χ ∈ Θ) :
    ActualThetaAction theta χ := by
  apply Finset.ext
  intro ψ
  constructor
  · intro h
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp h
    exact (hmem _).mpr (Θ.mul_mem hχ ((hmem η).mp hη))
  · intro h
    refine Finset.mem_image.mpr ⟨χ⁻¹ * ψ,
      (hmem _).mpr (Θ.mul_mem (Θ.inv_mem hχ) ((hmem ψ).mp h)), ?_⟩
    group

end ActualThetaAction
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaAction.stabilizer
#print axioms HeckeSkeleton.Moments.EngineStep.ActualThetaAction.mem_iff_of_ratio
