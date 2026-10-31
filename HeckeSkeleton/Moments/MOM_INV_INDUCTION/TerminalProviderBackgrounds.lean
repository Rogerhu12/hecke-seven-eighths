import HeckeSkeleton.Moments.MOM_INV_STEP.BackgroundCycle
import HeckeSkeleton.Moments.MOM_BASE.FiniteBackground
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# One fixed finite inventory of terminal periods

The original finite twist list and the calibration twist generate a
finite subgroup: its generators have finite order and the Hecke character
group is commutative.  Every coefficient cycle remains in the two classes
Θ and ψΘ.  The reflected-energy constants are chosen for the finite image
of these two classes under ν ↦ νΛ⁻¹, with Θ, ψ and Λ already fixed.

This inventory is independent of the scale, row, label, and recursion
depth.  No finiteness of a varying family of arbitrary backgrounds is
asserted.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalBackgrounds

open NumberField IsDedekindDomain HeckeGeneral.Characters
  HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOM_INV_STEP
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- Only the original finite twists and the fixed calibration character
are needed to close the background class under both coefficient cycles. -/
def generatedTwists (theta : Finset (HeckeCharacter K)) (G : HeckeCharacter K) :
    Subgroup (HeckeCharacter K) :=
  Subgroup.closure (↑(insert G theta) : Set (HeckeCharacter K))

theorem mem_generatedTwists (theta : Finset (HeckeCharacter K))
    (G θ : HeckeCharacter K) (hθ : θ ∈ theta) :
    θ ∈ generatedTwists K theta G :=
  Subgroup.subset_closure (Finset.mem_insert_of_mem hθ)

theorem calibration_mem_generatedTwists (theta : Finset (HeckeCharacter K))
    (G : HeckeCharacter K) : G ∈ generatedTwists K theta G :=
  Subgroup.subset_closure (Finset.mem_insert_self _ _)

theorem generatedTwists_finiteOrder (theta : Finset (HeckeCharacter K))
    (G : HeckeCharacter K) (htheta : ∀ θ ∈ theta, FiniteOrder θ)
    (hG : FiniteOrder G) (ν : HeckeCharacter K)
    (hν : ν ∈ generatedTwists K theta G) : FiniteOrder ν := by
  refine Subgroup.closure_induction (p := fun ν _ => FiniteOrder ν)
    ?_ IsOfFinOrder.one ?_ ?_ hν
  · intro θ hθ
    rcases Finset.mem_insert.mp hθ with rfl | hθ
    · exact hG
    · exact htheta θ hθ
  · intro θ η hθ hη hfθ hfη
    exact hfθ.mul hfη
  · intro θ hθ hfθ
    exact hfθ.inv

/-- Finiteness is proved from the source's finite-order hypotheses,
rather than added as a property of the terminal node. -/
theorem generatedTwists_finite (theta : Finset (HeckeCharacter K))
    (G : HeckeCharacter K) (htheta : ∀ θ ∈ theta, FiniteOrder θ)
    (hG : FiniteOrder G) : Finite (generatedTwists K theta G) := by
  letI : Group.FG (generatedTwists K theta G) := by
    dsimp only [generatedTwists]
    infer_instance
  apply CommGroup.finite_of_fg_isMulTorsion (generatedTwists K theta G)
  intro ν
  exact (Function.Injective.isOfFinOrder_iff
    (f := (generatedTwists K theta G).subtype) Subtype.coe_injective).mp
      (generatedTwists_finiteOrder K theta G htheta hG ν.val ν.property)

theorem generatedTwists_unramified
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (theta : Finset (HeckeCharacter K)) (G : HeckeCharacter K)
    (htheta : ∀ θ ∈ theta, ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ S → UnramifiedAt K θ p)
    (hG : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K G p)
    (ν : HeckeCharacter K) (hν : ν ∈ generatedTwists K theta G) :
    ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p := by
  refine Subgroup.closure_induction
    (p := fun ν _ => ∀ p : HeightOneSpectrum (𝓞 K),
      p ∉ S → UnramifiedAt K ν p) ?_ ?_ ?_ ?_ hν
  · intro θ hθ
    rcases Finset.mem_insert.mp hθ with rfl | hθ
    · exact hG
    · exact htheta θ hθ
  · intro p hp
    exact unramifiedAt_one K p
  · intro θ η hθ hη huθ huη p hp
    exact (huθ p hp).mul K (huη p hp)
  · intro θ hθ huθ p hp
    exact (huθ p hp).inv K

/-- The actual directed inverse background belongs to this fixed class
using the existing `MomentData.directed_background` field. -/
theorem directed_background_admissible
    (ω ψ : HeckeCharacter K) (d : MomentData K ω ψ) (G : HeckeCharacter K) :
    BackgroundCycle.Admissible K (generatedTwists K d.theta G) ψ
      (d.inverseBackground ^ (-d.direction)) := by
  rcases d.directed_background with h | ⟨θ, hθ, heq⟩
  · exact Or.inl (mem_generatedTwists K d.theta G _ h)
  · exact Or.inr ⟨θ, mem_generatedTwists K d.theta G θ hθ, heq⟩

/-- This finite set is fixed before invoking the general reflected
energy input.  Its elements are the literal periods used by completed
canonical columns, including the original Λ normalization. -/
def periodInventory (Θ : Subgroup (HeckeCharacter K)) [Finite Θ]
    (ψ Λ : HeckeCharacter K) : Finset (HeckeCharacter K) := by
  letI := Fintype.ofFinite Θ
  exact (Finset.univ.image (fun θ : Θ => θ.val * Λ⁻¹)) ∪
    (Finset.univ.image (fun θ : Θ => (ψ * θ.val) * Λ⁻¹))

theorem period_mem_inventory (Θ : Subgroup (HeckeCharacter K)) [Finite Θ]
    (ψ Λ ν : HeckeCharacter K) (hν : BackgroundCycle.Admissible K Θ ψ ν) :
    ν * Λ⁻¹ ∈ periodInventory K Θ ψ Λ := by
  classical
  unfold periodInventory
  rcases hν with hν | ⟨θ, hθ, rfl⟩
  · exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨⟨ν, hν⟩, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨⟨θ, hθ⟩, Finset.mem_univ _, rfl⟩)

/-- Both genuine coefficient changes retain membership in the same
finite inventory.  In particular no new inventory is chosen at a child. -/
theorem cycle_periods_mem_inventory (Θ : Subgroup (HeckeCharacter K)) [Finite Θ]
    (ψ Λ ν G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ ν) (hG : G ∈ Θ) :
    (ν * G) * Λ⁻¹ ∈ periodInventory K Θ ψ Λ ∧
      (ν * G⁻¹) * Λ⁻¹ ∈ periodInventory K Θ ψ Λ := by
  exact ⟨period_mem_inventory K Θ ψ Λ _
      (BackgroundCycle.admissible_mul K Θ ψ ν G hν hG),
    period_mem_inventory K Θ ψ Λ _
      (BackgroundCycle.admissible_mul_inv K Θ ψ ν G hν hG)⟩

theorem inventory_unramified (S : Set (HeightOneSpectrum (𝓞 K)))
    (Θ : Subgroup (HeckeCharacter K)) [Finite Θ] (ψ Λ : HeckeCharacter K)
    (hΘ : ∀ θ ∈ Θ, ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hψ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ψ p)
    (hΛ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K Λ p)
    (ν : HeckeCharacter K) (hν : ν ∈ periodInventory K Θ ψ Λ) :
    ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p := by
  classical
  unfold periodInventory at hν
  rcases Finset.mem_union.mp hν with hν | hν
  · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hν
    intro p hp
    exact (hΘ θ.val θ.property p hp).mul K ((hΛ p hp).inv K)
  · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hν
    intro p hp
    exact ((hψ p hp).mul K (hΘ θ.val θ.property p hp)).mul K ((hΛ p hp).inv K)

/-- The finite inventory for the actual target also has the original
nonzero angular period condition, including the ψΘ class. -/
theorem inventory_nonzero_angular (c : TargetContext K)
    (Θ : Subgroup (HeckeCharacter K)) [Finite Θ]
    (ν : HeckeCharacter K)
    (hν : ν ∈ periodInventory K Θ (targetCharacter K c) (signalCharacters K c).1) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv ν ≠ 0 := by
  classical
  unfold periodInventory at hν
  rcases Finset.mem_union.mp hν with hν | hν
  · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hν
    have hf : FiniteOrder θ.val :=
      (Function.Injective.isOfFinOrder_iff (f := Θ.subtype)
        Subtype.coe_injective).mpr (isOfFinOrder_of_finite θ)
    simpa only [canonicalPeriod, mul_comm] using
      canonicalPeriod_finite_nonzero_angular K c θ.val hf
  · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hν
    have hf : FiniteOrder θ.val :=
      (Function.Injective.isOfFinOrder_iff (f := Θ.subtype)
        Subtype.coe_injective).mpr (isOfFinOrder_of_finite θ)
    simpa only [canonicalPeriod, mul_comm] using
      canonicalPeriod_target_finite_nonzero_angular K c θ.val hf

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalBackgrounds

end
