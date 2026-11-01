module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite nonnegative energies embed into the disjoint union of all sector fibres. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open scoped Classical BigOperators

/-- Reindex a nonnegative finite energy into all of its sector fibres.
The injection is allowed to distinguish equal ideals in different sectors. -/
theorem finite_sector_sum_le
    {ι α S V : Type*} [Fintype S]
    [AddCommMonoid V] [Preorder V] [AddLeftMono V]
    (R : Finset ι) (rows : S → Finset α)
    (ideal : ι → α) (sector : ι → S)
    (hinj : Function.Injective (fun u => (ideal u, sector u)))
    (hrows : ∀ u ∈ R, ideal u ∈ rows (sector u))
    (F : ι → V) (G : S → α → V)
    (hcal : ∀ u ∈ R, F u ≤ G (sector u) (ideal u))
    (hnonneg : ∀ s u, 0 ≤ G s u) :
    ∑ u ∈ R, F u ≤ ∑ s, ∑ u ∈ rows s, G s u := by
  classical
  let e : ι → Sigma (fun _ : S => α) := fun u => ⟨sector u, ideal u⟩
  have he : Function.Injective e := by
    intro u v huv
    apply hinj
    exact Prod.ext (congrArg (fun p : Sigma (fun _ : S => α) => p.2) huv)
      (congrArg (fun p : Sigma (fun _ : S => α) => p.1) huv)
  rw [Finset.sum_sigma']
  apply Finset.sum_le_sum_of_injOn e he.injOn
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hrows u hu⟩
  · exact hcal
  · intro p _ _
    exact hnonneg p.1 p.2

end HeckeSkeleton.Moments.UniformAmplify
