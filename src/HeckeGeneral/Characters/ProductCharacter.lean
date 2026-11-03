import HeckeGeneral.Characters.SmallSubgroups
import Mathlib.Algebra.BigOperators.Pi

/-! Finite coordinate dependence for continuous circle characters on products. -/

noncomputable section

namespace HeckeGeneral.Characters

open Filter Topology
open scoped Classical

variable {ι : Type*} {G : ι → Type*}
variable [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]

/-- A character kills the entire complementary product, not merely its single factors. -/
theorem exists_finset_product_character_kernel (χ : (∀ i, G i) →ₜ* Circle) :
    ∃ S : Finset ι, ∀ u : ∀ i, G i, (∀ i ∈ S, u i = 1) → χ u = 1 := by
  have hneigh : χ ⁻¹' circleSmallArc ∈ 𝓝 (1 : ∀ i, G i) :=
    χ.continuous.continuousAt.preimage_mem_nhds
      (isOpen_circleSmallArc.mem_nhds (by simpa using one_mem_circleSmallArc))
  rw [nhds_pi] at hneigh
  obtain ⟨S, t, ht, hsub⟩ := Filter.mem_pi'.mp hneigh
  refine ⟨S, fun u hu => circle_eq_one_of_powers_re _ (fun n => ?_)⟩
  have hn : u ^ n ∈ Set.pi (↑S) t := by
    intro i hi
    change u i ^ n ∈ t i
    rw [hu i hi, one_pow]
    exact mem_of_mem_nhds (ht i)
  have hs := hsub hn
  change (1 / 2 : ℝ) < (χ (u ^ n) : ℂ).re at hs
  rw [map_pow] at hs
  exact hs.le

def productTruncation (S : Finset ι) (u : ∀ i, G i) : ∀ i, G i :=
  fun i => if i ∈ S then u i else 1

omit [∀ i, TopologicalSpace (G i)] in
@[simp] theorem productTruncation_apply_mem (S : Finset ι) (u : ∀ i, G i)
    {i : ι} (hi : i ∈ S) : productTruncation S u i = u i := by
  simp [productTruncation, hi]

omit [∀ i, TopologicalSpace (G i)] in
@[simp] theorem productTruncation_apply_not_mem (S : Finset ι) (u : ∀ i, G i)
    {i : ι} (hi : i ∉ S) : productTruncation S u i = 1 := by
  simp [productTruncation, hi]

omit [∀ i, TopologicalSpace (G i)] in
theorem productTruncation_eq_prod (S : Finset ι) (u : ∀ i, G i) :
    productTruncation S u = ∏ i ∈ S, Pi.mulSingle i (u i) := by
  funext i
  simp [productTruncation, Finset.prod_apply]

theorem product_character_eq_of_eq_on (χ : (∀ i, G i) →ₜ* Circle) (S : Finset ι)
    (hS : ∀ u : ∀ i, G i, (∀ i ∈ S, u i = 1) → χ u = 1)
    (u w : ∀ i, G i) (huw : ∀ i ∈ S, u i = w i) : χ u = χ w := by
  have h : χ (u * w⁻¹) = 1 := hS _ (fun i hi => by
    change u i * (w i)⁻¹ = 1
    rw [huw i hi, mul_inv_cancel])
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

theorem product_character_truncation (χ : (∀ i, G i) →ₜ* Circle) (S : Finset ι)
    (hS : ∀ u : ∀ i, G i, (∀ i ∈ S, u i = 1) → χ u = 1) (u : ∀ i, G i) :
    χ u = χ (productTruncation S u) :=
  product_character_eq_of_eq_on χ S hS u _ (fun i hi => by simp [hi])

theorem product_character_eq_prod (χ : (∀ i, G i) →ₜ* Circle) (S : Finset ι)
    (hS : ∀ u : ∀ i, G i, (∀ i ∈ S, u i = 1) → χ u = 1) (u : ∀ i, G i) :
    χ u = ∏ i ∈ S, χ (Pi.mulSingle i (u i)) := by
  rw [product_character_truncation χ S hS u, productTruncation_eq_prod, map_prod]

theorem exists_finset_product_character_eq_prod (χ : (∀ i, G i) →ₜ* Circle) :
    ∃ S : Finset ι, ∀ u : ∀ i, G i, χ u = ∏ i ∈ S, χ (Pi.mulSingle i (u i)) := by
  obtain ⟨S, hS⟩ := exists_finset_product_character_kernel χ
  exact ⟨S, product_character_eq_prod χ S hS⟩

/-- Any finite set containing all nontrivial coordinate restrictions suffices. -/
theorem product_character_eq_prod_of_trivial_outside (χ : (∀ i, G i) →ₜ* Circle)
    (S : Finset ι) (hS : ∀ i, i ∉ S → ∀ x : G i, χ (Pi.mulSingle i x) = 1)
    (u : ∀ i, G i) : χ u = ∏ i ∈ S, χ (Pi.mulSingle i (u i)) := by
  obtain ⟨T, hT⟩ := exists_finset_product_character_eq_prod χ
  have hTu := hT u
  rw [hTu]
  refine (Finset.prod_subset (Finset.subset_union_left (s₁ := T) (s₂ := S)) ?_).trans
    ((Finset.prod_subset (Finset.subset_union_right (s₁ := T) (s₂ := S)) ?_).symm)
  · intro i hi hnot
    have hiS : i ∈ S := (Finset.mem_union.mp hi).resolve_left hnot
    have heq : χ (Pi.mulSingle i (u i)) = 1 := by
      have hsingle := hT (Pi.mulSingle i (u i))
      have hprod : (∏ j ∈ T, χ (Pi.mulSingle j
          (Pi.mulSingle (M := G) i (u i) j))) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hnot hj
        simp [Pi.mulSingle_eq_of_ne hji]
      simpa [hprod] using hsingle
    exact heq
  · intro i _ hnot
    exact hS i hnot (u i)

end HeckeGeneral.Characters
