import HeckeSkeleton.Moments.MOM_ENGINE_STEP.TailBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualTupleCount

/-! # Whole-factor fibre counts for the actual truncation carrier -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ι κ : Type*}

/-- The injective case is the fibre-one case of the same carrier theorem. -/
theorem factor_fiber_card_le_one {α β : Type*} (S : Finset α) (f : α → β)
    (hinj : Set.InjOn f (S : Set α)) (v : β) :
    (S.filter (fun x => f x = v)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)

theorem first_common_label_tuple_card_of_fibers
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    {k : ℕ} (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ)
    (hfiber : ∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity)
    (hproduct : ∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val)
    (X : ℝ) (hX : 1 ≤ X)
    (hnorm : ∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ X) :
    ((firstZeroPairs left right fullI fullJ).card : ℝ) ≤
      (multiplicity : ℝ) * (idealCountConstant K * X) ^ k := by
  let S := left ×ˢ right
  have hc := whole_ideal_tuple_card (S.image factors) id (fun _ _ _ _ he => he) X hX
    (by
      intro v hv
      obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hv
      change PowerfulDiagonal.tupleIdeal (factors ij) ≠ 0
      rw [hproduct ij hij]
      exact mul_ne_zero (fullI ij.1).property.1 (fullJ ij.2).property.1)
    (by
      intro v hv
      obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hv
      change (Ideal.absNorm (PowerfulDiagonal.tupleIdeal (factors ij)) : ℝ) ≤ X
      rw [hproduct ij hij]
      exact hnorm ij hij)
  have hSc : (S.card : ℝ) ≤ (multiplicity : ℝ) * (S.image factors).card := by
    simpa using positive_pushforward_bound S factors (fun _ => (1 : ℝ))
      (multiplicity : ℝ) (fun _ _ => zero_le_one)
      (fun v _ => by exact_mod_cast hfiber v)
  have hlabels : (firstZeroPairs left right fullI fullJ).card ≤ S.card := by
    have hi := firstZeroPairs_projection_injective left right fullI fullJ
    have hs : (firstZeroPairs left right fullI fullJ).image Prod.snd ⊆ S := by
      intro ij hij
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij
      have hm := (mem_firstZeroPairs left right fullI fullJ v).mp hv
      exact Finset.mem_product.mpr ⟨hm.1, hm.2.1⟩
    have ht := Finset.card_le_card hs
    rw [Finset.card_image_of_injOn hi] at ht
    exact ht
  exact (Nat.cast_le.mpr hlabels).trans
    (hSc.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_common_label_tuple_card_of_fibers
