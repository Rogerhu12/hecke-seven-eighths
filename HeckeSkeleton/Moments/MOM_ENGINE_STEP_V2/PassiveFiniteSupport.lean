import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact support replacement before the residual expansion

Both finite carriers may contain zero terms. Their intersection is used
to compare the sums without requiring one carrier to contain the other.
A common row translation is removed only after the exact polynomial
identity, so the original finite row weight is preserved.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveFiniteSupport

open EngineStep

variable {H I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem sum_replace (S T : Finset I) (f g : I → ℂ)
    (agree : ∀ i ∈ S ∩ T, f i = g i)
    (left_zero : ∀ i ∈ S, i ∉ T → f i = 0)
    (right_zero : ∀ i ∈ T, i ∉ S → g i = 0) :
    (∑ i ∈ S, f i) = ∑ i ∈ T, g i := by
  calc
    _ = ∑ i ∈ S ∩ T, f i := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro i hi hn
      exact left_zero i hi (fun ht => hn (Finset.mem_inter.mpr ⟨hi, ht⟩))
    _ = ∑ i ∈ S ∩ T, g i := Finset.sum_congr rfl agree
    _ = _ := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro i hi hn
      exact right_zero i hi (fun hs => hn (Finset.mem_inter.mpr ⟨hs, hi⟩))

theorem fourier_replace (S T : Finset I) (c d : I → ℂ)
    (x y : I → V) (ξ : V)
    (agree : ∀ i ∈ S ∩ T, c i = d i)
    (location : ∀ i ∈ S ∩ T, x i = y i)
    (left_zero : ∀ i ∈ S, i ∉ T → c i = 0)
    (right_zero : ∀ i ∈ T, i ∉ S → d i = 0) :
    jointFourierColumn S c x ξ = jointFourierColumn T d y ξ := by
  apply sum_replace S T
  · intro i hi
    rw [agree i hi, location i hi]
  · intro i hi hn
    rw [left_zero i hi hn, zero_mul]
  · intro i hi hn
    rw [right_zero i hi hn, zero_mul]

/-- The condition may be checked only on nonzero-weight rows. The
other summands are identically zero before either column is changed. -/
theorem energy_replace (rows : Finset H) (S T : Finset I) (q : H → ℂ)
    (c d : H → I → ℂ) (x y : H → I → V) (ξ : V)
    (agree : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S ∩ T, c h i = d h i)
    (location : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S ∩ T, x h i = y h i)
    (left_zero : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S, i ∉ T → c h i = 0)
    (right_zero : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ T, i ∉ S → d h i = 0) :
    jointColumnEnergy rows S q c x ξ = jointColumnEnergy rows T q d y ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hz : q h = 0
  · simp only [hz, norm_zero, zero_mul]
  · rw [fourier_replace S T (c h) (d h) (x h) (y h) ξ
      (agree h hh hz) (location h hh hz) (left_zero h hh hz) (right_zero h hh hz)]

theorem energy_replace_translation (rows : Finset H) (S T : Finset I) (q : H → ℂ)
    (c d : H → I → ℂ) (x y : H → I → V) (z : H → V) (ξ : V)
    (agree : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S ∩ T, c h i = d h i)
    (location : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S ∩ T, x h i = z h + y h i)
    (left_zero : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ S, i ∉ T → c h i = 0)
    (right_zero : ∀ h ∈ rows, q h ≠ 0 → ∀ i ∈ T, i ∉ S → d h i = 0) :
    jointColumnEnergy rows S q c x ξ = jointColumnEnergy rows T q d y ξ := by
  calc
    _ = jointColumnEnergy rows T q d (fun h i => z h + y h i) ξ :=
      energy_replace rows S T q c d x _ ξ agree location left_zero right_zero
    _ = _ := jointColumnEnergy_rowTranslation rows T q d y z ξ

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveFiniteSupport

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveFiniteSupport.energy_replace
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveFiniteSupport.energy_replace_translation
