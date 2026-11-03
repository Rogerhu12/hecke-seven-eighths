import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
UNCOMPILED / native 0. The precise linear-composition Schwartz estimate,
including k=n=0, followed by genuine compact-family operator bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.SchwartzLinearCompositionDraft

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- No max-one loss is necessary, even for zero indices or trivial spaces. -/
theorem seminorm_comp_linearEquiv_le (e : E ≃L[ℝ] F)
    (f : SchwartzMap F ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ≤
      ‖e.symm.toContinuousLinearMap‖ ^ k * ‖e.toContinuousLinearMap‖ ^ n *
        SchwartzMap.seminorm ℂ k n f := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  have hx : ‖x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    have h2 : e.symm.toContinuousLinearMap (e x) = x := e.symm_apply_apply x
    rwa [h2] at h
  have hd :
      ‖iteratedFDeriv ℝ n (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) x‖ ≤
        ‖iteratedFDeriv ℝ n f (e x)‖ * ‖e.toContinuousLinearMap‖ ^ n := by
    change ‖iteratedFDeriv ℝ n ((f : F → ℂ) ∘ e.toContinuousLinearMap) x‖ ≤ _
    rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth n) x le_rfl]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ContinuousLinearEquiv.coe_coe] using
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ n f (e x)) (fun _ : Fin n => e.toContinuousLinearMap)
  calc
    _ ≤ (‖e.symm.toContinuousLinearMap‖ * ‖e x‖) ^ k *
        (‖iteratedFDeriv ℝ n f (e x)‖ * ‖e.toContinuousLinearMap‖ ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hx k) hd
        (norm_nonneg _) (by positivity)
    _ = (‖e.symm.toContinuousLinearMap‖ ^ k * ‖e.toContinuousLinearMap‖ ^ n) *
        (‖e x‖ ^ k * ‖iteratedFDeriv ℝ n f (e x)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k n f (e x))
      (by positivity)

theorem seminorm_zero_zero_comp_linearEquiv_le (e : E ≃L[ℝ] F)
    (f : SchwartzMap F ℂ) :
    SchwartzMap.seminorm ℂ 0 0 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ≤
      SchwartzMap.seminorm ℂ 0 0 f := by
  simpa only [pow_zero, one_mul] using seminorm_comp_linearEquiv_le e f 0 0

/-- Continuity of the two actual operator families on a compact set supplies
the constants; a family-uniform seminorm bound is not an input. -/
theorem exists_compact_family_seminorm_bound
    {T : Type*} [TopologicalSpace T] (C : Set T) (hC : IsCompact C)
    (e : T → E ≃L[ℝ] F)
    (he : Continuous (fun t => (e t).toContinuousLinearMap))
    (hi : Continuous (fun t => (e t).symm.toContinuousLinearMap)) (k n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ C, ∀ f : SchwartzMap F ℂ,
      SchwartzMap.seminorm ℂ k n
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e t) f) ≤
          B * SchwartzMap.seminorm ℂ k n f := by
  obtain ⟨A, hA, ha⟩ := (hC.image he).isBounded.exists_pos_norm_le
  obtain ⟨D, hD, hd⟩ := (hC.image hi).isBounded.exists_pos_norm_le
  refine ⟨D ^ k * A ^ n, by positivity, fun t ht f => ?_⟩
  have hforward : ‖(e t).toContinuousLinearMap‖ ≤ A :=
    ha _ (Set.mem_image_of_mem _ ht)
  have hinverse : ‖(e t).symm.toContinuousLinearMap‖ ≤ D :=
    hd _ (Set.mem_image_of_mem _ ht)
  calc
    _ ≤ ‖(e t).symm.toContinuousLinearMap‖ ^ k *
        ‖(e t).toContinuousLinearMap‖ ^ n * SchwartzMap.seminorm ℂ k n f :=
      seminorm_comp_linearEquiv_le (e t) f k n
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinverse k)
        (pow_le_pow_left₀ (norm_nonneg _) hforward n)
        (by positivity) (by positivity)) (apply_nonneg _ _)

end HeckeGeneral.Analysis.SchwartzLinearCompositionDraft
