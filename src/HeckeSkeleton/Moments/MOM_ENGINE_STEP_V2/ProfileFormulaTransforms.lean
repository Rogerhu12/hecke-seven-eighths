module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormula
public import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzDilation

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Internal positive-dilation and conjugation estimates for N5a

Every constant and finite set of input orders is chosen before the
original profile. Dilation is allowed on any fixed positive interval,
including dilation factors below one. The representatives are the
literal global functions in `ProfileFormula.value`.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormulaProof

open HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzDilation

private def conjugation : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

private def oriented (b : Bool) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  if b then conjugation φ else φ

private theorem oriented_apply (b : Bool) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    oriented b φ x = if b then star (φ x) else φ x := by
  cases b <;> rfl

private theorem oriented_support (b : Bool) (φ : 𝓢(ℝ, ℂ)) :
    Function.support (oriented b φ) ⊆ Function.support φ := by
  intro x hx
  change oriented b φ x ≠ 0 at hx
  change φ x ≠ 0
  intro hzero
  apply hx
  rw [oriented_apply, hzero]
  cases b <;> simp

private theorem complex_real_finset_seminorm (q : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) :
    q.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ =
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) φ := by
  rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

private theorem conjugation_finset_bound (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓢(ℝ, ℂ),
      q.sup (schwartzSeminormFamily ℂ ℝ ℂ) (conjugation φ) ≤
        C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  let p : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp conjugation.toLinearMap
  have hq : Continuous (fun φ : 𝓢(ℝ, ℂ) =>
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) φ) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hq.comp conjugation.continuous)
  refine ⟨s, C, C.property, fun φ => ?_⟩
  rw [complex_real_finset_seminorm, complex_real_finset_seminorm]
  exact Seminorm.le_def.mp hb φ

private theorem oriented_finset_bound (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Bool, ∀ φ : 𝓢(ℝ, ℂ),
      q.sup (schwartzSeminormFamily ℂ ℝ ℂ) (oriented b φ) ≤
        C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  obtain ⟨s, C, hC, hb⟩ := conjugation_finset_bound q
  refine ⟨q ∪ s, C + 1, by positivity, fun b φ => ?_⟩
  have hq : q.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      (q ∪ s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left s hi)
  have hs : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
      (q ∪ s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_right q hi)
  cases b
  · change q.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ _
    exact hq.trans (le_mul_of_one_le_left (apply_nonneg _ _) (by linarith))
  · change q.sup (schwartzSeminormFamily ℂ ℝ ℂ) (conjugation φ) ≤ _
    exact (hb φ).trans (mul_le_mul (by linarith) hs (apply_nonneg _ _) (by positivity))

private theorem seminorm_dilate_interval
    (lower upper a : ℝ) (hlower : 0 < lower) (ha : 0 < a)
    (hla : lower ≤ a) (hau : a ≤ upper) (φ : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (dilate a ha φ) ≤
      ((max 1 upper) ^ n * (max 1 lower⁻¹) ^ k) * SchwartzMap.seminorm ℂ k n φ := by
  have hfactor : 0 ≤ (max 1 upper) ^ n * (max 1 lower⁻¹) ^ k := by positivity
  apply SchwartzMap.seminorm_le_bound ℂ k n _
    (mul_nonneg hfactor (apply_nonneg _ _))
  intro x
  rw [iteratedFDeriv_dilate, norm_smul, norm_pow, Real.norm_of_nonneg ha.le]
  have hx : ‖x‖ = a⁻¹ * ‖a * x‖ := by
    rw [norm_mul, Real.norm_of_nonneg ha.le, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  have haInv : a⁻¹ ≤ lower⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlower hla
  have hcoeff : a ^ n * (a⁻¹) ^ k ≤ (max 1 upper) ^ n * (max 1 lower⁻¹) ^ k :=
    mul_le_mul
      (pow_le_pow_left₀ ha.le (hau.trans (le_max_right _ _)) n)
      (pow_le_pow_left₀ (inv_nonneg.mpr ha.le) (haInv.trans (le_max_right _ _)) k)
      (pow_nonneg (inv_nonneg.mpr ha.le) k) (pow_nonneg (by positivity) n)
  calc
    ‖x‖ ^ k * (a ^ n * ‖iteratedFDeriv ℝ n φ (a * x)‖) =
        (a ^ n * (a⁻¹) ^ k) *
          (‖a * x‖ ^ k * ‖iteratedFDeriv ℝ n φ (a * x)‖) := by
      rw [hx, mul_pow]
      ring
    _ ≤ (a ^ n * (a⁻¹) ^ k) * SchwartzMap.seminorm ℂ k n φ :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k n φ (a * x)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (apply_nonneg _ _)

private def dilationCoefficient (lower upper : ℝ) (q : Finset (ℕ × ℕ)) : ℝ :=
  ∑ i ∈ q, (max 1 upper) ^ i.2 * (max 1 lower⁻¹) ^ i.1

private theorem dilationCoefficient_nonneg (lower upper : ℝ) (q : Finset (ℕ × ℕ)) :
    0 ≤ dilationCoefficient lower upper q := by
  unfold dilationCoefficient
  exact Finset.sum_nonneg (fun _ _ => by positivity)

private theorem finite_seminorm_dilate_interval
    (lower upper : ℝ) (hlower : 0 < lower) (q : Finset (ℕ × ℕ))
    (a : ℝ) (ha : 0 < a) (hla : lower ≤ a) (hau : a ≤ upper) (φ : 𝓢(ℝ, ℂ)) :
    q.sup (schwartzSeminormFamily ℂ ℝ ℂ) (dilate a ha φ) ≤
      dilationCoefficient lower upper q * q.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  have hC := dilationCoefficient_nonneg lower upper q
  apply Seminorm.finset_sup_apply_le (mul_nonneg hC (apply_nonneg _ _))
  intro i hi
  have hsingle : (max 1 upper) ^ i.2 * (max 1 lower⁻¹) ^ i.1 ≤
      dilationCoefficient lower upper q := by
    unfold dilationCoefficient
    exact Finset.single_le_sum
      (f := fun j : ℕ × ℕ => (max 1 upper) ^ j.2 * (max 1 lower⁻¹) ^ j.1)
      (fun j (_ : j ∈ q) => by positivity) hi
  exact (seminorm_dilate_interval lower upper a hlower ha hla hau φ i.1 i.2).trans
    (mul_le_mul hsingle
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (x := φ) hi)
      (apply_nonneg _ _) hC)

/-- The prescribed conjugation and positive dilation, before powers and phase. -/
def inputProfile (f : ProfileFormula) : 𝓢(ℝ, ℂ) :=
  dilate f.dilation f.dilation_pos (oriented f.conjugate f.original)

theorem inputProfile_apply (f : ProfileFormula) (x : ℝ) :
    inputProfile f x =
      if f.conjugate then star (f.original (f.dilation * x))
      else f.original (f.dilation * x) := by
  rw [inputProfile, dilate_apply, oriented_apply]

theorem inputProfile_support (f : ProfileFormula) (lower upper : ℝ)
    (hs : Function.support f.original ⊆ Set.Icc lower upper) :
    Function.support (inputProfile f) ⊆ f.window lower upper := by
  intro x hx
  have hox : oriented f.conjugate f.original (f.dilation * x) ≠ 0 := by
    simpa only [Function.mem_support, inputProfile, dilate_apply] using hx
  have hloc := hs (oriented_support f.conjugate f.original hox)
  change lower / f.dilation ≤ x ∧ x ≤ upper / f.dilation
  constructor
  · exact (div_le_iff₀ f.dilation_pos).mpr (by simpa only [mul_comm] using hloc.1)
  · exact (le_div_iff₀ f.dilation_pos).mpr (by simpa only [mul_comm] using hloc.2)

/-- A finite input-order set and one constant control every allowed orientation
and dilation. Neither is selected after the original profile. -/
theorem inputProfile_finset_bound (shape : ProfileShape) (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ProfileFormula, f.Bounded shape →
      q.sup (schwartzSeminormFamily ℂ ℝ ℂ) (inputProfile f) ≤
        C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f.original := by
  obtain ⟨s, C, hC, hb⟩ := oriented_finset_bound q
  let D := dilationCoefficient shape.dilationLower shape.dilationUpper q
  have hD : 0 ≤ D := dilationCoefficient_nonneg _ _ _
  refine ⟨s, D * C, mul_nonneg hD hC, fun f hf => ?_⟩
  have hd := finite_seminorm_dilate_interval
    shape.dilationLower shape.dilationUpper shape.dilationLower_pos q
    f.dilation f.dilation_pos hf.dilation_lower hf.dilation_upper
    (oriented f.conjugate f.original)
  exact hd.trans ((mul_le_mul_of_nonneg_left (hb f.conjugate f.original) hD).trans_eq
    (by ring))

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormulaProof
