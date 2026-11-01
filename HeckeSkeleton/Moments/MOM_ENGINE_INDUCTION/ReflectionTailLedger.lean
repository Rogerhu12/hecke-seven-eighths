import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Terminal

/-!
# Actual ordinary-reflection tail exponents

These inequalities account for the normalized long factor, the remaining
short factor and the entire prime product.  `overhead` includes both the
fixed conductor constant absorbed above the external threshold and the
actual remaining-ideal norm budget.  The prime cost is the absolute z/2
amplitude cost; it is not silently replaced by the stronger κz/2 bound.

One finite decay order handles all lengths, including unrestricted
zero-slot lengths above the width.  It is selected from fixed width,
overhead, slot and loss caps before moving scales and rows.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

/-- The common finite dyadic cutoff gives arbitrary saving even when the
long plain exponent exceeds the row width. -/
theorem reflection_dyadic_tail_exponent
    (M overhead long short z A gap cutoff : ℝ)
    (hM : 0 ≤ M) (hoverhead : 0 ≤ overhead) (hlong : 0 ≤ long)
    (hshort : short ≤ long) (hA : 1 ≤ A)
    (hcutoff : max (M - long + overhead) 0 + gap ≤ cutoff) :
    (A + 1 / 2) * (M - long + overhead) + (1 - A) * cutoff +
        (short + z) / 2 ≤
      3 * (M + overhead) / 2 + z / 2 - (A - 1) * gap := by
  have hc : (1 - A) * cutoff ≤
      (1 - A) * (max (M - long + overhead) 0 + gap) :=
    mul_le_mul_of_nonpos_left hcutoff (by linarith)
  by_cases hv : 0 ≤ M - long + overhead
  · rw [max_eq_left hv] at hc
    nlinarith
  · have hv' : M - long + overhead ≤ 0 := le_of_not_ge hv
    rw [max_eq_right hv'] at hc
    have hA0 : 0 ≤ A := by linarith
    have hprod : 0 ≤ A * (long - (M + overhead)) := mul_nonneg hA0 (by linarith)
    nlinarith

/-- A sufficiently long original factor contributes a genuine whole-
series terminal; the other factor is allowed to be just as long. -/
theorem reflection_whole_tail_exponent
    (M overhead long short z A gap : ℝ)
    (hshort : short ≤ long) (hA : 0 ≤ A)
    (hlong : M + overhead + gap ≤ long) :
    (A + 1 / 2) * (M - long + overhead) + (short + z) / 2 ≤
      (M + overhead) / 2 + z / 2 - A * gap := by
  have hprod : 0 ≤ A * (long - (M + overhead + gap)) :=
    mul_nonneg hA (by linarith)
  nlinarith

/-- A finite decay order is chosen before all moving node lengths.  The
same choice pays the explicit Euler-mass loss in either tail branch. -/
theorem exists_reflection_tail_decay_order
    (widthCap overheadCap slotCap loss saving gap δ : ℝ)
    (hwidth : 0 ≤ widthCap) (hoverhead : 0 ≤ overheadCap)
    (hslot : 0 ≤ slotCap) (hloss : 0 ≤ loss) (hsaving : 0 ≤ saving)
    (hgap : 0 < gap) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ δ ≤ A ∧
      3 * (widthCap + overheadCap) / 2 + slotCap / 2 + loss + saving ≤ (A - 1) * gap ∧
      (widthCap + overheadCap) / 2 + slotCap / 2 + loss + saving ≤ A * gap := by
  let L := 3 * (widthCap + overheadCap) / 2 + slotCap / 2 + loss + saving
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let A := δ + 2 + L / gap
  have hdiv : 0 ≤ L / gap := div_nonneg hL hgap.le
  have hmul : L / gap * gap = L := div_mul_cancel₀ L hgap.ne'
  refine ⟨A, by dsimp [A]; linarith, by dsimp [A]; linarith, ?_, ?_⟩
  · change L ≤ (δ + 2 + L / gap - 1) * gap
    nlinarith [mul_pos hδ hgap]
  · dsimp [A]
    dsimp [L] at hmul
    nlinarith [mul_pos hδ hgap]

/-- Explicit amplitude exponent after charging the actual Euler mass.
The entire slot exponent z remains in the displayed ledger. -/
theorem reflection_dyadic_tail_uniform_exponent
    (M overhead long short z A gap cutoff loss saving widthCap overheadCap slotCap : ℝ)
    (hM : 0 ≤ M) (hoverhead : 0 ≤ overhead) (hlong : 0 ≤ long)
    (hshort : short ≤ long) (hA : 1 ≤ A)
    (hwidth : M ≤ widthCap) (hoverheadCap : overhead ≤ overheadCap) (hslot : z ≤ slotCap)
    (hcutoff : max (M - long + overhead) 0 + gap ≤ cutoff)
    (hbudget : 3 * (widthCap + overheadCap) / 2 + slotCap / 2 + loss + saving ≤
      (A - 1) * gap) :
    (A + 1 / 2) * (M - long + overhead) + (1 - A) * cutoff +
        (short + z) / 2 + loss ≤ -saving := by
  have h := reflection_dyadic_tail_exponent M overhead long short z A gap cutoff
    hM hoverhead hlong hshort hA hcutoff
  linarith

/-- Uniform whole-series saving does not need any upper bound on the
long or short zero-slot plain length. -/
theorem reflection_whole_tail_uniform_exponent
    (M overhead long short z A gap loss saving widthCap overheadCap slotCap : ℝ)
    (hshort : short ≤ long) (hA : 0 ≤ A)
    (hlong : M + overhead + gap ≤ long)
    (hwidth : M ≤ widthCap) (hoverheadCap : overhead ≤ overheadCap) (hslot : z ≤ slotCap)
    (hbudget : (widthCap + overheadCap) / 2 + slotCap / 2 + loss + saving ≤ A * gap) :
    (A + 1 / 2) * (M - long + overhead) + (short + z) / 2 + loss ≤ -saving := by
  have h := reflection_whole_tail_exponent M overhead long short z A gap hshort hA hlong
  linarith

end HeckeSkeleton.Moments.EngineInduction
