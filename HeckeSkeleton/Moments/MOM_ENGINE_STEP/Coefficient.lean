import HeckePort.CenteredMoment.Basic
import HeckePort.Moments.FullCorrelation
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Whole coefficients in a fourth-moment step

The coefficient below is built from the existing masked-character and
rectangle definitions.  The same finite slot set is used in both stages,
including the empty set.  Extraction and divisor allocation act on the
whole coefficient before any absolute value is taken.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open HeckePort.CenteredMoment

section Coefficients

variable {M R ι : Type*} [CommMonoid M] [CommRing R]

/-- Both stages use the same profiles, including formally empty rectangles. -/
def stageRectangle (centered : Bool) (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  if centered then rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b
  else W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂)

/-- The unmodified product index; the frozen factors occur in both rectangles. -/
def wholeIndex (slots : Finset ι) (p : ι → M) (b₁ b₂ l₁ l₂ : M) : M :=
  (∏ i ∈ slots, p i) * ((b₁ * l₁) * (b₂ * l₂))

/-- One whole-product character, one norm phase, and one common mask. -/
def wholeCoefficient (centered : Bool) (d : MaskedCharacter M R)
    (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι) (a : ι → ℂ) (p : ι → M)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M) : ℂ :=
  (∏ i ∈ slots, a i) *
    stageRectangle centered N W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * l₁) (b₂ * l₂) *
    coefficient d N t (wholeIndex slots p b₁ b₂ l₁ l₂)

theorem wholeCoefficient_centered (d : MaskedCharacter M R)
    (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι) (a : ι → ℂ) (p : ι → M)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M) :
    wholeCoefficient true d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ =
      wholeCoefficient false d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ -
      wholeCoefficient false d N t slots a p W₁ W₂ Y₁ Y₂ X₁ X₂ b₁ b₂ l₁ l₂ := by
  simp only [wholeCoefficient, stageRectangle, Bool.true_eq, ite_true, Bool.false_eq_true,
    ite_false, rectangle]
  ring

theorem wholeCoefficient_zero_of_mask (centered : Bool) (d : MaskedCharacter M R)
    (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι) (a : ι → ℂ) (p : ι → M)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M)
    (hmask : ¬d.keep (wholeIndex slots p b₁ b₂ l₁ l₂)) :
    wholeCoefficient centered d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ = 0 := by
  simp [wholeCoefficient, coefficient, MaskedCharacter.value, hmask]

theorem wholeCoefficient_zero_of_impossible_rectangle (centered : Bool)
    (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι)
    (a : ι → ℂ) (p : ι → M) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M)
    (hX : W₁ ((N (b₁ * l₁) : ℝ) / X₁) *
      W₂ ((N (b₂ * l₂) : ℝ) / X₂) = 0)
    (hY : W₁ ((N (b₁ * l₁) : ℝ) / Y₁) *
      W₂ ((N (b₂ * l₂) : ℝ) / Y₂) = 0) :
    wholeCoefficient centered d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ = 0 := by
  cases centered <;> simp [wholeCoefficient, stageRectangle, rectangle, hX, hY]

theorem extracted_scale_argument (N : M →* ℝ≥0) (b l : M) (X : ℝ) :
    (N (b * l) : ℝ) / X = (N l : ℝ) / (X / (N b : ℝ)) := by
  simp only [map_mul, NNReal.coe_mul, div_div_eq_mul_div]
  ring

/-- Both rectangles are rescaled together, including a formally empty one. -/
theorem stageRectangle_extract (centered : Bool) (N : M →* ℝ≥0)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M) :
    stageRectangle centered N W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * l₁) (b₂ * l₂) =
      stageRectangle centered N W₁ W₂
        (X₁ / (N b₁ : ℝ)) (X₂ / (N b₂ : ℝ))
        (Y₁ / (N b₁ : ℝ)) (Y₂ / (N b₂ : ℝ)) l₁ l₂ := by
  cases centered <;>
    simp only [stageRectangle, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
      rectangle, extracted_scale_argument]

theorem balanced_scales_extract (X₁ X₂ Y₁ Y₂ B₁ B₂ : ℝ)
    (hbalance : X₁ * X₂ = Y₁ * Y₂) :
    (X₁ / B₁) * (X₂ / B₂) = (Y₁ / B₁) * (Y₂ / B₂) := by
  simpa only [div_mul_div_comm] using congrArg (fun x : ℝ => x / (B₁ * B₂)) hbalance

theorem wholeIndex_extract (slots : Finset ι) (p : ι → M) (b₁ b₂ l₁ l₂ : M) :
    wholeIndex slots p b₁ b₂ l₁ l₂ =
      (b₁ * b₂) * wholeIndex slots p 1 1 l₁ l₂ := by
  simp only [wholeIndex, one_mul]
  ac_rfl

/-- Exact frozen-factor extraction; the same character and mask survive. -/
theorem wholeCoefficient_extract (centered : Bool) (d : MaskedCharacter M R)
    (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι) (a : ι → ℂ) (p : ι → M)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M) :
    wholeCoefficient centered d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ =
      coefficient d N t (b₁ * b₂) *
        wholeCoefficient centered d N t slots a p W₁ W₂
          (X₁ / (N b₁ : ℝ)) (X₂ / (N b₂ : ℝ))
          (Y₁ / (N b₁ : ℝ)) (Y₂ / (N b₂ : ℝ)) 1 1 l₁ l₂ := by
  unfold wholeCoefficient
  rw [stageRectangle_extract, wholeIndex_extract, coefficient_mul]
  simp only [one_mul]
  ring

theorem wholeCoefficient_freeze_slot [DecidableEq ι] (centered : Bool)
    (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (slots : Finset ι)
    (a : ι → ℂ) (p : ι → M) (i : ι) (hi : i ∈ slots)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ l₁ l₂ : M) :
    wholeCoefficient centered d N t slots a p W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ =
      (a i * coefficient d N t (p i)) *
        wholeCoefficient centered d N t (slots.erase i) a p W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ l₁ l₂ := by
  have hp : (∏ j ∈ slots, p j) = p i * ∏ j ∈ slots.erase i, p j := by
    simpa only [mul_comm] using (Finset.prod_erase_mul slots p hi).symm
  have ha : (∏ j ∈ slots, a j) = a i * ∏ j ∈ slots.erase i, a j := by
    simpa only [mul_comm] using (Finset.prod_erase_mul slots a hi).symm
  simp only [wholeCoefficient, wholeIndex, hp, ha, mul_assoc, coefficient_mul]
  ring

/-- Any finite transform preserves the subtraction as a whole complex coefficient. -/
theorem finite_transform_centered {α : Type*} (s : Finset α) (kernel f g : α → ℂ) :
    (∑ i ∈ s, kernel i * (f i - g i)) =
      (∑ i ∈ s, kernel i * f i) - ∑ i ∈ s, kernel i * g i := by
  simp only [mul_sub, Finset.sum_sub_distrib]

end Coefficients

section DivisorAllocation

variable {ι M : Type*} [CommMonoidWithZero M]

def divisibilityIndicator (p a : M) : ℂ := if p ∣ a then 1 else 0

theorem product_divisibility_indicators (s : Finset ι) (p : M) (a : ι → M) :
    (∏ i ∈ s, divisibilityIndicator p (a i)) =
      if ∀ i ∈ s, p ∣ a i then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ih]
      by_cases hpi : p ∣ a i <;> by_cases hps : ∀ j ∈ s, p ∣ a j <;>
        simp [divisibilityIndicator, hpi, hps]

/-- The residual divisibility condition is allocated among every occurrence. -/
theorem divisor_allocation (slots : Finset ι) (p : M) (hp : Prime p) (a : ι → M) :
    divisibilityIndicator p (∏ i ∈ slots, a i) =
      ∑ J ∈ slots.powerset with J.Nonempty,
        (-1 : ℂ) ^ (J.card + 1) * ∏ i ∈ J, divisibilityIndicator p (a i) := by
  classical
  have h := Finset.indicator_biUnion_eq_sum_powerset slots
    (fun i => { _u : Unit | p ∣ a i }) (fun _ => (1 : ℂ)) ()
  simp only [Set.indicator, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop,
    Set.mem_iInter, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  simp_rw [product_divisibility_indicators]
  simpa only [divisibilityIndicator, hp.dvd_finsetProd_iff] using h

/-- Inclusion-exclusion multiplies the full coefficient, so its common mask and
the centered difference are not split into independently estimated pieces. -/
theorem divisor_allocation_whole (slots : Finset ι) (p : M) (hp : Prime p)
    (a : ι → M) (C : ℂ) :
    C * divisibilityIndicator p (∏ i ∈ slots, a i) =
      ∑ J ∈ slots.powerset with J.Nonempty,
        ((-1 : ℂ) ^ (J.card + 1) * ∏ i ∈ J, divisibilityIndicator p (a i)) * C := by
  rw [divisor_allocation slots p hp a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

/-- A live prime slot cannot be selected by two distinct divisor primes. -/
theorem prime_slot_double_selection_zero [IsCancelMulZero M]
    (p q r : M) (hp : Prime p) (hq : Prime q) (hr : Prime r)
    (hpq : ¬Associated p q) :
    divisibilityIndicator p r * divisibilityIndicator q r = 0 := by
  by_cases hpr : p ∣ r
  · have hqr : ¬q ∣ r := by
      intro hqr
      exact hpq ((hp.associated_of_dvd hr hpr).trans (hq.associated_of_dvd hr hqr).symm)
    simp [divisibilityIndicator, hqr]
  · simp [divisibilityIndicator, hpr]

end DivisorAllocation

section Correlation

open HeckePort.Moments

variable {A : Type*} [CommRing A]

/-- The full residue correlation is retained under arbitrary whole coefficients.
No primitive-conductor replacement or absolute value occurs in this identity. -/
theorem full_correlation_weighted_fourier (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive)
    (frequencies : Finset A) (C : A → ℂ) :
    (∑ j ∈ frequencies, C j *
      ∑ h : A ⧸ Ideal.span {u * v},
        fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
          star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
            ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) *
        ∑ j ∈ frequencies, C j * fullModulusCorrelation u v χu χv j := by
  simp_rw [fullModulusCorrelation_fourier u v χu χv _ ψ hψ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Frequency filtering is justified by the complete common divisor. -/
theorem full_correlation_common_support (u v d : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hdu : d ∣ u) (hdv : d ∣ v) (frequencies : Finset A) (C : A → ℂ) :
    (∑ j ∈ frequencies, C j * fullModulusCorrelation u v χu χv j) =
      ∑ j ∈ frequencies with d ∣ j, C j * fullModulusCorrelation u v χu χv j := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hdj : d ∣ j
  · simp [hdj]
  · simp [hdj, fullModulusCorrelation_eq_zero_of_common_not_dvd u v d j χu χv hdu hdv hdj]

/-- The zero-frequency diagonal is the full Euler factor. -/
theorem full_correlation_diagonal [IsDomain A] (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) (C : ℂ) :
    C * fullModulusCorrelation u u χ χ 0 =
      C * (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  rw [fullModulusCorrelation_zero_frequency_diagonal u hu χ]

end Correlation

end HeckeSkeleton.Moments.EngineStep
