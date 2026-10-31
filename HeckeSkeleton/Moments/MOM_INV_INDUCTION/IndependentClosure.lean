import HeckeSkeleton.Moments.MOM_INV_INDUCTION.BoundedScale

/-!
# The complete independent row ball at every scale

The canonical argument is an eventual estimate in the base U.  The
bounded interval is supplied here by the literal polynomial count from
`BoundedScale`, including all sectors and all independent parameters.
The constants and height degree precede U, D and the parameter index.

The full row ball is retained through the gluing.  Its sixth-power-free
subsum is then an immediate consequence, while the complete estimate
remains available to the independent amplification consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K} {ι σ : Type*} [Fintype σ]

/-- A strict independent column length is at most the row scale itself.
This also includes U=1, where D=1 follows from the hypotheses. -/
theorem independent_column_le_row {a U D : ℝ} (ha : 0 < a)
    (hU : 1 ≤ U) (hcap : D ≤ U ^ (1 / (1 + a))) : D ≤ U := by
  have hden : 0 < 1 + a := by linarith
  have hr : 1 / (1 + a) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  exact hcap.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hU hr)

/-- The compact interval is controlled from the actual supports and
the pointwise profile bound, uniformly over all independent parameters.
No arithmetic row calibration or moment estimate is used on this range. -/
theorem exists_bounded_complete_sector_inverse_bound
    (source : ℝ → ℝ → ι → σ → MomentData K ω ψ)
    (H : ι → ℝ) (Eligible : ℝ → ℝ → ι → Prop)
    (R b C₀ A₀ : ℝ) (hR : 1 ≤ R) (hb : 1 ≤ b) (hC₀ : 0 ≤ C₀)
    (hH : ∀ i, 1 ≤ H i)
    (hsupport : ∀ U D i, 1 ≤ U → U ≤ R → 1 ≤ D → D ≤ R → Eligible U D i →
      ∀ s u I, I ∈ (source U D i s).inverseTest.support u 0 D →
        idealNorm K I / D ≤ b)
    (hprofile : ∀ U D i, 1 ≤ U → U ≤ R → 1 ≤ D → D ≤ R → Eligible U D i →
      ∀ s u I, I ∈ (source U D i s).inverseTest.support u 0 D →
        ‖(source U D i s).inverseTest.profile u 0 (idealNorm K I / D)‖ ≤
          C₀ * H i ^ A₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ U D i,
      1 ≤ U → U ≤ R → 1 ≤ D → D ≤ R → Eligible U D i →
        (∑ s, completeIndependentInverseEnergy (source U D i s) U D) ≤
          C * H i ^ (2 * A₀) := by
  obtain ⟨B, hB, hbnd⟩ := exists_bounded_complete_scale_inverse_bound (K := K) R b hR hb
  let C := ((Fintype.card σ : ℝ) + 1) * B * (C₀ ^ 2 + 1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro U D i hU hUR hD hDR hi
  have hH0 : 0 ≤ H i := zero_le_one.trans (hH i)
  have hpow0 : 0 ≤ H i ^ (2 * A₀) := Real.rpow_nonneg hH0 _
  have hheight : (H i ^ A₀) ^ 2 = H i ^ (2 * A₀) := by
    rw [mul_comm (2 : ℝ) A₀, Real.rpow_mul_natCast hH0 A₀ 2]
  have hpoint (s : σ) :
      completeIndependentInverseEnergy (source U D i s) U D ≤
        (B * (C₀ ^ 2 + 1)) * H i ^ (2 * A₀) := by
    have hp := hbnd (source U D i s) U D (C₀ * H i ^ A₀)
      hU hUR hD hDR (mul_nonneg hC₀ (Real.rpow_nonneg hH0 _))
      (hsupport U D i hU hUR hD hDR hi s)
      (hprofile U D i hU hUR hD hDR hi s)
    apply hp.trans
    rw [mul_pow, hheight]
    calc
      _ = (B * C₀ ^ 2) * H i ^ (2 * A₀) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hB.le) hpow0
  calc
    _ ≤ ∑ _s : σ, (B * (C₀ ^ 2 + 1)) * H i ^ (2 * A₀) :=
      Finset.sum_le_sum fun s _ => hpoint s
    _ = (Fintype.card σ : ℝ) * ((B * (C₀ ^ 2 + 1)) * H i ^ (2 * A₀)) := by simp
    _ ≤ ((Fintype.card σ : ℝ) + 1) *
        ((B * (C₀ ^ 2 + 1)) * H i ^ (2 * A₀)) :=
      mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg (mul_nonneg hB.le (by positivity)) hpow0)
    _ = C * H i ^ (2 * A₀) := by dsimp only [C]; ring

/-- Combine a proved eventual canonical estimate with the separately
derived compact-range bound. The same finite sector family and literal
polynomials occur on both ranges; no per-scale constants are chosen. -/
theorem complete_independent_bound_all_scales
    (source : ℝ → ℝ → ι → σ → MomentData K ω ψ)
    (H : ι → ℝ) (Eligible : ℝ → ℝ → ι → Prop)
    (a eps U₀ b C₀ A₀ C₁ A₁ : ℝ)
    (ha : 0 < a) (heps : 0 < eps) (hb : 1 ≤ b)
    (hC₀ : 0 ≤ C₀) (hA₀ : 0 ≤ A₀) (hC₁ : 0 ≤ C₁)
    (hH : ∀ i, 1 ≤ H i)
    (hsupport : ∀ U D i, 1 ≤ U → U ≤ max 1 U₀ →
      1 ≤ D → D ≤ max 1 U₀ → Eligible U D i →
      ∀ s u I, I ∈ (source U D i s).inverseTest.support u 0 D →
        idealNorm K I / D ≤ b)
    (hprofile : ∀ U D i, 1 ≤ U → U ≤ max 1 U₀ →
      1 ≤ D → D ≤ max 1 U₀ → Eligible U D i →
      ∀ s u I, I ∈ (source U D i s).inverseTest.support u 0 D →
        ‖(source U D i s).inverseTest.profile u 0 (idealNorm K I / D)‖ ≤
          C₀ * H i ^ A₀)
    (hlarge : ∀ U D i, 1 ≤ U → U₀ ≤ U → 1 ≤ D →
      D ≤ U ^ (1 / (1 + a)) → Eligible U D i →
        (∑ s, completeIndependentInverseEnergy (source U D i s) U D) ≤
          C₁ * U ^ (1 + eps) * H i ^ A₁) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ U D i,
      1 ≤ U → 1 ≤ D → D ≤ U ^ (1 / (1 + a)) → Eligible U D i →
        (∑ s, completeIndependentInverseEnergy (source U D i s) U D) ≤
          C * U ^ (1 + eps) * H i ^ A := by
  obtain ⟨B, hB, hsmall⟩ := exists_bounded_complete_sector_inverse_bound source H Eligible
    (max 1 U₀) b C₀ A₀ (le_max_left _ _) hb hC₀ hH hsupport hprofile
  let C := B + C₁ + 1
  let A := max (2 * A₀) A₁
  have hC : 0 < C := by dsimp only [C]; linarith
  have hBC : B ≤ C := by dsimp only [C]; linarith
  have hC₁C : C₁ ≤ C := by dsimp only [C]; linarith
  have hA : 0 ≤ A := (mul_nonneg (by norm_num) hA₀).trans (le_max_left _ _)
  refine ⟨C, A, hC, hA, ?_⟩
  intro U D i hU hD hcap hi
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hH0 : 0 ≤ H i := zero_le_one.trans (hH i)
  have hUpow : 1 ≤ U ^ (1 + eps) := Real.one_le_rpow hU (by linarith)
  have hHpow0 : 0 ≤ H i ^ A := Real.rpow_nonneg hH0 _
  by_cases hbig : U₀ ≤ U
  · have hheight : H i ^ A₁ ≤ H i ^ A :=
      Real.rpow_le_rpow_of_exponent_le (hH i) (le_max_right _ _)
    exact (hlarge U D i hU hbig hD hcap hi).trans
      (mul_le_mul (mul_le_mul_of_nonneg_right hC₁C (Real.rpow_nonneg hU0 _))
        hheight (Real.rpow_nonneg hH0 _)
        (mul_nonneg hC.le (Real.rpow_nonneg hU0 _)))
  · have hUR : U ≤ max 1 U₀ := (le_of_lt (lt_of_not_ge hbig)).trans (le_max_right _ _)
    have hDR : D ≤ max 1 U₀ := (independent_column_le_row ha hU hcap).trans hUR
    have hheight : H i ^ (2 * A₀) ≤ H i ^ A :=
      Real.rpow_le_rpow_of_exponent_le (hH i) (le_max_left _ _)
    calc
      _ ≤ B * H i ^ (2 * A₀) := hsmall U D i hU hUR hD hDR hi
      _ ≤ C * H i ^ A := mul_le_mul hBC hheight (Real.rpow_nonneg hH0 _) hC.le
      _ ≤ C * U ^ (1 + eps) * H i ^ A :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le hUpow) hHpow0

/-- Preserve the full-row estimate for amplification and obtain the
skeleton's sixth-free specialization by a positive subsum. -/
theorem independent_sector_energy_le_complete
    (source : σ → MomentData K ω ψ) (U D : ℝ) :
    (∑ s, independentInverseEnergy (source s) U D) ≤
      ∑ s, completeIndependentInverseEnergy (source s) U D :=
  Finset.sum_le_sum fun s _ => independentInverseEnergy_le_complete (source s) U D

end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
