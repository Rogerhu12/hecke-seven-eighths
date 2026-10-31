import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FixedLineKernel
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionGeometry

/-!
# Pay the complete finite reflection mass from a preassigned loss

The actual dyadic cutoff is at most a fixed power of the original base.
Its complete branch count is therefore logarithmic. The square paid by
the two Cauchy steps is absorbed by any preassigned positive loss. This
does not change the cutoff, remove branches, or move a row supremum
through an integral.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open MeasureTheory
open scoped BigOperators Classical

/-- The actual finite cutoff gives a uniform logarithmic branch count. -/
theorem reflection_dyadic_count_le_log {U B : ℝ} {cutoff : ℕ}
    (hU : 1 < U) (hB : 0 ≤ B) (hcutoff : (2 : ℝ) ^ cutoff ≤ U ^ B) :
    ((cutoff + 1 : ℕ) : ℝ) ≤ (1 + B / Real.log 2) * (1 + Real.log U) := by
  have hlog : 0 < Real.log U := Real.log_pos hU
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlength := reflectionDyadicExponent_le hU hcutoff (le_refl cutoff)
  have hscaled := (div_le_iff₀ hlog).mp hlength
  simp only [reflectionDyadicExponent, Real.log_pow] at hscaled
  have hcount : (cutoff : ℝ) ≤ (B / Real.log 2) * Real.log U := by
    calc
      _ ≤ (B * Real.log U) / Real.log 2 := (le_div_iff₀ hlog2).mpr hscaled
      _ = _ := by ring
  have hratio : 0 ≤ B / Real.log 2 := div_nonneg hB hlog2.le
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The finite branch factor uses a constant chosen before the scale,
node and actual cutoff. -/
theorem reflection_dyadic_count_subpower {B loss : ℝ}
    (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 < U → ∀ cutoff : ℕ,
      (2 : ℝ) ^ cutoff ≤ U ^ B →
      ((cutoff + 1 : ℕ) : ℝ) ^ 2 ≤ C * U ^ loss := by
  let delta := loss / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := (1 + B / Real.log 2) * (1 + 1 / delta)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ 2, pow_pos hA _, ?_⟩
  intro U hU cutoff hcutoff
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlog : 1 + Real.log U ≤ (1 + 1 / delta) * U ^ delta := by
    have hp := Real.one_le_rpow hU.le hd.le
    have hl := Real.log_le_rpow_div hU0.le hd
    calc
      _ ≤ U ^ delta + U ^ delta / delta := add_le_add hp hl
      _ = _ := by ring
  have hcount : ((cutoff + 1 : ℕ) : ℝ) ≤ A * U ^ delta := by
    apply (reflection_dyadic_count_le_log hU hB hcutoff).trans
    convert mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 1 + B / Real.log 2 by positivity) using 1 <;> dsimp [A] <;> ring
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (cutoff + 1)) hcount 2
  have he : (U ^ delta) ^ 2 = U ^ loss := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    congr 1
    dsimp [delta]
    ring
  simpa only [mul_pow, he] using hs

universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- Complete mass of the actual common reflection kernel, after charging
the finite dyadic/line factor to a preassigned positive loss. -/
theorem reflectionCommonKernel_mass_subpower {B loss : ℝ}
    (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) (weight : Ω → ℝ),
      Measurable weight → (∀ ξ, 0 ≤ weight ξ) → Integrable weight μ →
      ∀ U : ℝ, 1 < U → ∀ cutoff : ℕ, (2 : ℝ) ^ cutoff ≤ U ^ B →
      (reflectionCommonKernel μ weight cutoff).real Set.univ ≤
        C * U ^ loss * (∫ ξ, weight ξ ∂μ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := reflection_dyadic_count_subpower hB hloss
  refine ⟨8 * C, by positivity, ?_⟩
  intro μ weight hm hw hi U hU cutoff hcutoff
  rw [reflectionCommonKernel_mass μ weight cutoff hm hw hi]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbound U hU cutoff hcutoff) (by norm_num : (0 : ℝ) ≤ 8))
    (sq_nonneg (∫ ξ, weight ξ ∂μ))
  simpa only [mul_assoc] using h

end HeckeSkeleton.Moments.EngineInduction
