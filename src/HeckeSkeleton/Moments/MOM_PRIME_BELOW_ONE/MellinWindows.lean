module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite Schwartz seminorms for the frozen physical Mellin power

A fixed Schwartz weight supported in the prime annulus can be multiplied
by the already constructed Mellin test.  Its cutoff is identically one
there, so the result is the original norm power.  Continuity of fixed
Schwartz multiplication transfers every finite family of seminorms to the
proved polynomial-frequency bound for the Mellin test.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.MellinWindow

open HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
open scoped Classical BigOperators ContDiff SchwartzMap ComplexConjugate

/-- The Mellin cutoff is one on the original prime annulus. -/
def frozen (W : SchwartzMap ℝ ℂ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ W
    (weightedTest (-(33 / 50 : ℝ)) (-t / (2 * Real.pi)))

theorem frozen_apply (W : SchwartzMap ℝ ℂ)
    (hW : Function.support (W : ℝ → ℂ) ⊆ Set.Ioo (1 : ℝ) 2) (t y : ℝ) :
    frozen W t y = W y *
      Complex.exp ((Real.log y : ℂ) *
        (conj ((17 / 50 : ℂ) + (t : ℂ) * Complex.I) - 1)) := by
  rw [frozen, SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  change W y * weightedTest _ _ y = _
  by_cases hw : W y = 0
  · simp only [hw, zero_mul]
  · have hy := hW hw
    rw [weightedTest_eq, cutoff_one (by linarith [hy.1]) (by linarith [hy.2]), one_mul,
      columnPhase_eq_exp, Real.rpow_def_of_pos (zero_lt_one.trans hy.1)]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    simp only [map_add, map_div₀, map_ofNat, Complex.conj_I, map_mul, Complex.conj_ofReal]
    field_simp [hpi]
    <;> ring

theorem frozen_support (W : SchwartzMap ℝ ℂ)
    (hW : Function.support (W : ℝ → ℂ) ⊆ Set.Ioo (1 : ℝ) 2) (t : ℝ) :
    Function.support (frozen W t : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2 := by
  intro y hy
  have hw : W y ≠ 0 := by
    intro hw
    exact hy (by rw [frozen_apply W hW, hw, zero_mul])
  exact (hW hw).imp le_of_lt le_of_lt

/-- A fixed original weight acts continuously on Schwartz space. -/
theorem weight_finite_seminorm_bound (W : SchwartzMap ℝ ℂ)
    (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ V : SchwartzMap ℝ ℂ,
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (SchwartzMap.smulLeftCLM ℂ W V) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) V := by
  let L := (SchwartzMap.smulLeftCLM ℂ W).restrictScalars ℝ
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp L.toLinearMap
  have ht : Continuous (fun V : SchwartzMap ℝ ℂ =>
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (ht.comp L.continuous)
  exact ⟨s, C, C.property, fun V => Seminorm.le_def.mp hb V⟩

theorem frozen_finite_seminorm_bound (W : SchwartzMap ℝ ℂ)
    (s : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frozen W t) ≤ C * (1 + |t|) ^ m := by
  obtain ⟨v, C₀, hC₀, hweight⟩ := weight_finite_seminorm_bound W s
  obtain ⟨m, C₁, hC₁, htwist⟩ := finite_seminorm_polynomial_bound (-(33 / 50 : ℝ)) v
  refine ⟨m, C₀ * C₁, mul_nonneg hC₀ hC₁, ?_⟩
  intro t
  have hden : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ht : |-t / (2 * Real.pi)| ≤ |t| := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact div_le_self (abs_nonneg t) hden
  calc
    _ ≤ C₀ * v.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (weightedTest (-(33 / 50 : ℝ)) (-t / (2 * Real.pi))) := hweight _
    _ ≤ C₀ * (C₁ * (1 + |-t / (2 * Real.pi)|) ^ m) :=
      mul_le_mul_of_nonneg_left (htwist _) hC₀
    _ ≤ (C₀ * C₁) * (1 + |t|) ^ m := by
      rw [← mul_assoc]
      gcongr

/-- The finite maximum precedes every selected slot and physical height. -/
theorem frozen_uniform_seminorm_bound {ι : Type*} [Fintype ι]
    (W : ι → SchwartzMap ℝ ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (j : ι) (t : ℝ),
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frozen (W j) t) ≤ C * (1 + |t|) ^ m := by
  choose m C hC hb using fun j : ι => frozen_finite_seminorm_bound (W j) s
  let A := Finset.univ.sup m
  let B := 1 + ∑ j : ι, C j
  have hsum : 0 ≤ ∑ j : ι, C j := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨A, B, by dsimp [B]; linarith, ?_⟩
  intro j t
  have hj : C j ≤ B := by
    have := Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
    dsimp [B]
    linarith
  exact (hb j t).trans (mul_le_mul hj
    (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg t))
      (Finset.le_sup (Finset.mem_univ j))) (by positivity) (by dsimp [B]; linarith))

end HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.MellinWindow

#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.MellinWindow.frozen_apply
#print axioms HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.MellinWindow.frozen_uniform_seminorm_bound

end
