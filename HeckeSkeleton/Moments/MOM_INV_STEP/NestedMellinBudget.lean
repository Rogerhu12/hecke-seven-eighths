module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
public import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveIntervalMellin

/-!
# Uniform cost of the two actual Mellin separations

The first inversion produces a fixed wide cutoff with a frequency
modulation. The second inversion acts on its genuine negative half
power, preserving its support. All second Mellin moments, including the
product introduced by Cauchy, have polynomial cost in the first
frequency. Integrating that cost against the original Mellin density
uses only finitely many original Schwartz seminorms. No arithmetic
parameter occurs in the chosen constants.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.NestedMellinBudget

open MeasureTheory
open scoped Classical

/-- The actual column test entering the second Mellin inversion. -/
def secondTest (a t : ℝ) : SchwartzMap ℝ ℂ :=
  FinalMellinTests.powerTest (WideMellinTests.weightedTest a t) (-1 / 2)

theorem secondTest_support (a t : ℝ) :
    tsupport (secondTest a t) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) :=
  (FinalMellinTests.powerTest_support _ _).trans
    (WideMellinTests.weightedTest_support a t)

def secondDensity (a t : ℝ) : SchwartzMap ℝ ℂ :=
  PositiveIntervalMellin.density (1 / 8) (21 / 8) (by norm_num) (by norm_num)
    (secondTest a t) (secondTest_support a t)

def moment (a t : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ, (1 + |u|) ^ k * ‖secondDensity a t u‖

theorem moment_nonneg (a t : ℝ) (k : ℕ) : 0 ≤ moment a t k :=
  integral_nonneg (fun _ => by positivity)

theorem moment_integrable (a t : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => (1 + |u|) ^ k * ‖secondDensity a t u‖) :=
  PositiveIntervalMellin.density_moment_integrable _ _ _ _ _ _ k

/-- A prescribed second Mellin moment costs a polynomial of the two
first frequencies. Constants precede both frequencies. -/
theorem moment_bound (a : ℝ) (k : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t τ : ℝ,
      moment a (t + τ) k ≤ C * (1 + |t|) ^ m * (1 + |τ|) ^ m := by
  obtain ⟨s, C₀, hC₀, hb₀⟩ :=
    PositiveIntervalMellin.density_moment_bound
      (1 / 8) (21 / 8) (by norm_num) (by norm_num) k
  obtain ⟨s', C₁, hC₁, hb₁⟩ :=
    FinalMellinTests.powerTest_finite_seminorm_bound (-1 / 2) s
  obtain ⟨m, C₂, hC₂, hb₂⟩ :=
    WideMellinTests.combined_frequency_seminorm_bound a s'
  refine ⟨m, C₀ * C₁ * C₂, by positivity, fun t τ => ?_⟩
  have h₀ := hb₀ (secondTest a (t + τ)) (secondTest_support a (t + τ))
  have h₁ := hb₁ (WideMellinTests.weightedTest a (t + τ))
  have h₂ := hb₂ t τ
  calc
    moment a (t + τ) k ≤ C₀ * s.sup
        (schwartzSeminormFamily ℝ ℝ ℂ) (secondTest a (t + τ)) := h₀
    _ ≤ C₀ * (C₁ * s'.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (WideMellinTests.weightedTest a (t + τ))) :=
      mul_le_mul_of_nonneg_left h₁ hC₀
    _ ≤ C₀ * (C₁ * (C₂ * (1 + |t|) ^ m * (1 + |τ|) ^ m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₂ hC₁) hC₀
    _ = _ := by ring

/-- The exact Mellin mass and moment product charged by weighted Cauchy. -/
def cauchyCost (a t : ℝ) (k : ℕ) : ℝ :=
  moment a t 0 * moment a t k

theorem cauchyCost_nonneg (a t : ℝ) (k : ℕ) : 0 ≤ cauchyCost a t k :=
  mul_nonneg (moment_nonneg a t 0) (moment_nonneg a t k)

theorem cauchyCost_bound (a : ℝ) (k : ℕ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t τ : ℝ,
      cauchyCost a (t + τ) k ≤ C * (1 + |t|) ^ m * (1 + |τ|) ^ m := by
  obtain ⟨m₀, C₀, hC₀, hb₀⟩ := moment_bound a 0
  obtain ⟨m₁, C₁, hC₁, hb₁⟩ := moment_bound a k
  refine ⟨m₀ + m₁, C₀ * C₁, mul_nonneg hC₀ hC₁, fun t τ => ?_⟩
  have hb := mul_le_mul (hb₀ t τ) (hb₁ t τ)
    (moment_nonneg a (t + τ) k) (by positivity)
  exact hb.trans_eq (by rw [pow_add, pow_add]; ring)

/-- Any polynomial cost of the first frequency is absorbed by a
finite original-test seminorm, uniformly in the remaining Fourier
frequency. The integrability premise is needed only for the actual
Mellin density, which is already proved. -/
theorem outer_polynomial_bound (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (τ : ℝ) (B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℝ),
      (∀ t, 0 ≤ f t) →
      (∀ t, f t ≤ B * (1 + |t|) ^ m * (1 + |τ|) ^ m) →
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * f t) ≤
        C * B * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1 + |τ|) ^ m := by
  obtain ⟨s, C, hC, hb⟩ := MellinSeparation.density_moment_bound m
  refine ⟨s, C, hC, fun W hW τ B hB f hf hfB => ?_⟩
  have hi := (MellinSeparation.density_moment_integrable W hW m).const_mul
    (B * (1 + |τ|) ^ m)
  calc
    _ ≤ ∫ t : ℝ, (B * (1 + |τ|) ^ m) *
        ((1 + |t|) ^ m * ‖MellinSeparation.density W hW t‖) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (hf t))) hi
      exact Filter.Eventually.of_forall fun t =>
        (mul_le_mul_of_nonneg_left (hfB t) (norm_nonneg _)).trans_eq (by ring)
    _ = (B * (1 + |τ|) ^ m) *
        (∫ t : ℝ, (1 + |t|) ^ m * ‖MellinSeparation.density W hW t‖) :=
      integral_const_mul _ _
    _ ≤ (B * (1 + |τ|) ^ m) *
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hW) (by positivity)
    _ = _ := by ring

/-- After the second Cauchy inequality, the whole nested Mellin cost
still uses only a fixed finite seminorm of the original column test. -/
theorem outer_cauchyCost_bound (a : ℝ) (k : ℕ) :
    ∃ m : ℕ, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (τ : ℝ),
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + τ) k) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1 + |τ|) ^ m := by
  obtain ⟨m, B, hB, hb⟩ := cauchyCost_bound a k
  obtain ⟨s, C, hC, hc⟩ := outer_polynomial_bound m
  exact ⟨m, s, C * B, mul_nonneg hC hB, fun W hW τ =>
    hc W hW τ B hB (fun t => cauchyCost a (t + τ) k)
      (fun t => cauchyCost_nonneg a (t + τ) k) (fun t => hb t τ)⟩

/-- The first Cauchy mass is charged once, giving the expected quadratic
seminorm bound on the original column test. -/
theorem two_pass_cauchyCost_bound (a : ℝ) (k : ℕ) :
    ∃ m : ℕ, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (τ : ℝ),
      (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) *
        (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + τ) k) ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * (1 + |τ|) ^ m := by
  obtain ⟨s₀, C₀, hC₀, hb₀⟩ := MellinSeparation.density_moment_bound 0
  obtain ⟨m, s₁, C₁, hC₁, hb₁⟩ := outer_cauchyCost_bound a k
  refine ⟨m, s₀ ∪ s₁, C₀ * C₁, mul_nonneg hC₀ hC₁, fun W hW τ => ?_⟩
  have h₀ : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) ≤
      C₀ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    have hm₀ : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖) ≤
        C₀ * s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using hb₀ W hW
    exact hm₀.trans
      (mul_le_mul_of_nonneg_left
        (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) hC₀)
  have h₁ : (∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + τ) k) ≤
      C₁ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1 + |τ|) ^ m :=
    (hb₁ W hW τ).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) hC₁)
      (by positivity))
  have hn : 0 ≤ ∫ t : ℝ, ‖MellinSeparation.density W hW t‖ * cauchyCost a (t + τ) k :=
    integral_nonneg (fun t => mul_nonneg (norm_nonneg _) (cauchyCost_nonneg _ _ _))
  exact (mul_le_mul h₀ h₁ hn (by positivity)).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.NestedMellinBudget

end

