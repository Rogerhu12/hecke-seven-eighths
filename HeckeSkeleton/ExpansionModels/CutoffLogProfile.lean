import HeckeSkeleton.ExpansionModels.LogProfileFourier

/-!
# The actual smooth one-sided cutoff in the uniform Fourier theorem

The detector cutoff is one on the whole negative half-line and therefore is
not itself a Schwartz function.  The symmetric extension below agrees with
it on every nonnegative input.  All scaled exponential inputs are
nonnegative, so this extension proves the Fourier estimates for the original
profile, with no alteration to its definition or values.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe.LogProfile

open MeasureTheory
open scoped Classical ContDiff FourierTransform

def cutoffSchwartzFun (V : ℝ → ℂ) (x : ℝ) : ℂ := V x * V (-x)

lemma cutoffSchwartzFun_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (cutoffSchwartzFun V) :=
  hV.mul (hV.comp contDiff_id.neg)

lemma cutoffSchwartzFun_support (V : ℝ → ℂ)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) :
    Function.support (cutoffSchwartzFun V) ⊆ Set.Icc (-2) 2 := by
  intro x hx
  have hleft : V x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hright : V (-x) ≠ 0 := (mul_ne_zero_iff.mp hx).2
  constructor
  · by_contra h
    exact hright (hzero (-x) (by linarith))
  · by_contra h
    exact hleft (hzero x (by linarith))

lemma cutoffSchwartzFun_tsupport (V : ℝ → ℂ)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) :
    tsupport (cutoffSchwartzFun V) ⊆ Set.Icc (-2) 2 := by
  exact closure_minimal (cutoffSchwartzFun_support V hzero) isClosed_Icc

lemma cutoffSchwartzFun_compact (V : ℝ → ℂ)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) :
    HasCompactSupport (cutoffSchwartzFun V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (cutoffSchwartzFun_support V hzero)

def cutoffSchwartz (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) : SchwartzMap ℝ ℂ :=
  (cutoffSchwartzFun_compact V hzero).toSchwartzMap (cutoffSchwartzFun_smooth V hV)

@[simp] lemma cutoffSchwartz_apply (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (x : ℝ) :
    cutoffSchwartz V hV hzero x = cutoffSchwartzFun V x := rfl

lemma cutoffSchwartzFun_eq_nonneg (V : ℝ → ℂ)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1) {x : ℝ} (hx : 0 ≤ x) :
    cutoffSchwartzFun V x = V x := by
  rw [cutoffSchwartzFun, hone (-x) (by linarith), mul_one]

lemma cutoffSchwartzFun_one (V : ℝ → ℂ)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1) {x : ℝ} (hx : |x| ≤ 1) :
    cutoffSchwartzFun V x = 1 := by
  rw [cutoffSchwartzFun, hone x (abs_le.mp hx).2,
    hone (-x) (by linarith [(abs_le.mp hx).1]), mul_one]

lemma cutoffSchwartzFun_norm_le (V : ℝ → ℂ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖cutoffSchwartzFun V x‖ ≤ 1 := by
  rw [cutoffSchwartzFun, norm_mul]
  exact (mul_le_mul (hV x) (hV (-x)) (norm_nonneg _) (by norm_num)).trans_eq
    (one_mul 1)

/-- Literal equality of Schwartz maps, not merely an almost-everywhere
replacement.  It holds at zero scales as well. -/
theorem logSource_cutoff_extension (Ω V : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (A B D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    logSource Ω V V hΩc hΩ hV hV A B D =
      logSource Ω (cutoffSchwartz V hV hzero) (cutoffSchwartz V hV hzero)
        hΩc hΩ ((cutoffSchwartz V hV hzero).smooth ⊤)
        ((cutoffSchwartz V hV hzero).smooth ⊤) A B D := by
  ext y
  change logSourceFun Ω V V A B D y =
    logSourceFun Ω (cutoffSchwartzFun V) (cutoffSchwartzFun V) A B D y
  unfold logSourceFun
  rw [cutoffSchwartzFun_eq_nonneg V hone (mul_nonneg hA (Real.exp_pos y).le),
    cutoffSchwartzFun_eq_nonneg V hone (mul_nonneg hD (Real.exp_pos y).le)]

/-- Uniform Fourier moments for the original one-sided detector cutoff.
The parameters may be arbitrarily large nonnegative real numbers. -/
theorem uniform_cutoff_fourier_moment (Ω V : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logSource Ω V V hΩc hΩ hV hV A B D)) t‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_fourier_moment Ω
    (cutoffSchwartz V hV hzero) (cutoffSchwartz V hV hzero)
    hΩc hΩ L hL hwindow J
  refine ⟨C, hC, ?_⟩
  intro A B D hA hB hD
  rw [logSource_cutoff_extension Ω V hΩc hΩ hV hone hzero A B D hA hD]
  exact hb A B D hA hB hD

/-- All polynomial tail orders for the same unchanged profile. -/
theorem uniform_cutoff_fourier_tail (Ω V : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logSource Ω V V hΩc hΩ hV hV A B D)) t‖) ≤ C / R ^ N := by
  obtain ⟨C, hC, hb⟩ := uniform_fourier_tail Ω
    (cutoffSchwartz V hV hzero) (cutoffSchwartz V hV hzero)
    hΩc hΩ L hL hwindow J N
  refine ⟨C, hC, ?_⟩
  intro A B D hA hB hD R hR
  rw [logSource_cutoff_extension Ω V hΩc hΩ hV hone hzero A B D hA hD]
  exact hb A B D hA hB hD R hR

end ExpansionRecipe.LogProfile

#print axioms ExpansionRecipe.LogProfile.logSource_cutoff_extension
#print axioms ExpansionRecipe.LogProfile.uniform_cutoff_fourier_moment
#print axioms ExpansionRecipe.LogProfile.uniform_cutoff_fourier_tail
