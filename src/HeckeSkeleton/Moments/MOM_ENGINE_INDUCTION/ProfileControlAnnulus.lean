import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.NormalizedReflectionDensity

/-!
# Annular profile budgets independent of a source dictionary

The literal slice supplies its own smooth annular test. Enlarging a
numerical budget or lowering its weight preserves the original profile
functions and their actual support. These generic comparisons are used
by both source preparation and finite Schwartz order conversion.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The actual slice, with its proved common support, is an annular test. -/
def sliceControlAnnularTest {f : ℝ → ℂ} {J : ℕ} {A C H a b T : ℝ}
    (h : SliceControl J A C H a b T f) (ha : 0 < a) (hab : a ≤ b) :
    SmoothAnnularTest where
  toFun := f
  smooth := h.1
  lower := a
  upper := b
  lower_pos := ha
  upper_ge := hab
  support := fun _ hy => h.2.1 _ hy

/-- A numerical parent budget at least its original height envelope
does not change the original model or any profile. -/
theorem modelProfileControl_fixed_budget {d : MomentData K ω ψ}
    {J : ℕ} {A C H a b T P : ℝ}
    (h : ModelProfileControl d J A C H a b T) (hP : C * (1 + T) ^ H ≤ P) :
    ModelProfileControl d J A P 0 a b 0 := by
  intro q
  exact ⟨(h q).1, (h q).2.1, by
    simpa only [Real.rpow_zero, mul_one] using (h q).2.2.trans hP⟩

/-- The common A-weighted seminorm supplies the order-zero weight used
by the absolute short-factor and slot estimates, with explicit factor two. -/
theorem modelProfileControl_weight_zero {d : MomentData K ω ψ}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    ModelProfileControl d J 0 (2 * C) H a b T := by
  intro q
  refine ⟨(h q).1, (h q).2.1, ?_⟩
  let V := sliceControlAnnularTest (h q) ha hab
  have hs := smoothAnnular_testSeminorm_weight_le V J (le_refl (0 : ℝ)) hA
  calc
    _ ≤ 2 * testSeminorm (modelProfile d q) J A := hs
    _ ≤ 2 * (C * (1 + T) ^ H) :=
      mul_le_mul_of_nonneg_left (h q).2.2 (by norm_num)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineInduction
