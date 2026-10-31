import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.NormalizedReflectionDensity

/-!
# Select the common annulus before the backward derivative orders

The original source provides all finite Euler orders, with a possibly
different reported annulus at each order. Its order-zero instance fixes
an annulus once. Every higher-order estimate can use that same support
fact, so the analytic order functions may subsequently depend on its
endpoints without a circular choice of the maximal derivative order.

The upper endpoint is enlarged to include the fixed reflected windows;
the lower endpoint is decreased to include them. The literal original
models and all original indices are unchanged.
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

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- The common annulus is chosen before every Euler order. This permits
the actual finite backward order schedule to depend on its endpoints. -/
theorem recipeRoot_fixed_annulus_profiles {lengthBound : ℝ}
    (hgeom : R.MomentGeometry lengthBound)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ 2 ≤ b ∧ a < b ∧
      ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
        ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
          ∀ Z T (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
            (s : SixthUnitClasses K (places K c)),
            ModelProfileControl (recipeRoot R i s).data J A C H a b T := by
  have hall := recipeRoot_uniform_profiles R hgeom hprofiles
  obtain ⟨C0, H0, a0, b0, _hC0, _hH0, ha0, hab0, hzero⟩ :=
    hall 0 0 (le_refl (0 : ℝ))
  let a := min a0 (1 / 2)
  let b := max b0 2
  have ha : 0 < a := lt_min ha0 (by norm_num)
  have hab : a < b :=
    (min_le_left a0 (1 / 2)).trans_lt (hab0.trans_le (le_max_left b0 2))
  refine ⟨a, b, ha, min_le_right _ _, le_max_right _ _, hab, ?_⟩
  intro J A hA
  obtain ⟨C, H, _a, _b, hC, hH, _ha, _hab, horder⟩ := hall J A hA
  refine ⟨C, H, hC, hH, ?_⟩
  intro Z T i s q
  have hsupport := (hzero Z T i s q).2.1
  have hcurrent := horder Z T i s q
  exact ⟨hcurrent.1, fun y hy =>
    ⟨(min_le_left _ _).trans (hsupport y hy).1,
      (hsupport y hy).2.trans (le_max_left _ _)⟩, hcurrent.2.2⟩

end Source

end HeckeSkeleton.Moments.EngineInduction
