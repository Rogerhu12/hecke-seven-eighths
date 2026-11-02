import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileControlAnnulus

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
