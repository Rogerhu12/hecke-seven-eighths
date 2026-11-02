import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteRowAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot

/-!
# Actual orbital atoms of the literal source recipe root

The actual complete source recipe at ec60 and canonical atom interface
at fd6 supply every field without any new calibration premise. The
original complete ideal, unit sector, fixed backgrounds and selected
slot coefficients are retained. The initial remaining ideal is one,
including in the unrestricted no-slot projection.

These are actual arithmetic atoms. A positive orbital chart and its
individual periodic-column identities are separate source constructions.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

/-- Every original arithmetic atom of the literal root, with no new
phase, coefficient, finite-order or moment hypothesis. Slot selection
and change of base preserve all fields used by this constructor. -/
def recipeRootArithmeticAtoms
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (sector : SixthUnitClasses K (places K c)) :
    EngineStep.ParentArithmeticAtoms (ActualSIntegerOrbit K (places K c))
      (recipeRoot R i sector).data :=
  completeIdealArithmeticAtoms (places K c) (probeData K c) (momentRowCharacters K c)
    (fun _ => sector) (recipeRoot R i sector).data 1 (fun _ hu => hu) (fun _ _ => rfl)
    (by
      intro u I
      change completeIdealCommonMask K (places K c) u I =
        (completeIdealCommonMask K (places K c) u I &&
          decide (IsCoprime I (1 : Ideal (𝓞 K))))
      simp only [isCoprime_one_right, decide_true, Bool.and_true])

end HeckeSkeleton.Moments.EngineInduction.Source
