import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualLocalInputMeasures
import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualCatalogueVolume

/-!
# The actual source closes every primitive input of the local induction

The original target's radial normalization and finite character
catalogue give the supported single-character volume primitive on each
fixed positive box. Its remainder seminorms are chosen before all moving
profiles and scales. The actual Fourier measures and the complete strict
and reflection constructions then supply both local scalar inputs.

There is no engine, child energy, local reduction or moment bound among
the hypotheses. This is the final source specialization used by the
three original moment theorems.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project EngineStep
open scoped Classical SchwartzMap

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)

/-- The actual annular ideal-series theorem supplies the owner's
supported volume input on every fixed numerical box. -/
def actualCatalogueVolumePrimitive (b : CanonicalPrimitiveEngineChoices.Box) :
    CanonicalLiteralExceptionalPaidSource.VolumePrimitive
      (targetCharacter K c) (canonicalDetectorTheta K (targetCharacter K c))
      (Set.Icc b.lo b.hi) := by
  let h := exists_originalCatalogue_supported_volume
    (isComplex_of_family K c) (normNormalizationPlace K) (targetCharacter K c)
    (targetCharacter_radial_zero K c)
    (canonicalDetectorTheta K (targetCharacter K c))
    (canonicalDetectorTheta_finiteOrder K (targetCharacter K c))
    b.lo b.hi b.lo_pos (b.lo_le_one.trans b.hi_ge_one)
  exact {
    compact := isCompact_Icc
    positive := fun _ hy => b.lo_pos.trans_le hy.1
    density := fun i => actualAnnularDensity
      (CanonicalLiteralExceptionalCharacters.background (targetCharacter K c) i.1 * i.2.val)
    remainder := h.choose
    continuous := h.choose_spec.1
    volume := fun i phi X hX hsupport => h.choose_spec.2 i phi hsupport X hX }

/-- Both original source regimes now have their actual local scalar
inputs. All analytic, arithmetic and measure choices are constructed
from the same target before any moving scale, height or index. -/
theorem actualRecipeScalarInputs :
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)) :=
  actualRecipeScalarInputs_canonicalMeasures c (actualCatalogueVolumePrimitive c)

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualCatalogueVolumePrimitive
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeScalarInputs
