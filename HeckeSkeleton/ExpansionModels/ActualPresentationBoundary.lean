import HeckeSkeleton.HighBin
import Expansion.PhysicalRecipeFiniteSums
import Expansion.PhysicalRecipeRemainders
import Expansion.PowerHeightTailAlgebra

/-!
# The original whole-bin boundary is the actual recipe boundary

The named actual presentation reads its fixed rows, bin, displacement and
contour height from the same raw physical recipe.  Its whole-bin contour
difference therefore equals the unguarded double schedule once the
original active guard holds.  Exact finite reindexing introduces neither
additional bins nor amplitude labels.

The tail consumer below takes only the original `HighBoundaryControl`
hypothesis.  It does not call the separate, still independent high-bin
boundary producer.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project ExpansionInterfaces HighBinActualEuler
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  expansionNormOneSpace expansionNormOneBorel

local instance actualBoundary_sectorFintype (c : TargetContext K) :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

local instance actualBoundary_localHaar (c : TargetContext K) (p : places K c) :
    ((probeMeasures K c).haar p).IsAddHaarMeasure :=
  (probeMeasures K c).haar_isAddHaar p

variable (c : TargetContext K)
local notation "q" => expansionPhysicalParameters K c
local notation "Eactual" => arithmeticHighEulerData K (places K c)
  (probeData K c) (targetCharacter K c)
local notation "X" => expansionRecipeRaw K c

/-- The same original fixed-bin difference occurs in the raw recipe
tail and in the named actual high presentation. -/
theorem wholeBinBoundary_eq_physicalScheduled (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    wholeBinBoundary K c (actualHighPresentation K c) Z H =
      physicalScheduledWholeBoundary K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c) Eactual
        c.family.omega (targetCharacter K c) (representative K c).val.property
        (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
        c.geometry (expansionShellAllowance K c) Z H := by
  let term : Fin (shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c)) →
      PhysicalRecipeChoice K (places K c) c.family.B (q).e → ℂ := fun j d =>
    ∑ u ∈ physicalRecipeRows K (places K c) (probeData K c) Eactual c.family.omega
      (targetCharacter K c) (representative K c).val.property (expansionBoundary_lower K c)
      c.family.B_upper (q).e_pos c.family.boundary (expansionShellAllowance K c) Z H j d,
      (rowContourBox K (places K c) (probeMeasures K c).haar (probeData K c)
        (targetCharacter K c) Eactual c.geometry ∅ u Z H
        (c.family.B + 20 * (q).e) (1 - d.1.center - 6 * (q).e) (17 / 50) -
        rowContourBox K (places K c) (probeMeasures K c).haar (probeData K c)
          (targetCharacter K c) Eactual c.geometry ∅ u Z H
          (d.1.center + 16 * (q).e) (1 - d.1.center - 6 * (q).e) (17 / 50))
  calc
    _ = ∑ b : HighBlockIndex K c Z H,
        term (expansionScheduledShell K c Z H b) (expansionScheduledChoice K c Z H b) := by
      unfold wholeBinBoundary
      apply Finset.sum_congr rfl
      intro b _
      rw [expansionScheduled_bin K c Z H b, ← Finset.sum_sub_distrib]
      rfl
    _ = ∑ b : Fin ((X).scheduledCount Z),
        term (physicalRecipeShellIndex K (places K c) c.family.B (q).e
          (expansionShellAllowance K c) Z b)
          (physicalRecipeChoice K (places K c) c.family.B (q).e
            (expansionShellAllowance K c) Z b) :=
      recipeExpansion_sum_active_map K (places K c) (X) Z H hZ hH _
    _ = ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + expansionShellAllowance K c)),
        ∑ d : PhysicalRecipeChoice K (places K c) c.family.B (q).e, term j d :=
      sum_physicalRecipeSchedule K (places K c) c.family.B (q).e
        (expansionShellAllowance K c) Z term
    _ = _ := rfl

/-- The original allowed whole-bin boundary hypothesis transfers to the
identical scheduled summand of the actual expansion tail. -/
theorem physicalScheduledWholeBoundary_tail_of_highBoundaryControl
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound
      (physicalScheduledWholeBoundary K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c) Eactual
        c.family.omega (targetCharacter K c) (representative K c).val.property
        (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
        c.geometry (expansionShellAllowance K c)) := by
  exact PowerHeightTailBound.of_eventuallyEq hmove ((2 : ℝ) ^ (16 : ℕ))
    (wholeBinBoundary_eq_physicalScheduled K c)

end HeckeSkeleton

#print axioms HeckeSkeleton.wholeBinBoundary_eq_physicalScheduled
#print axioms HeckeSkeleton.physicalScheduledWholeBoundary_tail_of_highBoundaryControl
