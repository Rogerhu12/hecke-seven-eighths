module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ComputedLengths

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: original pattern geometry and strict width descent

A single Boolean side fixes the original common ideal and its opposite.
The unit-pattern identity uses an original live correlation row; it does
not require the later ordinary rectangle to be nonempty. The resulting
geometry retains the supplied nominal geometry and the same calibration.
The base sixth-root ledger proves width descent with the full root kept.

Paper: Section 4.8, lines 2883--2906 and 2927--2946.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι]
variable (R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι)
variable (side : Bool)

def sixthRootLength (Z : ℝ) : ℝ :=
  idealLogLength Z (secondSixthRootIdeal R.primes
    (selectedMultiplicity R side) (oppositeMultiplicity R side)).val

theorem selectedMultiplicity_pos (hleft : ∀ i, 0 < R.leftMultiplicity i)
    (hright : ∀ i, 0 < R.rightMultiplicity i) :
    ∀ i, 0 < selectedMultiplicity R side i := by
  cases side
  · exact hleft
  · exact hright

theorem oppositeMultiplicity_pos (hleft : ∀ i, 0 < R.leftMultiplicity i)
    (hright : ∀ i, 0 < R.rightMultiplicity i) :
    ∀ i, 0 < oppositeMultiplicity R side i := by
  cases side
  · exact hright
  · exact hleft

/-- Swapping the column side does not replace the actual unit radical.
The complement identity is used only on an original live correlation. -/
theorem unitIdeal_eq_live (pattern : ι → Bool) (h : R.live)
    (hpattern : actualNonunitPattern (Arithmetic.context c) R.primes R.leftMultiplicity
      R.rightMultiplicity (R.frequency h.val) = pattern) :
    (secondPatternUnitIdeal R.primes (selectedMultiplicity R side)
      (oppositeMultiplicity R side) pattern).val =
      (unitFrequencyRadical (Arithmetic.context c) R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h.val)).val := by
  have he := congrArg Subtype.val
    (R.secondPatternUnitIdeal_eq_live (Arithmetic.context c) pattern h hpattern)
  cases side
  · exact he
  · change (secondPatternUnitIdeal R.primes R.rightMultiplicity R.leftMultiplicity
        pattern).val = _
    rw [secondPatternUnitIdeal_swap]
    exact he

variable {k : ℕ}
variable (s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k)
variable (D : OriginalCalibration call s) (p : SourceParameters c)
variable (G : OriginalNominalGeometry (K := K) call.workingParameters s.base
  (recipeInductionSigma c))
variable (pattern : ι → Bool)
variable (hleft : ∀ i, 0 < R.leftMultiplicity i)
variable (hright : ∀ i, 0 < R.rightMultiplicity i)
variable (hsecond : G.ideals.second.val =
  (primePowerProduct R.primes (selectedMultiplicity R side)).val)
variable (hopposite : G.ideals.secondOpposite.val =
  (primePowerProduct R.primes (oppositeMultiplicity R side)).val)
variable (hunit : G.ideals.unitPart.val =
  (secondPatternUnitIdeal R.primes (selectedMultiplicity R side)
    (oppositeMultiplicity R side) pattern).val)
variable (hm : D.calibration.parameters.m = rowParameter G (12 * p.loss))
variable (hq : D.calibration.parameters.q =
  supportParameter G (4 * p.loss) (sixthRootLength R side s.base))
variable (direct : G.tag = .direct → call.node.data.geometry.slotCount = 0)

/-- Primitive original ideal identities and the exact N3 parameters
construct the existing geometry record. The nominal geometry is retained
literally, including both its original first tag and its full support. -/
def sideGeometry : SideGeometryData R side s D where
  nominal := G
  pattern := pattern
  selected_pos := selectedMultiplicity_pos R side hleft hright
  opposite_pos := oppositeMultiplicity_pos R side hleft hright
  second_eq := hsecond
  opposite_eq := hopposite
  unit_eq := hunit
  lengths := originalSixthLengths D p G (sixthRootLength R side s.base) hm hq direct
  mesh_nonneg := (momentMesh K c.family).property.le

theorem sideGeometry_nominal :
    (sideGeometry R side s D p G pattern hleft hright hsecond hopposite hunit hm hq direct).nominal =
      G := by
  rfl

section Descent

variable {R side s D} (geometry : SideGeometryData R side s D)

include geometry in
/-- The actual calibration width drops after the complete sixth-root
support is included. No ordinary-row witness or analytic prime estimate
is needed for this geometric conclusion. -/
theorem source_width_drop :
    D.calibration.parameters.m + D.calibration.parameters.q ≤
      call.node.parameters.m + call.node.parameters.q - recipeInductionSigma c / 2 := by
  have hslack := geometry.nominal.sixthDeletion_slack_of_pattern s.base_gt_one
    R.primes R.primes_injective (selectedMultiplicity R side) (oppositeMultiplicity R side)
    geometry.selected_pos geometry.opposite_pos geometry.pattern
    geometry.second_eq geometry.opposite_eq geometry.unit_eq
  dsimp only at hslack
  have hdrop := geometry.lengths.scales.sixthDeletion_width_drop s.base_gt_one
    (recipeInduction_budget (c := c)).1.le (sixthRootLength R side s.base) hslack.2.1
  have hactual : D.calibration.parameters.m + D.calibration.parameters.q ≤
      call.workingParameters.m + call.workingParameters.q - recipeInductionSigma c / 2 := by
    simpa only [sixthRootLength, sub_add_cancel] using hdrop
  dsimp only [Call.workingParameters] at hactual
  linarith

include geometry in
theorem source_width_lt :
    D.calibration.parameters.m + D.calibration.parameters.q <
      call.node.parameters.m + call.node.parameters.q := by
  have hdrop := source_width_drop geometry
  have hstep := (recipeInduction_budget (c := c)).1
  linarith

end Descent

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.unitIdeal_eq_live
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.sideGeometry
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.source_width_drop
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.source_width_lt
