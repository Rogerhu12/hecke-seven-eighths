import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original sixth-root geometry and one side-independent normalization

The right column uses the opposite original common ideal. A Boolean
side selects the two multiplicity functions once, so the same base
sixth-root capacity constructor handles both sides. No descendant
capacity, width inequality or removal set is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H ι : Type} [Fintype ι] [DecidableEq ι]

def columnSide : Bool → SecondColumnSide
  | false => .left
  | true => .right

def selectedMultiplicity
    (R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι)
    (side : Bool) : ι → ℕ :=
  if side then R.rightMultiplicity else R.leftMultiplicity

def oppositeMultiplicity
    (R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι)
    (side : Bool) : ι → ℕ :=
  if side then R.leftMultiplicity else R.rightMultiplicity

variable (R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι)
variable (side : Bool) {k : ℕ}
variable (f : SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
  R PUnit (columnSide side) k)
variable (D : OriginalCalibration call f.source)

structure SideGeometryData where
  nominal : OriginalNominalGeometry call.workingParameters f.source.base
    (recipeInductionSigma c)
  pattern : ι → Bool
  selected_pos : ∀ i, 0 < selectedMultiplicity R side i
  opposite_pos : ∀ i, 0 < oppositeMultiplicity R side i
  second_eq : nominal.ideals.second.val =
    (primePowerProduct R.primes (selectedMultiplicity R side)).val
  opposite_eq : nominal.ideals.secondOpposite.val =
    (primePowerProduct R.primes (oppositeMultiplicity R side)).val
  unit_eq : nominal.ideals.unitPart.val =
    (secondPatternUnitIdeal R.primes (selectedMultiplicity R side)
      (oppositeMultiplicity R side) pattern).val
  lengths : D.calibration.OriginalSixthLengthBinding call.node.data
    call.workingParameters (recipeInductionSigma c) nominal
    (idealLogLength f.source.base
      (secondSixthRootIdeal R.primes (selectedMultiplicity R side)
        (oppositeMultiplicity R side)).val)
  mesh_nonneg : 0 ≤ (momentMesh K c.family).val

namespace SideGeometryData

variable {R side f D}
variable (G : SideGeometryData R side f D)
variable {window : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable {B δ lengthBound analyticHeight width : ℝ} {J₁ J₂ : ℕ}

/-- This real constructor uses exactly the displayed arithmetic
calibration, global profile representatives and original length ledger.
The base then normalizes all profiles and chooses whole slots once. -/
def normalization
    (profiles : D.calibration.FullKappaProfileInput D.recipe
      Set.univ Set.univ window orders B J₁ J₂ δ lengthBound analyticHeight width) :
    SecondSideNormalization f c.family.omega (targetCharacter K c)
      Set.univ Set.univ window orders where
  calibration := D.calibration
  capacity := G.lengths.capacityInputOfPattern R.primes_injective
    G.selected_pos G.opposite_pos G.pattern G.second_eq G.opposite_eq G.unit_eq
    (recipeInduction_budget (c := c)).1 (momentMesh K c.family).val
    G.mesh_nonneg call.fitsMesh profiles.atoms
  amplitude := profiles.amplitude
  amplitude_pos := profiles.amplitude_pos
  bounds := fun _ => 1
  bounds_nonneg := fun _ => zero_le_one
  factor := profiles.atoms_primeBound
  profile := profiles.clippedWindow

end SideGeometryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
