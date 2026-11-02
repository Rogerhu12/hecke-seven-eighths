import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.InputDemands
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorNormCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectOriginalData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstPhase

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original first allowances and the finite Cauchy family

Paper: Section 4.8, lines 2827--2850. The source key is the actual
common pair, physical mask divisor, residual coprimality divisor,
finite character and chosen Cauchy side. A bijection with that key
prevents arbitrary duplicated labels or enlarged outer weights.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance firstCauchyCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

abbrev FirstCauchyKey (F : FirstPresentation call p) :=
  Σ v : F.source.CommonLabel,
    Σ D : ((F.source.block v).mask F.source.mask).powerset,
      divisorPool (F.source.pieces v D).rightData.columns
        (fun i => ((F.source.pieces v D).rightData.ideal i).val) ×
        ((PUnit.{1} × PUnit.{1}) →* Circle) × Bool

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : FirstCauchyKey F)

abbrev common := key.1
abbrev divisor := key.2.1
abbrev residual := key.2.2.1
abbrev character := key.2.2.2.1
abbrev side := key.2.2.2.2
abbrev block := F.source.block key.1
abbrev chart := F.source.charts key.1 key.2.1
abbrev piece := F.source.pieces key.1 key.2.1

def data : DirectGaussData (Arithmetic.context c) F.source.Column :=
  if FirstCauchyKey.side key then (FirstCauchyKey.piece key).rightData
  else (FirstCauchyKey.piece key).leftData

def point (i : F.source.Column) : ℝ :=
  if FirstCauchyKey.side key then -(FirstCauchyKey.chart key).rightPoint i
  else (FirstCauchyKey.chart key).leftPoint i

/-- The fixed first reciprocity element, before either continuous
Fourier variable. It includes the actual physical mask generator. -/
def firstElement : (Arithmetic.data c).R :=
  let b := FirstCauchyKey.block key
  let delta := (sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (FirstCauchyKey.divisor key).val).val
  if FirstCauchyKey.side key then
    CanonicalLiteralFirstPhase.rightElement (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity delta
  else
    CanonicalLiteralFirstPhase.leftElement (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity delta

def phase : ℂ :=
  if FirstCauchyKey.side key then
    (fixedRightPhase PUnit (FirstCauchyKey.character key) PUnit.unit : ℂ)
  else (fixedLeftPhase PUnit (FirstCauchyKey.character key) PUnit.unit : ℂ)

def coefficient (i : F.source.Column) : ℂ :=
  if (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val then
    (if FirstCauchyKey.side key then
      (FirstCauchyKey.piece key).originalRightCoefficient i
    else (FirstCauchyKey.piece key).originalLeftCoefficient i) *
      FirstCauchyKey.phase key
  else 0

/-- The same explicit linear column operation acts on each rectangle. -/
def multiplier (i : F.source.Column) : ℂ :=
  let b := FirstCauchyKey.block key
  let r := actualActiveColumn (Arithmetic.units_are_sixth c)
    (Arithmetic.context c) b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let delta := (sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (FirstCauchyKey.divisor key).val).val
  if (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val then
    (if FirstCauchyKey.side key then
      let a := generatedOriginalColumn (σ := Arithmetic.embedding c)
        (Arithmetic.units_are_sixth c) (b.rightResidual i)
        (b.rightGenerator i) (b.right_generates i)
      ((((Arithmetic.data c).exteriorNorm (b.rightResidual i) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm (b.rightResidual i) : ℂ)) *
          firstRightDivisorFactor a r delta
    else
      let a := generatedOriginalColumn (σ := Arithmetic.embedding c)
        (Arithmetic.units_are_sixth c) (b.leftResidual i)
        (b.leftGenerator i) (b.left_generates i)
      ((((Arithmetic.data c).exteriorNorm (b.leftResidual i) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm (b.leftResidual i) : ℂ)) *
          firstLeftDivisorFactor a r delta) * FirstCauchyKey.phase key
  else 0

def outer (N : F.source.Normalization) : ℝ :=
  let NL := N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  let NR := N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  (F.source.fiber : ℝ) * ‖(moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
    ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) (FirstCauchyKey.character key)‖ *
    ((FirstCauchyKey.piece key).rowBound * Real.sqrt NL * Real.sqrt NR / 2) /
    (if FirstCauchyKey.side key then NR else NL)

end FirstCauchyKey

namespace PhysicalSource

variable (source : PhysicalSource call p)

def cost : ℝ :=
  source.outerWeight * ∫ x,
    source.source.phaseEnergy (hDiff := Arithmetic.different c) source.firstPoint x
      ∂actualFourierMeasure source.firstKernel

/-- Only actual column and row norm windows appear here. They precede
the second Poisson transform and every descendant capacity choice. -/
structure Windows : Prop where
  retained_upper : source.source.rows.Nonempty → source.first.retainedScale ≤
    call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z) - idealLogLength call.base source.first.selected.val -
      idealLogLength call.base source.first.opposite.val +
      idealLogLength call.base (firstActiveRadical source.first.selected.val source.first.opposite.val) +
      idealLogLength call.base source.first.complementary.val - call.workingParameters.m + 4 * p.loss)
  column_lower : ∀ i ∈ source.source.columns, source.source.coefficient i ≠ 0 →
    call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z - idealLogLength call.base source.first.selected.val -
      source.first.tag.removedLength call.base - 4 * p.loss) ≤
        (Arithmetic.data c).exteriorNorm (source.source.ideal i)
  column_upper : ∀ i ∈ source.source.columns, source.source.coefficient i ≠ 0 →
    (Arithmetic.data c).exteriorNorm (source.source.ideal i) ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z - idealLogLength call.base source.first.selected.val -
        source.first.tag.removedLength call.base + 4 * p.loss)
  row_upper : ∀ h ∈ source.source.rows,
    (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤
      source.first.retainedScale * call.base ^
        (source.first.tag.padding (recipeInductionSigma c))

end PhysicalSource

/-- The original linearized source, with all its finite labels exactly
once. There is no aggregate inequality among the data fields. -/
structure FirstCauchyFamily (F : FirstPresentation call p) where
  normalization : F.source.Normalization
  count : ℕ
  index : Fin count ≃ FirstCauchyKey F
  source : Fin count → PhysicalSource call p

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

def cost : ℝ := ∑ i, (family.source i).cost

structure Realizes : Prop where
  column : ∀ i, (family.source i).Column = F.source.Column
  leftAllowance : ∀ v D S chi,
    family.normalization.left v D S chi = firstLeftAllowance call.base
      (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
        call.workingParameters.q + idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
        idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val)
      v.val.1 v.val.2
  rightAllowance : ∀ v D S chi,
    family.normalization.right v D S chi = firstRightAllowance call.base
      (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
        call.workingParameters.q + idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
        idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val)
      v.val.1 v.val.2
  source : ∀ i, HEq (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource (FirstCauchyKey.coefficient (family.index i)))
  ancestor : ∀ i, HEq (family.source i).ancestor (fun j : F.source.Column => F.index j)
  multiplier : ∀ i, HEq (family.source i).multiplier (FirstCauchyKey.multiplier (family.index i))
  kernel : ∀ i, (family.source i).firstKernel = (FirstCauchyKey.chart (family.index i)).kernel
  point : ∀ i, HEq (family.source i).firstPoint (FirstCauchyKey.point (family.index i))
  outer : ∀ i, (family.source i).outerWeight =
    FirstCauchyKey.outer (family.index i) family.normalization
  selected : ∀ i, (family.source i).first.selected.val =
    if FirstCauchyKey.side (family.index i) then (family.index i).1.val.2 else (family.index i).1.val.1
  opposite : ∀ i, (family.source i).first.opposite.val =
    if FirstCauchyKey.side (family.index i) then (family.index i).1.val.1 else (family.index i).1.val.2
  complementary : ∀ i, (family.source i).first.complementary.val =
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) (family.index i).2.1.val).val
  residual : ∀ i, (family.source i).first.residualDivisor.val =
    (FirstCauchyKey.residual (family.index i)).val
  firstElement : ∀ i, (family.source i).first.firstElement =
    FirstCauchyKey.firstElement (family.index i)
  firstRight : ∀ i, (family.source i).first.firstRight =
    FirstCauchyKey.side (family.index i)
  poolPower : ∀ i, (family.source i).first.poolPower = unitExterior (Arithmetic.data c)
  tag : ∀ i, (family.source i).first.tag = .direct
  retained : ∀ i, (family.source i).first.retainedScale =
    max 1 ((F.source.source (family.index i).1).divisorPhysicalCutoff (family.index i).2.1.val)
  deletion : ∀ i, (family.source i).first.fullDeletion =
    primeSupport (family.source i).first.selected.val
  paid : ∀ i, (family.source i).first.paidSupport.val = call.oldSupport.val *
    (firstActiveIdeal (FirstCauchyKey.block (family.index i)).primes
      (FirstCauchyKey.block (family.index i)).leftMultiplicity
      (FirstCauchyKey.block (family.index i)).rightMultiplicity).val *
        (family.source i).first.complementary.val

end FirstCauchyFamily

/-- S2. Original Cauchy allowances, literal first-divisor enumeration
and physical windows. The demand depends only on fixed source data. -/
def FirstAllowanceTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, ∃ demand : UniformDemand,
    ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      demand.Ready call input → ∀ F : FirstPresentation call p,
      F.Realizes → ∃ family : FirstCauchyFamily F,
        family.Realizes ∧
        (F.source.fiber : ℝ) * F.source.linearizedCost
          (Arithmetic.different c) family.normalization = family.cost ∧
        ∀ i, (family.source i).Windows

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
