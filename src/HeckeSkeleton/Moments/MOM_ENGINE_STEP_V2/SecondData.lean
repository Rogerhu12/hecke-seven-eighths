module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TerminalData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildSectors
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyClassStability

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The genuine second transform and its literal terminal expressions

The data below fix the original row-ball, its scale, the logarithmic
kernel, every coefficient and every Fourier location. The finite row
classifier has only the actual nonunit pattern and sixth-unit sector
complexity. No estimate of a terminal or descendant is a data field.

Paper: Section 4.8, lines 2883--2894 and 3004--3010.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PhysicalSource

variable (source : PhysicalSource call p)

def firstFrequency : ℝ :=
  2 * (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z) -
    idealLogLength call.base source.first.selected.val -
    idealLogLength call.base source.first.opposite.val +
    idealLogLength call.base
      (firstActiveRadical source.first.selected.val source.first.opposite.val) +
    idealLogLength call.base source.first.complementary.val - call.workingParameters.m

def enlargement : ℝ :=
  max (idealLogLength call.base source.first.opposite.val -
    idealLogLength call.base source.first.selected.val + source.firstFrequency -
    Real.log source.first.retainedScale / Real.log call.base -
    2 * source.first.tag.removedLength call.base + source.first.tag.movingLength call.base) 0 +
      source.first.tag.padding (recipeInductionSigma c)

/-- The exact maximum of the original finite orbit fibres. -/
def orbitMultiplicity : ℕ :=
  (source.source.rows.image
    (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))).sup
      (fun q => (source.source.rows.filter
        (fun h => engineElementOrbit (Γ := Arithmetic.unitSubgroup c) h = q)).card)

def activeCommon : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  commonSupportPool (source.source.columns.filter (fun i => source.source.coefficient i ≠ 0))
    (source.source.columns.filter (fun i => source.source.coefficient i ≠ 0))
    (fun i => (source.source.ideal i).val) (fun i => (source.source.ideal i).val)

end PhysicalSource

/-- This is the existing fixed logarithmic Fourier transform. It is
independent of all moving rows, coefficients, labels and source scales. -/
def secondKernel (c : TargetContext K) (p : SourceParameters c) : SchwartzMap ℝ ℂ := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  exact CanonicalSecondLogChart.kernel (Γ := Arithmetic.unitSubgroup c)
    (Arithmetic.localMeasures (K := K)) (Arithmetic.finiteMeasure (K := K))
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    p.tilt p.tilt_pos p.tilt_half (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)

namespace SecondSource

variable (source : SecondSource call p)

abbrev CommonLabel := commonSupportPool source.physical.source.columns
  source.physical.source.columns (fun i => (source.physical.source.ideal i).val)
  (fun i => (source.physical.source.ideal i).val)

abbrev block (DE : source.CommonLabel) := canonicalFirstCommonBlock
  (Arithmetic.context c) source.physical.source.columns source.physical.source.columns
  source.physical.source.ideal source.physical.source.ideal DE.val DE.property

abbrev rows (DE : source.CommonLabel) (D : source.stage.mask.powerset)
    (label : Fin ((source.stage.charts DE D).rowLabelCount + 1)) :=
  (source.stage.charts DE D).actualRows source.stage.mask source.stage.cutoff
    source.stage.cutoff_one label

/-- The exact original finite common-support discrepancy. -/
def truncationCost : ℝ :=
  ∑ DE : source.CommonLabel,
    ‖(∑ i ∈ (source.stage.sources DE).leftColumns,
        ∑ j ∈ (source.stage.sources DE).rightColumns,
          ((source.stage.sources DE).pairs i j).maskedSeries
            (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
              (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
            source.stage.radius source.stage.mask) -
      (source.stage.sources DE).transform (Arithmetic.localMeasures (K := K))
        (Arithmetic.different c) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖

def phaseStage (x : ℝ) := EngineStep.ActualGaussStage.withMultiplier source.stage
  (fun i => jointPhase x (source.physical.firstPoint i))

def phaseTail (x : ℝ) : ℝ :=
  ∑ DE : source.CommonLabel,
    ‖(∑ i ∈ ((source.phaseStage x).sources DE).leftColumns,
        ∑ j ∈ ((source.phaseStage x).sources DE).rightColumns,
          (((source.phaseStage x).sources DE).pairs i j).maskedSeries
            (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
              (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
            source.stage.radius source.stage.mask) -
      ((source.phaseStage x).sources DE).transform (Arithmetic.localMeasures (K := K))
        (Arithmetic.different c) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖

def zero : ℝ := source.physical.outerWeight * (source.stage.fiber : ℝ) *
  ∫ x, (source.phaseStage x).rawZeroCost ∂actualFourierMeasure source.physical.firstKernel

def tail : ℝ := source.physical.outerWeight * (source.stage.fiber : ℝ) *
  ∫ x, source.phaseTail x ∂actualFourierMeasure source.physical.firstKernel

def nonzero : ℝ := source.physical.outerWeight * (source.stage.fiber : ℝ) *
  ∫ x, (source.phaseStage x).rawNonzeroCost ∂actualFourierMeasure source.physical.firstKernel

theorem zero_nonneg : 0 ≤ source.zero :=
  mul_nonneg (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
    (integral_nonneg (fun _ => EngineStep.ActualGaussStage.rawZeroCost_nonneg _))

theorem tail_nonneg : 0 ≤ source.tail :=
  mul_nonneg (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
    (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem nonzero_nonneg : 0 ≤ source.nonzero :=
  mul_nonneg (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
    (integral_nonneg (fun _ => EngineStep.ActualGaussStage.rawNonzeroCost_nonneg _))

/-- Every analytic data field is fixed at the original single-column
level. The only classifier freedom is a bounded finite relabelling of
the actual nonunit pattern and sixth-unit sector. -/
structure Realizes : Prop where
  profile : source.stage.profile = CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1
  radius : source.stage.radius.val =
    (source.physical.first.retainedScale * call.base ^ source.physical.enlargement)⁻¹
  mask : source.stage.mask = ∅
  cutoff : source.stage.cutoff = p.secondCutoff call
  fiber : source.stage.fiber = source.physical.orbitMultiplicity
  kernel : ∀ DE D, (source.stage.charts DE D).kernel = secondKernel c p
  weight : ∀ DE D q, (source.stage.charts DE D).weight q =
    (((CanonicalSecondLogChart.rowRadius source.stage.radius D.val q).val ^ (-p.tilt) : ℝ) : ℂ)
  leftCoefficient : ∀ DE D i, (source.stage.charts DE D).leftCoefficient i =
    if DE.val ∈ source.physical.activeCommon then source.physical.source.coefficient i *
      (((Arithmetic.data c).exteriorNorm ((source.block DE).secondLeftIdeal i) ^ p.tilt : ℝ) : ℂ)
    else 0
  rightCoefficient : ∀ DE D i, (source.stage.charts DE D).rightCoefficient i =
    if DE.val ∈ source.physical.activeCommon then source.physical.source.coefficient i *
      (((Arithmetic.data c).exteriorNorm ((source.block DE).secondRightIdeal i) ^ p.tilt : ℝ) : ℂ)
    else 0
  leftPoint : ∀ DE D q i, (source.stage.charts DE D).leftPoint q i =
    Real.log (CanonicalSecondLogChart.rowRadius source.stage.radius D.val q).val -
      Real.log ((Arithmetic.data c).exteriorNorm ((source.block DE).secondLeftIdeal i))
  rightPoint : ∀ DE D q i, (source.stage.charts DE D).rightPoint q i =
    -Real.log ((Arithmetic.data c).exteriorNorm ((source.block DE).secondRightIdeal i))
  labelCount : ∀ DE D, (source.stage.charts DE D).rowLabelCount ≤
    2 ^ (source.block DE).primeCount *
      Nat.card (SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))))
  patternStable : ∀ DE D q r,
    (source.stage.charts DE D).rowLabel q = (source.stage.charts DE D).rowLabel r →
    actualNonunitPattern (Arithmetic.context c) (source.block DE).primes
      (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity (-q.out.val) =
    actualNonunitPattern (Arithmetic.context c) (source.block DE).primes
      (source.block DE).leftMultiplicity (source.block DE).rightMultiplicity (-r.out.val)
  sectorStable : ∀ DE D label (h k : (source.rows DE D label).live),
    ((source.rows DE D label).extractedRow (Arithmetic.context c) h).sector (probeData K c) =
    ((source.rows DE D label).extractedRow (Arithmetic.context c) k).sector (probeData K c)

end SecondSource

/-- Every amplified physical summand is transformed exactly once. -/
structure SecondFamily {F : FirstPresentation call p} {family : FirstCauchyFamily F}
    (expansion : PoolExpansion family) where
  source : Fin expansion.count → SecondSource call p

namespace SecondFamily

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} (second : SecondFamily expansion)

def zero : ℝ := ∑ i, (second.source i).zero
def tail : ℝ := ∑ i, (second.source i).tail
def nonzero : ℝ := ∑ i, (second.source i).nonzero
def normalizedZero : ℝ := call.normalizedScalar second.zero
def normalizedTail : ℝ := call.normalizedScalar second.tail

theorem normalizedZero_nonneg : 0 ≤ second.normalizedZero :=
  call.normalizedScalar_nonneg (Finset.sum_nonneg (fun _ _ => SecondSource.zero_nonneg _))

theorem normalizedTail_nonneg : 0 ≤ second.normalizedTail :=
  call.normalizedScalar_nonneg (Finset.sum_nonneg (fun _ _ => SecondSource.tail_nonneg _))

structure Realizes : Prop where
  physical : ∀ i, (second.source i).physical = expansion.source i
  stage : ∀ i, (second.source i).Realizes

end SecondFamily

/-- The same sequence of original source choices is shared by every
later estimate; no stage is selected again for a different terminal. -/
structure SourceTrace (call : Call c) (p : SourceParameters c) where
  first : FirstPresentation call p
  cauchy : FirstCauchyFamily first
  expansion : PoolExpansion cauchy
  second : SecondFamily expansion

namespace SourceTrace

structure Realizes (trace : SourceTrace call p) : Prop where
  first : trace.first.Realizes
  cauchy : trace.cauchy.Realizes
  firstWindows : ∀ i, (trace.cauchy.source i).Windows
  expansion : trace.expansion.Realizes
  poolWindows : ∀ i, (trace.expansion.source i).Windows
  second : trace.second.Realizes

end SourceTrace

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
