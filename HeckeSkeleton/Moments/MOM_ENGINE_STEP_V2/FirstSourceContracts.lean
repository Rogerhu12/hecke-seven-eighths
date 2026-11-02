import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDivisorPhysicalSource

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# First source and first Poisson task

The source is tied to the original finite column dictionary and the
literal logarithmic chart. Its two row carriers and its row weight
majorant are fixed by the actual first physical source. Thus later
tasks are not asked to estimate an arbitrary enlarged carrier or an
arbitrarily rescaled Schwartz kernel.

Paper: Section 4.8, lines 2800--2828. The independent proof task is
`FirstTransformTask`; it retains the actual zero term and the actual
finite truncation discrepancy, without choosing a tail majorant.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

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

/-- Only a source and its original column coordinates are data. -/
structure FirstPresentation (call : Call c) (p : SourceParameters c) where
  source : FirstSource call p
  index : source.Column ≃ call.workingRaw.Column

namespace FirstPresentation

variable (F : FirstPresentation call p)

def coefficient (i : F.source.Column) : ℂ :=
  call.workingValues.coefficient call.node.centered (F.index i)

def originalProfile (i j : F.source.Column) :
    SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  (F.coefficient i * star (F.coefficient j)) •
    CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1

/-- The fixed base log chart, including its actual inverse norm
factors. It is independent of any later source or child estimate. -/
def canonicalChart (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) :
    FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (F.source.block v)
      (Arithmetic.context c) F.source.columns F.source.columns F.originalProfile
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  exact FirstBlockProfileChart.canonicalLogWithCoefficients
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.finiteMeasure (K := K)) (F.source.block v)
    (Arithmetic.context c) F.source.columns F.source.columns
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)
    F.coefficient F.coefficient (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    F.source.radius D.val p.tilt p.tilt_pos p.tilt_half

/-- All equalities are on original atoms, actual rows or actual log
charts. No polynomial bound or transformed-family conclusion is a field. -/
structure Realizes : Prop where
  active : call.Active
  columns : F.source.columns.map F.index.toEmbedding = call.workingRaw.exteriorColumns
  ideal : ∀ i, F.source.ideal i = call.workingRaw.columnExterior (F.index i)
  generator : ∀ i, F.source.generator i =
    engineAllowedGenerator (Arithmetic.context c) (F.source.ideal i)
  profile : F.source.profiles = F.originalProfile
  radius : F.source.radius.val = call.base ^ (-call.workingParameters.m)
  mask : F.source.mask = ∅
  fiber : F.source.fiber = 1
  chart : ∀ v D, HEq (F.source.charts v D) (F.canonicalChart v D)
  leftRows : ∀ v D, (F.source.pieces v D).leftData.rows =
    ((F.source.source v).divisorRows D.val).image (fun q => q.out.val)
  rightRows : ∀ v D, (F.source.pieces v D).rightData.rows =
    ((F.source.source v).divisorRows D.val).image (fun q => -q.out.val)
  weight : ∀ v D, (F.source.pieces v D).weightBound =
    (((F.source.source v).divisorRows D.val).sup
      (fun q => ‖(F.source.charts v D).weight q‖₊) : ℝ)

def zero : ℝ :=
  (F.source.fiber : ℝ) * F.source.zeroCost (Arithmetic.different c)

/-- The whole original common-support matrix is truncated at its own
physical cutoff before any residual coprimality or Fourier absolute value. -/
def tail : ℝ :=
  (F.source.fiber : ℝ) * ∑ v : F.source.CommonLabel,
    ‖(∑ i ∈ (F.source.source v).leftColumns,
        ∑ j ∈ (F.source.source v).rightColumns,
          ((F.source.source v).pairs i j).maskedSeries
            (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
              (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
            F.source.radius F.source.mask) -
      (F.source.source v).transform (Arithmetic.localMeasures (K := K))
        (Arithmetic.different c) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖

end FirstPresentation

/-- S1. Original whole-centered source, exact first transform and raw
zero/tail separation. Both zero-slot and positive-slot inputs use it. -/
def FirstTransformTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ call : Call c, call.Active → ∃ F : FirstPresentation call p,
    F.Realizes ∧ ∀ N : F.source.Normalization,
      call.node.energy call.base 0 ≤
        F.zero + F.tail + (F.source.fiber : ℝ) *
          F.source.linearizedCost (Arithmetic.different c) N

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
