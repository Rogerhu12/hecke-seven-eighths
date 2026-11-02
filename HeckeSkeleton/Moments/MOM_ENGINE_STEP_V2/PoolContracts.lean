import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ArithmeticPrimePool

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# One pool for the whole first finite family

Paper: Section 4.8, lines 2852--2881. A pool is selected once, before
the first-source index and the main/1/6/7 index. The direct constructor
has no pool. Exact index bijections and exact scalar identities prevent
extra copies of a physical source or a repeated density charge.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

namespace PhysicalSource

def rowSize (source : PhysicalSource call p) : ℝ :=
  max 1 (source.source.rows.sup (fun h =>
    (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
      ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : ℝ≥0)) : ℝ)

def rowExponent (source : PhysicalSource call p) : ℝ :=
  Real.log source.rowSize / Real.log call.base

end PhysicalSource

/-- There is exactly one pool for all the first physical sources. -/
structure PoolPresentation (family : FirstCauchyFamily F) where
  pool : PowerScaleExteriorPool (Arithmetic.data c) ∅ call.base
    (recipeInductionSigma c / 3) p.loss
  data : ∀ i, FirstGaussPoolData (Arithmetic.context c) pool (family.source i).Column

namespace PoolPresentation

variable {family : FirstCauchyFamily F} (P : PoolPresentation family)

structure Realizes : Prop where
  original : ∀ i,
    (P.data i).directSource (family.source i).source.coefficient = (family.source i).source
  rowIdeal : ∀ i, (P.data i).rowIdeal = originalFrequencyIdeal
  frozen : ∀ i, (P.data i).frozen = (family.source i).first.residualDivisor.val
  rowExponent : ∀ i, (P.data i).rowExponent = (family.source i).rowExponent
  frozenExponent : ∀ i, (P.data i).frozenExponent =
    idealLogLength call.base (family.source i).first.residualDivisor.val
  density : ∀ i, call.base ^ (recipeInductionSigma c / 3 - 2 * p.loss) ≤
    (P.data i).density

abbrev Index := Σ i : Fin family.count,
  Unit ⊕ (P.pool.primes × AmplifierValuation)

def MainOrigin (i : Fin family.count) (source : PhysicalSource call p) : Prop :=
  HEq source.source ((P.data i).mainSource (family.source i).source.coefficient) ∧
  HEq source.ancestor (family.source i).ancestor ∧
  HEq source.multiplier (family.source i).multiplier ∧
  source.firstKernel = (family.source i).firstKernel ∧
  HEq source.firstPoint (family.source i).firstPoint ∧
  source.outerWeight = (family.source i).outerWeight *
    (4 / (P.data i).density) * (P.data i).multiplicity ∧
  source.first = { (family.source i).first with tag := .main }

def ErrorOrigin (i : Fin family.count) (q : P.pool.primes)
    (e : AmplifierValuation) (source : PhysicalSource call p) : Prop :=
  HEq source.source
    ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient) ∧
  HEq source.ancestor (fun j : (P.data i).valuationColumns q.val e.multiplicity =>
    (family.source i).ancestor j.val) ∧
  HEq source.multiplier
    ((P.data i).residualCoefficient q.val e.multiplicity (family.source i).multiplier) ∧
  source.firstKernel = (family.source i).firstKernel ∧
  HEq source.firstPoint (fun j : (P.data i).valuationColumns q.val e.multiplicity =>
    (family.source i).firstPoint j.val) ∧
  source.outerWeight = (family.source i).outerWeight * (4 / (P.data i).density) *
    FirstGaussPoolData.localErrorWeight q.val e.multiplicity ∧
  source.first.selected = (family.source i).first.selected ∧
  source.first.opposite = (family.source i).first.opposite ∧
  source.first.complementary = (family.source i).first.complementary ∧
  source.first.residualDivisor = (family.source i).first.residualDivisor ∧
  source.first.retainedScale = (family.source i).first.retainedScale ∧
  source.first.tag = .error e q.val.val ∧
  source.first.fullDeletion = (family.source i).first.fullDeletion ∪ {q.val.val.asIdeal} ∧
  source.first.paidSupport.val = (family.source i).first.paidSupport.val *
    q.val.val.asIdeal ^ e.movingMultiplicity

def Origin (index : P.Index) (source : PhysicalSource call p) : Prop :=
  match index.2 with
  | .inl _ => P.MainOrigin index.1 source
  | .inr qe => P.ErrorOrigin index.1 qe.1 qe.2 source

end PoolPresentation

/-- The constructor itself records whether amplification occurred.
In the direct case the first family is reused literally. -/
inductive PoolExpansion (family : FirstCauchyFamily F) where
  | direct
  | pooled (pool : PoolPresentation family) (count : ℕ)
      (index : Fin count ≃ pool.Index) (source : Fin count → PhysicalSource call p)

namespace PoolExpansion

variable {family : FirstCauchyFamily F} (expansion : PoolExpansion family)

def count : ℕ :=
  match expansion with
  | .direct => family.count
  | .pooled _ count _ _ => count

def source : Fin expansion.count → PhysicalSource call p :=
  match expansion with
  | .direct => family.source
  | .pooled _ _ _ source => source

def cost : ℝ := ∑ i, (expansion.source i).cost

def Realizes : Prop :=
  match expansion with
  | .direct => call.node.data.geometry.slotCount = 0
  | .pooled pool _ index source =>
    call.node.data.geometry.slotCount ≠ 0 ∧ pool.Realizes ∧
      ∀ i, pool.Origin (index i) (source i)

end PoolExpansion

/-- S3. A single original prime pool, its three exact correction
valuations, and their density, with a separate zero-slot direct exit. -/
def AmplificationTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, ∃ demand : UniformDemand,
    ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      demand.Ready call input → ∀ (F : FirstPresentation call p), F.Realizes →
      ∀ family : FirstCauchyFamily F, family.Realizes →
      (∀ i, (family.source i).Windows) →
      ∃ expansion : PoolExpansion family,
        expansion.Realizes ∧ family.cost ≤ expansion.cost ∧
        ∀ i, (expansion.source i).Windows

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
