import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Literal sources of the single-pool expansion

The output carrier has one main label and exactly the three valuation
labels for each prime of the earlier pool. Every coefficient, Fourier
point, ancestor and scalar is the one prescribed by `PoolContracts`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance valuationFintype : Fintype AmplifierValuation where
  elems := {.one, .six, .seven}
  complete e := by cases e <;> simp

theorem sum_valuation (f : AmplifierValuation → ℝ) :
    (∑ e, f e) = f .one + f .six + f .seven := by
  change (∑ e ∈ ({.one, .six, .seven} : Finset AmplifierValuation), f e) = _
  simp [add_assoc]

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

def main (P : PoolPresentation family) (i : Fin family.count) :
    PhysicalSource call p :=
  { family.source i with
    source := (P.data i).mainSource (family.source i).source.coefficient
    outerWeight := (family.source i).outerWeight *
      (4 / (P.data i).density) * (P.data i).multiplicity
    outerWeight_nonneg := mul_nonneg
      (mul_nonneg (family.source i).outerWeight_nonneg
        (div_nonneg (by norm_num) (P.data i).density_pos.le))
      (P.data i).multiplicity_nonneg
    first := { (family.source i).first with tag := .main } }

theorem main_origin (P : PoolPresentation family) (i : Fin family.count) :
    P.MainOrigin i (main P i) := by
  exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, rfl, rfl⟩

def error (P : PoolPresentation family) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation) : PhysicalSource call p where
  Column := (P.data i).valuationColumns q.val e.multiplicity
  source := (P.data i).residualSource q.val e.multiplicity
    (family.source i).source.coefficient
  ancestor j := (family.source i).ancestor j.val
  multiplier := (P.data i).residualCoefficient q.val e.multiplicity
    (family.source i).multiplier
  firstKernel := (family.source i).firstKernel
  firstPoint j := (family.source i).firstPoint j.val
  outerWeight := (family.source i).outerWeight * (4 / (P.data i).density) *
    FirstGaussPoolData.localErrorWeight q.val e.multiplicity
  outerWeight_nonneg := mul_nonneg
    (mul_nonneg (family.source i).outerWeight_nonneg
      (div_nonneg (by norm_num) (P.data i).density_pos.le))
    (FirstGaussPoolData.localErrorWeight_nonneg q.val e.multiplicity)
  first :=
    { (family.source i).first with
      poolPower := powerIdeal q.val e.multiplicity
      tag := .error e q.val.val
      fullDeletion := (family.source i).first.fullDeletion ∪ {q.val.val.asIdeal}
      paidSupport := ExteriorIdealEuler.mul (family.source i).first.paidSupport
        (powerIdeal q.val e.movingMultiplicity) }

theorem error_origin (P : PoolPresentation family) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation) :
    P.ErrorOrigin i q e (error P i q e) := by
  exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def physical (P : PoolPresentation family) (key : P.Index) :
    PhysicalSource call p :=
  match key.2 with
  | .inl _ => main P key.1
  | .inr qe => error P key.1 qe.1 qe.2

theorem physical_origin (P : PoolPresentation family) (key : P.Index) :
    P.Origin key (physical P key) := by
  rcases key with ⟨i, key⟩
  cases key with
  | inl u => exact main_origin P i
  | inr qe => exact error_origin P i qe.1 qe.2

def expansion (P : PoolPresentation family) : PoolExpansion family :=
  .pooled P (Fintype.card P.Index) (Fintype.equivFin P.Index).symm
    (fun i => physical P ((Fintype.equivFin P.Index).symm i))

theorem expansion_realizes (P : PoolPresentation family)
    (hslots : call.node.data.geometry.slotCount ≠ 0) (hP : P.Realizes) :
    (expansion P).Realizes := by
  exact ⟨hslots, hP, fun i => physical_origin P _⟩

theorem expansion_cost (P : PoolPresentation family) :
    (expansion P).cost = ∑ key : P.Index, (physical P key).cost := by
  exact (Fintype.equivFin P.Index).symm.sum_comp (fun key => (physical P key).cost)

theorem direct_solution (hslots : call.node.data.geometry.slotCount = 0)
    (windows : ∀ i, (family.source i).Windows) :
    ∃ output : PoolExpansion family,
      output.Realizes ∧ family.cost ≤ output.cost ∧
      ∀ i, (output.source i).Windows := by
  exact ⟨.direct, hslots, le_rfl, windows⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3
