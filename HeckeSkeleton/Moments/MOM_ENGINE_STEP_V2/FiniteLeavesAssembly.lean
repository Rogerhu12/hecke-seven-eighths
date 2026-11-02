import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesIntegral

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S6: exact finite enumeration and the original nonzero bound

The original class and allocation labels are flattened once. The sole
restriction removes labels whose original costs both vanish. A single
finite equivalence then supplies the public raw family without copies
or enlarged weights.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance finiteLeavesAssemblyCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace FiniteLeaves

/-- The base positive Fourier comparison, with the original orbital
fibre and outer scalar each paid once. -/
theorem source_nonzero_le_sum (source : SecondSource call p)
    (LC RC : SourceCartesianCover source.physical.source.columns source.physical.source.ideal)
    (exceptional : source.stage.CoverHybridPredicates LC RC) :
    source.nonzero ≤ ∑ key : (Σ v : SourceClassKey source.stage LC RC,
        SourceClassKey.AllocationKey v),
      (secondSourceLeaf source LC RC key.1 exceptional key.2).cost := by
  have h := source.stage.integral_rawPhaseNonzeroCost_le_cover LC RC
    source.physical.firstKernel source.physical.firstPoint exceptional
  have hw : 0 ≤ source.physical.outerWeight * (source.stage.fiber : ℝ) :=
    mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _)
  calc
    source.nonzero ≤ (source.physical.outerWeight * (source.stage.fiber : ℝ)) *
        ∫ x, source.stage.coverHybridPhaseNonzeroCost LC RC exceptional
          source.physical.firstPoint x ∂actualFourierMeasure source.physical.firstKernel :=
      mul_le_mul_of_nonneg_left h hw
    _ = ∑ key : (Σ v : SourceClassKey source.stage LC RC,
          SourceClassKey.AllocationKey v),
        (secondSourceLeaf source LC RC key.1 exceptional key.2).cost := by
      rw [FiniteLeavesIntegral.ActualGaussStage.integral_coverHybridPhaseNonzeroCost_eq_leaf_sum]
      simp only [Finset.mul_sum, secondSourceLeaf, ActualHybridLeaf.scale_cost]

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}

/-- Every source and every class/allocation key occurs once. -/
theorem nonzero_le_sum (covers : RawCovers second) :
    second.nonzero ≤ ∑ key : covers.Key, (covers.leaf key).cost := by
  have hs (i : Fin expansion.count) := source_nonzero_le_sum (second.source i)
    (covers.left i).cover (covers.right i).cover (covers.predicates i)
  simp only [Fintype.sum_sigma] at hs
  change (∑ i, (second.source i).nonzero) ≤ _
  simp only [RawCovers.Key, RawCovers.ClassKey, Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun i _ => hs i)

theorem sum_cost_eq_retained (covers : RawCovers second) (hsecond : second.Realizes) :
    (∑ key : covers.Key, (covers.leaf key).cost) =
      ∑ key : covers.LiveKey, (covers.leaf key.val).cost := by
  let retained : Finset covers.Key := Finset.univ.filter
    (fun key => (covers.leaf key).Live ∧ (covers.classKey key).Active)
  have hz (key : covers.Key) (hk : key ∉ retained) : (covers.leaf key).cost = 0 := by
    have hn : ¬((covers.leaf key).Live ∧ (covers.classKey key).Active) := by
      intro h
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have h := FiniteLeavesSupport.costs_zero_of_not_retained covers hsecond key hn
    exact show (covers.leaf key).exceptionalCost + (covers.leaf key).ordinaryCost = 0 by
      rw [h.1, h.2, add_zero]
  calc
    (∑ key : covers.Key, (covers.leaf key).cost) =
        ∑ key ∈ retained, (covers.leaf key).cost := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun key _ hk => hz key hk)
    _ = ∑ key : covers.LiveKey, (covers.leaf key.val).cost :=
      Finset.sum_subtype retained (by intro key; simp only [retained,
        Finset.mem_filter, Finset.mem_univ, true_and]) _

/-- An equivalence, rather than a surjection, prevents duplicated leaves. -/
def fromCovers (geometry : GeometryFamily second) (covers : RawCovers second) :
    RawFamily geometry where
  covers := covers
  count := Fintype.card covers.LiveKey
  index := (Fintype.equivFin covers.LiveKey).symm

theorem packet_leaf (geometry : GeometryFamily second) (covers : RawCovers second)
    (j : Fin (fromCovers geometry covers).count) :
    ((fromCovers geometry covers).packet j).leaf =
      covers.leaf ((fromCovers geometry covers).index j).val := rfl

theorem sum_cost_eq_raw (geometry : GeometryFamily second) (covers : RawCovers second) :
    (∑ key : covers.LiveKey, (covers.leaf key.val).cost) =
      (fromCovers geometry covers).exceptional + (fromCovers geometry covers).ordinary := by
  rw [← (fromCovers geometry covers).index.sum_comp
    (fun key : covers.LiveKey => (covers.leaf key.val).cost)]
  change (∑ j, ((fromCovers geometry covers).packet j).leaf.cost) = _
  simp only [ActualHybridLeaf.cost, Finset.sum_add_distrib,
    RawFamily.exceptional, RawFamily.ordinary]

/-- Once the original covers are built, the public S6 conclusion
follows from the base Fourier comparison and exact zero deletion. -/
theorem finiteLeaves_of_covers (geometry : GeometryFamily second)
    (hsecond : second.Realizes) (covers : RawCovers second)
    (hcovers : ∀ i, (covers.left i).Realizes ∧ (covers.right i).Realizes) :
    ∃ raw : RawFamily geometry, raw.Realizes ∧
      second.nonzero ≤ raw.exceptional + raw.ordinary := by
  refine ⟨fromCovers geometry covers, hcovers, ?_⟩
  exact (nonzero_le_sum covers).trans_eq
    ((sum_cost_eq_retained covers hsecond).trans (sum_cost_eq_raw geometry covers))

end FiniteLeaves
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves.finiteLeaves_of_covers
