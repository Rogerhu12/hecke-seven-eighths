import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceFirstMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! Exact separation of the original raw carrier into its physical
source index and its complete second-class arithmetic mass. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8RawMassCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}

namespace PhysicalSource

def firstCommonFactor (source : PhysicalSource call p) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical source.first.selected.val source.first.opposite.val) : ℝ)) *
    ‖(moebius source.first.residualDivisor.val : ℂ)‖

theorem firstCommonFactor_nonneg (source : PhysicalSource call p) :
    0 ≤ source.firstCommonFactor := by
  unfold firstCommonFactor
  positivity

end PhysicalSource

namespace SecondSource

variable (source : SecondSource call p) (LC RC : OriginalCover source.physical)

theorem classIndexMass_eq_class_sum :
    source.classIndexMass LC RC =
      ∑ key : SourceClassKey source.stage LC.cover RC.cover,
        if key.1.val ∈ source.physical.activeCommon then
          (1 / (Ideal.absNorm (commonRadical key.1.val.1 key.1.val.2) : ℝ)) *
            SourceClassKey.allocationIndexMass (source := source) (LC := LC) (RC := RC) key
        else 0 := by
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro DE _
  by_cases hDE : DE.val ∈ source.physical.activeCommon
  · simp only [if_pos hDE, Finset.mul_sum]
  · simp only [if_neg hDE, Finset.sum_const_zero]

end SecondSource

namespace PoolExpansion

def firstIndexMass (expansion : PoolExpansion family) : ℝ :=
  ∑ i, expansion.indexPrefactor i * (expansion.source i).firstIndexWeight

theorem firstIndexMass_nonneg (expansion : PoolExpansion family) :
    0 ≤ expansion.firstIndexMass :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (expansion.indexPrefactor_nonneg i)
    (expansion.source i).firstIndexWeight_nonneg)

end PoolExpansion

namespace RawCovers

variable (covers : RawCovers second)

theorem supportedIndexMass_eq :
    covers.supportedIndexMass =
      ∑ i : Fin expansion.count,
        if 0 < (second.source i).physical.outerWeight ∧
            (second.source i).physical.source.rows.Nonempty then
          expansion.indexPrefactor i * (second.source i).physical.firstCommonFactor *
            (second.source i).classIndexMass (covers.left i) (covers.right i)
        else 0 := by
  unfold supportedIndexMass supportedKeys
  rw [Finset.sum_filter]
  conv_lhs =>
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpos : 0 < (second.source i).physical.outerWeight
  · by_cases hrows : (second.source i).physical.source.rows.Nonempty
    · simp only [hpos, hrows, true_and, if_true]
      rw [(second.source i).classIndexMass_eq_class_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      by_cases hDE : key.1.val ∈ (second.source i).physical.activeCommon
      · simp only [if_pos hDE]
        simp only [SourceClassKey.allocationIndexMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro allocation _
        unfold indexWeight N8Source.arithmeticWeight arithmeticKey
          PhysicalSource.firstCommonFactor
        ring
      · simp only [if_neg hDE, Finset.sum_const_zero, mul_zero]
    · simp only [hpos, hrows, true_and, false_and, if_false, Finset.sum_const_zero]
  · simp only [hpos, false_and, if_false, Finset.sum_const_zero]

end RawCovers

namespace N8Source

/-- The original raw sum is reduced to the same single amplified first
index.  The second common sum supplies exactly the first-divisor norm
already present in `PoolExpansion.firstIndexMass`. -/
theorem original_raw_index_reduction (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (trace : SourceTrace call p), trace.Realizes →
      ∀ (geometry : GeometryFamily trace.second) (raw : RawFamily geometry), raw.Realizes →
        raw.indexMass ≤ C * call.base ^ ε * trace.expansion.firstIndexMass := by
  obtain ⟨C, hC, hmass⟩ := original_second_class_mass c ε hε
  refine ⟨C, hC, ?_⟩
  intro call input large p trace htrace geometry raw hraw
  have hbase_pos : 0 < call.base := call.base_pos
  apply raw.indexMass_le_supportedIndexMass.trans
  rw [raw.covers.supportedIndexMass_eq, PoolExpansion.firstIndexMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hactive : 0 < (trace.second.source i).physical.outerWeight ∧
      (trace.second.source i).physical.source.rows.Nonempty
  · rw [if_pos hactive]
    have h := mul_le_mul_of_nonneg_left
      (hmass call input large p trace htrace i (raw.covers.left i) (raw.covers.right i)
        (hraw i).1 (hraw i).2 hactive.1 hactive.2)
      (mul_nonneg (trace.expansion.indexPrefactor_nonneg i)
        (trace.second.source i).physical.firstCommonFactor_nonneg)
    apply h.trans_eq
    rw [← htrace.second.physical i]
    unfold PhysicalSource.firstIndexWeight PhysicalSource.firstCommonFactor
    ring
  · rw [if_neg hactive]
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg call.base_pos.le _))
      (mul_nonneg (trace.expansion.indexPrefactor_nonneg i)
        (trace.expansion.source i).firstIndexWeight_nonneg)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawCovers.supportedIndexMass_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_raw_index_reduction
