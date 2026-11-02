import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact second-divisor weights on the original raw index

The lower endpoint may be the actual logarithmic norm of the retained
inner divisor. Its exceptional weight is then exactly the N8a weight,
with no new family or extra divisor multiplicity. All positivity facts
come from the original pool and its actual divisor carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolExpansion

theorem t3b_indexPrefactor_nonneg (expansion : PoolExpansion family)
    (i : Fin expansion.count) : 0 ≤ expansion.indexPrefactor i := by
  cases expansion with
  | direct => exact zero_le_one
  | pooled pool count index source =>
    dsimp only [indexPrefactor]
    apply mul_nonneg
      (div_nonneg (by norm_num) (pool.data (index i).1).density_pos.le)
    cases h : (index i).2 with
    | inl u =>
      exact mul_nonneg (pool.data (index i).1).multiplicity_nonneg
        (Real.rpow_nonneg call.base_pos.le _)
    | inr qe =>
      exact mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg _ _)
        (pow_nonneg (by
          change (0 : ℝ) ≤ (Ideal.absNorm qe.1.val.val.asIdeal : ℝ)
          positivity) _)

end PoolExpansion

namespace RawFamily

variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

theorem t3b_innerDivisor_ne_zero (j : Fin raw.count) : raw.innerDivisor j ≠ 0 := by
  have hmem := (raw.packet j).allocation.1.property
  simp only [MOMInvStep.FullMobius.divisorPool] at hmem
  obtain ⟨x, hx, hdiv⟩ := Finset.mem_biUnion.mp hmem
  exact LargeSieve.ne_bot_of_mem_idealDivisors hdiv

theorem t3b_innerDivisor_norm_pos (j : Fin raw.count) :
    0 < (Ideal.absNorm (raw.innerDivisor j) : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (raw.t3b_innerDivisor_ne_zero j)))

theorem t3b_innerDivisor_length_nonneg (j : Fin raw.count) :
    0 ≤ idealLogLength call.base (raw.innerDivisor j) :=
  idealLogLength_nonneg call.base call.domain.scale _
    (raw.t3b_innerDivisor_ne_zero j)

theorem t3b_commonIndexFactor_nonneg (j : Fin raw.count) :
    0 ≤ raw.commonIndexFactor j := by
  unfold commonIndexFactor
  positivity

theorem t3b_indexWeight_nonneg (j : Fin raw.count) : 0 ≤ raw.indexWeight j :=
  div_nonneg
    (mul_nonneg (expansion.t3b_indexPrefactor_nonneg _)
      (raw.t3b_commonIndexFactor_nonneg j)) (Nat.cast_nonneg _)

theorem t3b_indexMass_nonneg : 0 ≤ raw.indexMass :=
  Finset.sum_nonneg (fun j _ => raw.t3b_indexWeight_nonneg j)

theorem t3b_exceptionalDyadWeight_nonneg (lower : ℝ) (j : Fin raw.count) :
    0 ≤ raw.exceptionalDyadWeight lower j :=
  mul_nonneg
    (mul_nonneg (expansion.t3b_indexPrefactor_nonneg _)
      (raw.t3b_commonIndexFactor_nonneg j))
    (Real.rpow_nonneg call.base_pos.le _)

/-- The retained divisor is used at its own exact norm length. -/
theorem t3b_exceptionalDyadWeight_actual_length (j : Fin raw.count) :
    raw.exceptionalDyadWeight
      (idealLogLength call.base (raw.innerDivisor j)) j = raw.indexWeight j := by
  simp only [exceptionalDyadWeight, indexWeight, Real.rpow_neg call.base_pos.le,
    rpow_idealLogLength call.base call.domain.scale _
      (raw.t3b_innerDivisor_ne_zero j), div_eq_mul_inv]

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
