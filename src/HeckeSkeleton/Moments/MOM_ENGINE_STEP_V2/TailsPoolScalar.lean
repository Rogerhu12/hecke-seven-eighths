module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsPoolCounting
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsCauchyGeometry

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original pool outer scalar

The physical row windows bound the exponent used by the one original
pool. Its exact density and multiplicity then bound every main or error
outer scalar by the same fixed constant times its first-family scalar.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem physical_rpow_rowExponent (source : PhysicalSource call p) :
    call.base ^ source.rowExponent = source.rowSize := by
  have hsize : 1 ≤ source.rowSize := le_max_left _ _
  have hlog : Real.log call.base ≠ 0 := (Real.log_pos call.domain.scale).ne'
  have he : Real.log call.base *
      (Real.log source.rowSize / Real.log call.base) = Real.log source.rowSize := by
    field_simp [hlog]
  rw [PhysicalSource.rowExponent, Real.rpow_def_of_pos call.base_pos, he,
    Real.exp_log (zero_lt_one.trans_le hsize)]

theorem physical_rowExponent_le (source : PhysicalSource call p)
    (degree : ℝ) (hdegree : 0 ≤ degree)
    (hnorm : ∀ h ∈ source.source.rows,
      (Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h) ≤ call.base ^ degree) :
    source.rowExponent ≤ degree := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [physical_rpow_rowExponent]
  apply max_le (Real.one_le_rpow call.domain.scale.le hdegree)
  let bound : NNReal := ⟨call.base ^ degree, Real.rpow_nonneg call.base_pos.le degree⟩
  have hsup : source.source.rows.sup (fun h =>
      (⟨(Arithmetic.data c).exteriorNorm (originalFrequencyIdeal h),
        ((Arithmetic.data c).exteriorNorm_pos (originalFrequencyIdeal h)).le⟩ : NNReal)) ≤
      bound := by
    apply Finset.sup_le
    intro h hh
    exact hnorm h hh
  exact_mod_cast hsup

theorem first_family_rowExponent_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) (hw : (family.source i).Windows) :
    (family.source i).rowExponent ≤ firstRowExponent c p + recipeInductionSigma c := by
  apply physical_rowExponent_le _ _
    (add_nonneg (firstRowExponent_nonneg c p) (recipeInduction_budget (c := c)).1.le)
  intro h hh
  calc
    _ ≤ (family.source i).first.retainedScale *
        call.base ^ (family.source i).first.tag.padding (recipeInductionSigma c) :=
      hw.row_upper h hh
    _ = (family.source i).first.retainedScale * call.base ^ recipeInductionSigma c := by
      rw [hf.tag i]
      rfl
    _ ≤ call.base ^ firstRowExponent c p * call.base ^ recipeInductionSigma c :=
      mul_le_mul_of_nonneg_right (first_family_retained_le F hF family hf input hlarge i)
        (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := (Real.rpow_add call.base_pos _ _).symm

def poolOuterFactor (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  4 * max 1 (poolMultiplicityBound c (firstRowExponent c p + recipeInductionSigma c))

theorem poolOuterFactor_one_le (c : TargetContext K) (p : SourceParameters c) :
    1 ≤ poolOuterFactor c p := by
  have h : (1 : ℝ) ≤ max 1
      (poolMultiplicityBound c (firstRowExponent c p + recipeInductionSigma c)) :=
    le_max_left _ _
  unfold poolOuterFactor
  linarith

theorem poolOuterFactor_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ poolOuterFactor c p := zero_le_one.trans (poolOuterFactor_one_le c p)

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem pool_origin_outer_le (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (horigin : P.Origin index source)
    (hrow : (family.source index.1).rowExponent ≤
      firstRowExponent c p + recipeInductionSigma c) :
    source.outerWeight ≤ (family.source index.1).outerWeight * poolOuterFactor c p := by
  rcases index with ⟨i, u | ⟨q, e⟩⟩
  · rcases horigin with ⟨_, _, _, _, _, _, hout, _⟩
    rw [hout, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (family.source i).outerWeight_nonneg
    unfold poolOuterFactor
    exact mul_le_mul (pool_density_factor_le P hP i)
      ((pool_multiplicity_le P hP i _ hrow).trans (le_max_right _ _))
      (P.data i).multiplicity_nonneg (by norm_num)
  · rcases horigin with ⟨_, _, _, _, _, _, hout, _⟩
    rw [hout, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (family.source i).outerWeight_nonneg
    unfold poolOuterFactor
    exact mul_le_mul (pool_density_factor_le P hP i)
      ((localErrorWeight_le_one q.val e.multiplicity).trans (le_max_left _ _))
      (FirstGaussPoolData.localErrorWeight_nonneg q.val e.multiplicity) (by norm_num)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_rowExponent_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.pool_origin_outer_le
