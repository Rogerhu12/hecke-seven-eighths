import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceOuterLedger

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! The original main length and moving valuation power are precisely
the factors already present in the fixed source index prefactor. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem origin_scalar_coordinates (j : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin j source) :
    source.first.selected = (family.source j.1).first.selected ∧
      source.first.opposite = (family.source j.1).first.opposite ∧
      source.first.complementary = (family.source j.1).first.complementary ∧
      source.first.residualDivisor = (family.source j.1).first.residualDivisor := by
  rcases j with ⟨i, branch⟩
  cases branch with
  | inl u =>
    rcases horigin with ⟨_, _, _, _, _, _, _, hfirst⟩
    rw [hfirst]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | inr qe =>
    rcases horigin with
      ⟨_, _, _, _, _, _, _, hselected, hopposite, hcomplementary, hresidual, _, _, _, _, _, _, _⟩
    exact ⟨hselected, hopposite, hcomplementary, hresidual⟩

theorem indexPrefactor_nonneg (j : pool.Index) : 0 ≤ pool.indexPrefactor j := by
  unfold indexPrefactor
  apply mul_nonneg (div_nonneg (by norm_num) (pool.data j.1).density_pos.le)
  cases j.2 with
  | inl u =>
    exact mul_nonneg (pool.data j.1).multiplicity_nonneg
      (Real.rpow_nonneg call.base_pos.le _)
  | inr qe =>
    exact mul_nonneg (FirstGaussPoolData.localErrorWeight_nonneg _ _)
      (pow_nonneg (by change (0 : ℝ) ≤ (Ideal.absNorm qe.1.val.val.asIdeal : ℝ); positivity) _)

theorem outer_mul_poolIndexAllowance (j : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin j source) :
    source.outerWeight * source.poolIndexAllowance =
      (family.source j.1).outerWeight * pool.indexPrefactor j := by
  rcases j with ⟨i, branch⟩
  cases branch with
  | inl u =>
    rcases horigin with ⟨_, _, _, _, _, _, houter, hfirst⟩
    unfold PhysicalSource.poolIndexAllowance
    rw [houter, hfirst]
    simp only [OriginalNominalTag.poolLength, OriginalNominalTag.movingLength,
      zero_add, PoolPresentation.indexPrefactor]
    ring
  | inr qe =>
    rcases horigin with
      ⟨_, _, _, _, _, _, houter, _, _, _, _, _, _, _, _, htag, _, _⟩
    have hmoving : call.base ^ ((qe.2.movingMultiplicity : ℝ) *
        idealLogLength call.base qe.1.val.val.asIdeal) =
          Q qe.1.val ^ qe.2.movingMultiplicity := by
      rw [mul_comm, Real.rpow_mul call.base_pos.le,
        rpow_idealLogLength call.base call.domain.scale _ qe.1.val.val.ne_bot,
        Real.rpow_natCast]
      rfl
    unfold PhysicalSource.poolIndexAllowance
    rw [houter, htag]
    simp only [OriginalNominalTag.poolLength, OriginalNominalTag.movingLength,
      add_zero, hmoving, PoolPresentation.indexPrefactor]
    ring

theorem first_ledger_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes)
    (j : pool.Index) (source : PhysicalSource call p) (horigin : pool.Origin j source) :
    source.outerWeight * call.base ^ source.firstLedgerExponent ≤
      orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        pool.indexPrefactor j * source.firstCommonFactor := by
  obtain ⟨hsel, hopp, hcomp, hres⟩ := pool.origin_scalar_coordinates j source horigin
  have hexp : source.firstBaseExponent = (family.source j.1).firstBaseExponent := by
    unfold PhysicalSource.firstBaseExponent
    rw [hsel, hopp, hcomp]
  have hfactor : source.firstCommonFactor = (family.source j.1).firstCommonFactor := by
    unfold PhysicalSource.firstCommonFactor
    rw [hsel, hopp, hres]
  calc
    _ = (source.outerWeight * source.poolIndexAllowance) *
        call.base ^ source.firstBaseExponent := by rw [source.firstLedgerPower_eq]; ring
    _ = ((family.source j.1).outerWeight * call.base ^
        (family.source j.1).firstBaseExponent) * pool.indexPrefactor j := by
      rw [pool.outer_mul_poolIndexAllowance j source horigin, hexp]
      ring
    _ ≤ (orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        (family.source j.1).firstCommonFactor) * pool.indexPrefactor j :=
      mul_le_mul_of_nonneg_right (family.first_base_ledger_le input large hF hf j.1)
        (pool.indexPrefactor_nonneg j)
    _ = _ := by rw [hfactor]; ring

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

theorem first_ledger_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (hexp : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).outerWeight * call.base ^ (expansion.source i).firstLedgerExponent ≤
      orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        expansion.indexPrefactor i * (expansion.source i).firstCommonFactor := by
  cases expansion with
  | direct =>
    have he : (family.source i).firstLedgerExponent = (family.source i).firstBaseExponent := by
      unfold PhysicalSource.firstLedgerExponent
      rw [hf.tag i]
      simp only [OriginalNominalTag.movingLength, OriginalNominalTag.poolLength, add_zero]
    simpa only [PoolExpansion.source, PoolExpansion.indexPrefactor, he, mul_one] using
      family.first_base_ledger_le input large hF hf i
  | pooled pool count index source =>
    exact pool.first_ledger_le input large hF hf (index i) (source i) (hexp.2.2 i)

end PoolExpansion
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.first_ledger_le
