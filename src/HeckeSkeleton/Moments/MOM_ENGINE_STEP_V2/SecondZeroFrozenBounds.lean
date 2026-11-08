module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceCarrierBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroNormalization
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PoolContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original frozen divisor has a fixed norm exponent

Every residual first-Cauchy divisor divides an actual support residual
of an original right column. The complete original column carrier has
a uniform upper norm window, including coefficient-zero columns. This
gives the pool's frozen exponent before any moving pool is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum FirstZeroProof

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- The whole dictionary, without a nonzero-coefficient restriction,
fits this fixed norm box. -/
theorem first_complete_column_norm_le_five
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤ call.base ^ (5 : ℝ) := by
  apply (first_column_norm_le frame input hframe p.loss hannulusZ F hF i hi).trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
  linarith [p.loss_small]

private theorem first_residual_dvd_column (F : FirstPresentation call p)
    (key : FirstCauchyKey F) :
    ∃ j ∈ F.source.columns,
      (FirstCauchyKey.residual key).val ∣ (F.source.ideal j).val := by
  obtain ⟨j, hj, hS⟩ := Finset.mem_biUnion.mp (FirstCauchyKey.residual key).property
  have hd := (DedekindZetaZeroFree.LargeSieve.mem_idealDivisors
    ((FirstCauchyKey.piece key).rightData.ideal j).property.1).mp hS
  have hj' : j ∈ F.source.columns := by
    rw [(FirstCauchyKey.piece key).right_columns] at hj
    exact (Finset.mem_filter.mp hj).1
  refine ⟨j, hj', hd.trans ?_⟩
  have hideal : ((FirstCauchyKey.piece key).rightData.ideal j).val =
      supportResidual (F.source.ideal j).val (primeSupport key.1.val.1) :=
    (congrArg (fun f : F.source.Column → (Arithmetic.data c).Exterior => (f j).val)
      (FirstCauchyKey.piece key).right_ideal).trans ((FirstCauchyKey.block key).right_residual j)
  have hdiv : supportResidual (F.source.ideal j).val (primeSupport key.1.val.1) ∣
      (F.source.ideal j).val := by
    refine ⟨supportExtract (F.source.ideal j).val (primeSupport key.1.val.1), ?_⟩
    exact (support_reconstruct (F.source.ideal j).val (F.source.ideal j).property.1
      (primeSupport key.1.val.1)).symm.trans (mul_comm _ _)
  exact Eq.mp (congrArg (fun I : Ideal (𝓞 K) => I ∣ (F.source.ideal j).val)
    hideal.symm) hdiv

theorem first_key_residual_norm_le_five
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes) (key : FirstCauchyKey F) :
    (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ) ≤ call.base ^ (5 : ℝ) := by
  obtain ⟨j, hj, hdiv⟩ := first_residual_dvd_column F key
  exact (norm_le_of_dvd (F.source.ideal j).property.1 hdiv).trans
    (first_complete_column_norm_le_five frame input hframe hannulusZ F hF j hj)

theorem first_source_residual_norm_le_five
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes) (i : Fin family.count) :
    (Ideal.absNorm (family.source i).first.residualDivisor.val : ℝ) ≤
      call.base ^ (5 : ℝ) := by
  rw [hfamily.residual i]
  exact first_key_residual_norm_le_five frame input hframe hannulusZ F hF (family.index i)

/-- The actual nonzero frozen ideal, including all original residual
divisor labels, has logarithmic length at most five. -/
theorem first_source_residual_length_le_five
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes) (i : Fin family.count) :
    idealLogLength call.base (family.source i).first.residualDivisor.val ≤ 5 := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale _
    (nonZeroDivisors.coe_ne_zero (family.source i).first.residualDivisor)]
  exact first_source_residual_norm_le_five frame input hframe hannulusZ F hF family hfamily i

/-- Pool realization identifies this same original frozen ideal. No
row or coefficient nonvanishing assumption is needed. -/
theorem pool_frozenExponent_le
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes) (i : Fin family.count) :
    (P.data i).frozenExponent ≤ 5 := by
  rw [hP.frozenExponent i]
  exact first_source_residual_length_le_five frame input hframe hannulusZ F hF family hfamily i

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
