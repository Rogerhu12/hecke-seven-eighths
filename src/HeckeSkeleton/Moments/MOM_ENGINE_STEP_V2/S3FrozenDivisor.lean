import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S3PoolData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The frozen divisor is a divisor of an original column

This exact divisibility transports a uniform bound on the original
finite column carrier to every residual divisor, including labels with
zero coefficient. No nonzero-coefficient condition is introduced.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open EngineStep EngineInduction.Source
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

theorem residual_dvd_original_column (key : FirstCauchyKey F) :
    ∃ j ∈ F.source.columns,
      (FirstCauchyKey.residual key).val ∣ (F.source.ideal j).val := by
  obtain ⟨j, hj, hdivisor⟩ := Finset.mem_biUnion.mp
    (FirstCauchyKey.residual key).property
  have hd := (mem_idealDivisors
    ((FirstCauchyKey.piece key).rightData.ideal j).property.1).mp hdivisor
  rw [(FirstCauchyKey.piece key).right_columns] at hj
  let b := FirstCauchyKey.block key
  have hideal : ((FirstCauchyKey.piece key).rightData.ideal j).val =
      (b.rightResidual j).val :=
    congrArg (fun I : (Arithmetic.data c).Exterior => I.val)
      (congrFun (FirstCauchyKey.piece key).right_ideal j)
  refine ⟨j, (Finset.mem_filter.mp hj).1,
    hd.trans ⟨(primePowerProduct b.primes b.rightMultiplicity).val, ?_⟩⟩
  calc
    (F.source.ideal j).val =
        (primePowerProduct b.primes b.rightMultiplicity).val * (b.rightResidual j).val :=
      b.right_reconstruct F.source.columns j hj
    _ = (primePowerProduct b.primes b.rightMultiplicity).val *
        ((FirstCauchyKey.piece key).rightData.ideal j).val :=
      congrArg (fun I : Ideal (𝓞 K) =>
        (primePowerProduct b.primes b.rightMultiplicity).val * I) hideal.symm
    _ = _ := mul_comm _ _

theorem residual_norm_le (key : FirstCauchyKey F) (B : ℝ)
    (columns : ∀ j ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal j) ≤ call.base ^ B) :
    (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ) ≤ call.base ^ B := by
  obtain ⟨j, hj, hd⟩ := residual_dvd_original_column key
  exact (norm_le_of_dvd (F.source.ideal j).property.1 hd).trans (columns j hj)

theorem frozen_exponent_le {family : FirstCauchyFamily F}
    (realized : family.Realizes) (i : Fin family.count) (B : ℝ)
    (columns : ∀ j ∈ F.source.columns,
      (Arithmetic.data c).exteriorNorm (F.source.ideal j) ≤ call.base ^ B) :
    idealLogLength call.base (family.source i).first.residualDivisor.val ≤ B := by
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  rw [rpow_idealLogLength call.base call.domain.scale _
    (nonZeroDivisors.coe_ne_zero (family.source i).first.residualDivisor),
    realized.residual i]
  exact residual_norm_le (family.index i) B columns

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.residual_dvd_original_column
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S3.frozen_exponent_le
