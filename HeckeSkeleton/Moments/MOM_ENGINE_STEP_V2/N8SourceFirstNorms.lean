import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceResidualWindows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! The complete first common pair and its independent residual divisor
are bounded by the same original column window. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

namespace FirstCauchyKey

variable (key : FirstCauchyKey F)

theorem common_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base) (hF : F.Realizes) :
    (Ideal.absNorm key.1.val.1 : ℝ) ≤ call.base ^ N8Source.columnExponent c ∧
      (Ideal.absNorm key.1.val.2 : ℝ) ≤ call.base ^ N8Source.columnExponent c :=
  N8Source.commonSupportPool_norm _ _ _ _
    (fun i _ => (F.source.ideal i).property.1)
    (fun i _ => (F.source.ideal i).property.1) _
    (N8Source.first_source_norm input large F hF)
    (N8Source.first_source_norm input large F hF) _ key.1.property

theorem rightResidual_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base) (hF : F.Realizes)
    (j : F.source.Column) (hj : j ∈ (FirstCauchyKey.piece key).rightData.columns) :
    (Arithmetic.data c).exteriorNorm ((FirstCauchyKey.piece key).rightData.ideal j) ≤
      call.base ^ N8Source.columnExponent c := by
  have hj' : j ∈ F.source.columns := by
    rw [(FirstCauchyKey.piece key).right_columns] at hj
    exact (Finset.mem_filter.mp hj).1
  change (Ideal.absNorm ((FirstCauchyKey.piece key).rightData.ideal j).val : ℝ) ≤ _
  rw [(FirstCauchyKey.piece key).right_ideal,
    (FirstCauchyKey.block key).right_residual]
  exact (norm_le_of_dvd (F.source.ideal j).property.1
    (N8Source.supportResidual_dvd_original _ (F.source.ideal j).property.1 _)).trans
      (N8Source.first_source_norm input large F hF j hj')

theorem residual_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base) (hF : F.Realizes) :
    (Ideal.absNorm (FirstCauchyKey.residual key).val : ℝ) ≤
      call.base ^ N8Source.columnExponent c := by
  obtain ⟨j, hj, hDj⟩ := Finset.mem_biUnion.mp (FirstCauchyKey.residual key).property
  have hJ := ((FirstCauchyKey.piece key).rightData.ideal j).property.1
  exact (norm_le_of_dvd hJ ((mem_idealDivisors hJ).mp hDj)).trans
    (key.rightResidual_norm input large hF j hj)

end FirstCauchyKey

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

theorem selected_opposite_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count) :
    (Ideal.absNorm (family.source i).first.selected.val : ℝ) ≤
        call.base ^ N8Source.columnExponent c ∧
      (Ideal.absNorm (family.source i).first.opposite.val : ℝ) ≤
        call.base ^ N8Source.columnExponent c := by
  have h := (family.index i).common_norm input large hF
  rw [hf.selected i, hf.opposite i]
  cases hs : FirstCauchyKey.side (family.index i) <;>
    simp only [hs, Bool.false_eq_true, if_false, if_true]
  · exact h
  · exact h.symm

theorem residual_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count) :
    (Ideal.absNorm (family.source i).first.residualDivisor.val : ℝ) ≤
      call.base ^ N8Source.columnExponent c := by
  rw [hf.residual i]
  exact (family.index i).residual_norm input large hF

end FirstCauchyFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.selected_opposite_norm
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.residual_norm
