import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceCoverCounts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The first Cauchy sources retain their original extraction identities

The Cauchy-side choice changes which ordered common ideal is selected.
The two common ideals have the same prime support, so both choices use
the same original support-extraction operation.  Source-column and
ancestor identities are transported together across the public HEq
dictionary; no independent ideal or replacement column is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p}

namespace N8Source

/-- Transport one original-column property through the simultaneous
source/ancestor dictionary.  The source carrier is transported as well. -/
theorem transport_column_predicate {I J : Type}
    (G : ActualGaussSource (Arithmetic.context c) I)
    (H : ActualGaussSource (Arithmetic.context c) J)
    (ancestor : I → call.workingRaw.Column)
    (original : J → call.workingRaw.Column)
    (hI : I = J) (hG : HEq G H) (ha : HEq ancestor original)
    (P : call.workingRaw.Column → Prop)
    (hP : ∀ j ∈ H.columns, P (original j)) :
    ∀ i ∈ G.columns, P (ancestor i) := by
  subst J
  have hG' : G = H := eq_of_heq hG
  have ha' : ancestor = original := eq_of_heq ha
  subst H
  subst original
  exact hP

/-- The ideal and ancestor are transported by the same source equality. -/
theorem transport_ideal_dictionary {I J : Type}
    (G : ActualGaussSource (Arithmetic.context c) I)
    (H : ActualGaussSource (Arithmetic.context c) J)
    (ancestor : I → call.workingRaw.Column)
    (original : J → call.workingRaw.Column)
    (hI : I = J) (hG : HEq G H) (ha : HEq ancestor original)
    (P : call.workingRaw.Column → (Arithmetic.data c).Exterior → Prop)
    (hP : ∀ j, P (original j) (H.ideal j)) :
    ∀ i, P (ancestor i) (G.ideal i) := by
  subst J
  have hG' : G = H := eq_of_heq hG
  have ha' : ancestor = original := eq_of_heq ha
  subst H
  subst original
  exact hP

end N8Source

namespace FirstCauchyKey

variable (key : FirstCauchyKey F)

def selectedIdeal : Ideal (𝓞 K) :=
  if FirstCauchyKey.side key then key.1.val.2 else key.1.val.1

theorem common_support_eq : primeSupport key.1.val.1 = primeSupport key.1.val.2 :=
  commonSupportPool_support_eq _ _ _ _ _ key.1.property

theorem selected_support_eq :
    primeSupport key.selectedIdeal = primeSupport key.1.val.1 := by
  cases hs : FirstCauchyKey.side key <;>
    simp [selectedIdeal, hs, key.common_support_eq]

theorem data_columns_subset : (FirstCauchyKey.data key).columns ⊆ F.source.columns := by
  intro i hi
  cases hs : FirstCauchyKey.side key with
  | false =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).leftData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).left_columns] at hi
    exact (Finset.mem_filter.mp hi).1
  | true =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).rightData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).right_columns] at hi
    exact (Finset.mem_filter.mp hi).1

/-- The actual complete selected ideal is the extraction of every
source column, separately for either Cauchy orientation. -/
theorem data_columns_extract (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) :
    supportExtract (F.source.ideal i).val (primeSupport key.selectedIdeal) =
      key.selectedIdeal := by
  rw [key.selected_support_eq]
  cases hs : FirstCauchyKey.side key with
  | false =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).leftData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).left_columns] at hi
    simpa only [selectedIdeal, hs, Bool.false_eq_true, if_false] using
      (Finset.mem_filter.mp hi).2
  | true =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).rightData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).right_columns] at hi
    simpa only [selectedIdeal, hs, if_true] using (Finset.mem_filter.mp hi).2

theorem data_ideal_residual (i : F.source.Column) :
    ((FirstCauchyKey.data key).ideal i).val =
      supportResidual (F.source.ideal i).val (primeSupport key.selectedIdeal) := by
  rw [key.selected_support_eq]
  cases hs : FirstCauchyKey.side key with
  | false =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).leftData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).left_ideal]
    exact (FirstCauchyKey.block key).left_residual i
  | true =>
    have hd : FirstCauchyKey.data key = (FirstCauchyKey.piece key).rightData := by
      simp [FirstCauchyKey.data, hs]
    rw [hd, (FirstCauchyKey.piece key).right_ideal]
    exact (FirstCauchyKey.block key).right_residual i

theorem original_column_mem (hF : F.Realizes) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) :
    F.index i ∈ call.workingRaw.exteriorColumns := by
  rw [← hF.columns]
  exact Finset.mem_map.mpr ⟨i, key.data_columns_subset hi, rfl⟩

theorem original_column_extract (hF : F.Realizes) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) :
    supportExtract (call.workingRaw.columnExterior (F.index i)).val
      (primeSupport key.selectedIdeal) = key.selectedIdeal := by
  rw [← hF.ideal i]
  exact key.data_columns_extract i hi

end FirstCauchyKey

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

/-- Every actual first physical column belongs to the original parent
and has precisely the recorded complete common extraction. -/
theorem original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (i : Fin family.count) (j : (family.source i).Column)
    (hj : j ∈ (family.source i).source.columns) :
    (family.source i).ancestor j ∈ call.workingRaw.exteriorColumns ∧
      supportExtract
        (call.workingRaw.columnExterior ((family.source i).ancestor j)).val
        (family.source i).first.fullDeletion = (family.source i).first.selected.val := by
  let key := family.index i
  have h := N8Source.transport_column_predicate
    (family.source i).source
    ((FirstCauchyKey.data key).directSource (FirstCauchyKey.coefficient key))
    (family.source i).ancestor (fun x : F.source.Column => F.index x)
    (hf.column i) (hf.source i) (hf.ancestor i)
    (fun x => x ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior x).val
        (primeSupport key.selectedIdeal) = key.selectedIdeal)
    (fun x hx => ⟨key.original_column_mem hF x hx,
      key.original_column_extract hF x hx⟩) j hj
  refine ⟨h.1, ?_⟩
  rw [hf.deletion i, hf.selected i]
  exact h.2

theorem original_ideal_residual (hF : F.Realizes) (hf : family.Realizes)
    (i : Fin family.count) (j : (family.source i).Column) :
    ((family.source i).source.ideal j).val =
      supportResidual
        (call.workingRaw.columnExterior ((family.source i).ancestor j)).val
        (family.source i).first.fullDeletion := by
  let key := family.index i
  have h := N8Source.transport_ideal_dictionary
    (family.source i).source
    ((FirstCauchyKey.data key).directSource (FirstCauchyKey.coefficient key))
    (family.source i).ancestor (fun x : F.source.Column => F.index x)
    (hf.column i) (hf.source i) (hf.ancestor i)
    (fun x I => I.val = supportResidual (call.workingRaw.columnExterior x).val
      (primeSupport key.selectedIdeal))
    (fun x => by
      change ((FirstCauchyKey.data key).ideal x).val = _
      rw [← hF.ideal x]
      exact key.data_ideal_residual x) j
  rw [hf.deletion i, hf.selected i]
  exact h

/-- The first unamplified cover therefore has the literal common-ideal
divisor count.  This is the direct entrance needed by the zero-slot case. -/
theorem original_cover_card_le (hF : F.Realizes) (hf : family.Realizes)
    (i : Fin family.count) (cover : OriginalCover (family.source i))
    (hcover : cover.Realizes) :
    cover.cover.labels.card ≤
      (idealDivisors (family.source i).first.selected.val).card ^ (c.geometry.slots + 2) := by
  apply cover.labels_card_le_divisorPower hcover _
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
  · intro j hj
    exact (family.original_columns_extract hF hf i j hj).1
  · intro j hj
    exact (family.original_columns_extract hF hf i j hj).2

end FirstCauchyFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.original_columns_extract
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.original_cover_card_le
