import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceFirstExtraction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original support extraction through the one prime pool

The main source keeps the first extraction.  An error source removes
exactly its own prime power from the residual ideal, so its original
extraction is the product of that first extraction and the same prime
power.  These equalities follow from the valuation subtype and the
source dictionaries and include the actual original-column ancestor.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
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
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem data_columns_eq (hpool : pool.Realizes) (i : Fin family.count) :
    (pool.data i).columns = (family.source i).source.columns :=
  congrArg (fun G => G.columns) (hpool.original i)

theorem data_ideal_eq (hpool : pool.Realizes) (i : Fin family.count)
    (j : (family.source i).Column) :
    (pool.data i).ideal j = (family.source i).source.ideal j :=
  congrArg (fun G => G.ideal j) (hpool.original i)

theorem main_original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : Fin family.count) (source : PhysicalSource call p)
    (horigin : pool.MainOrigin i source)
    (j : source.Column) (hj : j ∈ source.source.columns) :
    source.ancestor j ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior (source.ancestor j)).val
        source.first.fullDeletion = source.first.selected.val * source.first.poolPower.val := by
  rcases horigin with ⟨hcol, hsource, ha, _, _, _, _, hfirst⟩
  have h := N8Source.transport_column_predicate source.source
    ((pool.data i).mainSource (family.source i).source.coefficient)
    source.ancestor (family.source i).ancestor hcol hsource ha
    (fun x => x ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior x).val
        (family.source i).first.fullDeletion = (family.source i).first.selected.val)
    (fun x hx => by
      change x ∈ (pool.data i).columns at hx
      rw [pool.data_columns_eq hpool i] at hx
      exact family.original_columns_extract hF hf i x hx) j hj
  refine ⟨h.1, ?_⟩
  rw [hfirst]
  change supportExtract (call.workingRaw.columnExterior (source.ancestor j)).val
    (family.source i).first.fullDeletion =
      (family.source i).first.selected.val * (family.source i).first.poolPower.val
  rw [hf.poolPower i]
  simpa only [unitExterior, mul_one] using h.2

theorem error_original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : Fin family.count) (q : pool.pool.primes)
    (e : AmplifierValuation) (source : PhysicalSource call p)
    (horigin : pool.ErrorOrigin i q e source)
    (j : source.Column) (hj : j ∈ source.source.columns) :
    source.ancestor j ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior (source.ancestor j)).val
        source.first.fullDeletion = source.first.selected.val * source.first.poolPower.val := by
  rcases horigin with
    ⟨hcol, hsource, ha, _, _, _, _, hselected, _, _, _, _, _, hpower, _, _, hdeletion, _⟩
  have h := N8Source.transport_column_predicate source.source
    ((pool.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    source.ancestor (fun x : (pool.data i).valuationColumns q.val e.multiplicity =>
      (family.source i).ancestor x.val) hcol hsource ha
    (fun x => x ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior x).val
        ((family.source i).first.fullDeletion ∪ {q.val.val.asIdeal}) =
          (family.source i).first.selected.val * q.val.val.asIdeal ^ e.multiplicity)
    (fun x _ => by
      have hx : x.val ∈ (family.source i).source.columns := by
        rw [← pool.data_columns_eq hpool i]
        exact (Finset.mem_filter.mp x.property).1
      have hbase := family.original_columns_extract hF hf i x.val hx
      refine ⟨hbase.1, ?_⟩
      have hres : ((pool.data i).ideal x.val).val =
          supportResidual
            (call.workingRaw.columnExterior ((family.source i).ancestor x.val)).val
            (family.source i).first.fullDeletion := by
        rw [pool.data_ideal_eq hpool i x.val]
        exact family.original_ideal_residual hF hf i x.val
      rw [supportExtract_union_factor _
        (call.workingRaw.columnExterior ((family.source i).ancestor x.val)).property.1,
        hbase.2, ← hres, supportExtract_singleton_power]
      change (family.source i).first.selected.val *
        q.val.val.asIdeal ^ MaskedQuotientCRT.primeExponent q.val ((pool.data i).ideal x.val) = _
      rw [(Finset.mem_filter.mp x.property).2]) j hj
  refine ⟨h.1, ?_⟩
  rw [hdeletion, hselected, hpower]
  exact h.2

theorem original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin i source)
    (j : source.Column) (hj : j ∈ source.source.columns) :
    source.ancestor j ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior (source.ancestor j)).val
        source.first.fullDeletion = source.first.selected.val * source.first.poolPower.val := by
  rcases i with ⟨i, branch⟩
  cases branch with
  | inl u => exact pool.main_original_columns_extract hF hf hpool i source horigin j hj
  | inr qe => exact pool.error_original_columns_extract hF hf hpool i qe.1 qe.2 source horigin j hj

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

/-- The direct and pooled alternatives have one original extraction
formula, with the actual pool power equal to one in the direct case. -/
theorem original_columns_extract (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count)
    (j : (expansion.source i).Column)
    (hj : j ∈ (expansion.source i).source.columns) :
    (expansion.source i).ancestor j ∈ call.workingRaw.exteriorColumns ∧
      supportExtract
        (call.workingRaw.columnExterior ((expansion.source i).ancestor j)).val
        (expansion.source i).first.fullDeletion =
          (expansion.source i).first.selected.val * (expansion.source i).first.poolPower.val := by
  cases expansion with
  | direct =>
    have h := family.original_columns_extract hF hf i j hj
    refine ⟨h.1, ?_⟩
    change supportExtract
      (call.workingRaw.columnExterior ((family.source i).ancestor j)).val
      (family.source i).first.fullDeletion =
        (family.source i).first.selected.val * (family.source i).first.poolPower.val
    rw [hf.poolPower i]
    simpa only [unitExterior, mul_one] using h.2
  | pooled pool count index source =>
    exact pool.original_columns_extract hF hf hexpansion.2.1
      (index i) (source i) (hexpansion.2.2 i) j hj

/-- The full prime power is charged only as part of its same combined
occurrence extraction; it creates no extra prime-pool copy. -/
theorem original_cover_card_le (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count)
    (cover : OriginalCover (expansion.source i)) (hcover : cover.Realizes) :
    cover.cover.labels.card ≤
      (idealDivisors ((expansion.source i).first.selected.val *
        (expansion.source i).first.poolPower.val)).card ^ (c.geometry.slots + 2) := by
  apply cover.labels_card_le_divisorPower hcover _
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero (expansion.source i).first.selected)
      (expansion.source i).first.poolPower.property.1)
  · intro j hj
    exact (expansion.original_columns_extract hF hf hexpansion i j hj).1
  · intro j hj
    exact (expansion.original_columns_extract hF hf hexpansion i j hj).2

end PoolExpansion
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.original_columns_extract
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.original_cover_card_le
