module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ScaleProduct
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedSupportPoolAtlas

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the first frozen ideal has the original complete pool valuation

The original Cauchy column has the selected first common extraction.
A pool error extracts its exact valuation from that residual ideal.
The realized occurrence cover records the same extraction tuple of the
same ancestor column, so its complete frozen product is precisely the
first common ideal times that pool power. Zero coefficients do not
enter this arithmetic identification.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private def columnFact (first : FirstCoordinates call) (j : call.workingRaw.Column)
    (I : (Arithmetic.data c).Exterior) : Prop :=
  j ∈ call.workingRaw.exteriorColumns ∧
    supportExtract (call.workingRaw.columnExterior j).val first.fullDeletion =
      first.selected.val * first.poolPower.val ∧
    I.val = supportResidual (call.workingRaw.columnExterior j).val first.fullDeletion

private def physicalColumnFacts (source : PhysicalSource call p) : Prop :=
  ∀ i ∈ source.source.columns, columnFact source.first (source.ancestor i) (source.source.ideal i)

/-- Transport only the original carrier and the original arithmetic
column functions; no coefficient or energy comparison is involved. -/
private theorem transportColumnFacts {α β : Type}
    (s : ActualGaussSource (Arithmetic.context c) α)
    (t : ActualGaussSource (Arithmetic.context c) β)
    (f : α → call.workingRaw.Column) (g : β → call.workingRaw.Column)
    (htype : α = β) (hsource : HEq s t) (hindex : HEq f g)
    (P : call.workingRaw.Column → (Arithmetic.data c).Exterior → Prop)
    (hP : ∀ j ∈ t.columns, P (g j) (t.ideal j)) :
    ∀ i ∈ s.columns, P (f i) (s.ideal i) := by
  cases htype
  cases eq_of_heq hsource
  cases eq_of_heq hindex
  exact hP

private theorem firstKey_column_facts {F : FirstPresentation call p}
    (hF : F.Realizes) (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : i ∈ key.data.columns) :
    F.index i ∈ call.workingRaw.exteriorColumns ∧
      supportExtract (call.workingRaw.columnExterior (F.index i)).val
          (primeSupport (if key.side then key.1.val.2 else key.1.val.1)) =
        (if key.side then key.1.val.2 else key.1.val.1) ∧
      (key.data.ideal i).val =
        supportResidual (call.workingRaw.columnExterior (F.index i)).val
          (primeSupport (if key.side then key.1.val.2 else key.1.val.1)) := by
  have hideal : (call.workingRaw.columnExterior (F.index i)).val =
      (F.source.ideal i).val := congrArg Subtype.val (hF.ideal i).symm
  cases hs : key.side with
  | false =>
    have hi' : i ∈ key.piece.leftData.columns := by
      simpa only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false] using hi
    rw [key.piece.left_columns] at hi'
    have hmem : F.index i ∈ call.workingRaw.exteriorColumns := by
      rw [← hF.columns]
      exact Finset.mem_map.mpr ⟨i, (Finset.mem_filter.mp hi').1, rfl⟩
    have hres : (key.piece.leftData.ideal i).val =
        supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) := by
      rw [key.piece.left_ideal]
      exact key.block.left_residual i
    simpa only [FirstCauchyKey.data, hs, Bool.false_eq_true, if_false, hideal] using
      And.intro hmem (And.intro (Finset.mem_filter.mp hi').2 hres)
  | true =>
    have hi' : i ∈ key.piece.rightData.columns := by
      simpa only [FirstCauchyKey.data, hs, if_true] using hi
    rw [key.piece.right_columns] at hi'
    have hmem : F.index i ∈ call.workingRaw.exteriorColumns := by
      rw [← hF.columns]
      exact Finset.mem_map.mpr ⟨i, (Finset.mem_filter.mp hi').1, rfl⟩
    have hres : (key.piece.rightData.ideal i).val =
        supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) := by
      rw [key.piece.right_ideal]
      exact key.block.right_residual i
    have hsupp := key.block.common_support_eq
    simpa only [FirstCauchyKey.data, hs, if_true, hideal, ← hsupp] using
      And.intro hmem (And.intro (Finset.mem_filter.mp hi').2 hres)

private theorem first_column_facts {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) : physicalColumnFacts (family.source i) := by
  apply transportColumnFacts (family.source i).source
    ((family.index i).data.directSource (family.index i).coefficient)
    (family.source i).ancestor (fun j => F.index j)
    (hfamily.column i) (hfamily.source i) (hfamily.ancestor i)
    (columnFact (family.source i).first)
  intro j hj
  have h := firstKey_column_facts hF (family.index i) j hj
  dsimp only [columnFact]
  rw [hfamily.deletion i, hfamily.selected i, hfamily.poolPower i]
  simpa only [unitExterior, mul_one, Ideal.mul_top, DirectGaussData.directSource] using h

private theorem pool_main_column_facts {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (pool : PoolPresentation family)
    (hpool : pool.Realizes) (i : Fin family.count) (source : PhysicalSource call p)
    (horigin : pool.MainOrigin i source)
    (hold : physicalColumnFacts (family.source i)) : physicalColumnFacts source := by
  rcases horigin with ⟨htype, hsource, hancestor, _, _, _, _, hfirst⟩
  apply transportColumnFacts source.source
    ((pool.data i).mainSource (family.source i).source.coefficient)
    source.ancestor (family.source i).ancestor htype hsource hancestor (columnFact source.first)
  have hcolumns : (pool.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hpool.original i)
  have hideal : (pool.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hpool.original i)
  intro j hj
  have hj' : j ∈ (family.source i).source.columns := hcolumns ▸ hj
  have h := hold j hj'
  dsimp only [columnFact] at h ⊢
  simpa only [hfirst, FirstGaussPoolData.mainSource, hideal] using h

private theorem pool_error_column_facts {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (pool : PoolPresentation family)
    (hpool : pool.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) (q : pool.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : pool.ErrorOrigin i q e source)
    (hold : physicalColumnFacts (family.source i)) : physicalColumnFacts source := by
  rcases horigin with ⟨htype, hsource, hancestor, _, _, _, _, hselected, _, _, _, _, _,
    hpower, _, _, hdeletion, _⟩
  apply transportColumnFacts source.source
    ((pool.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    source.ancestor (fun j => (family.source i).ancestor j.val)
    htype hsource hancestor (columnFact source.first)
  have hcolumns : (pool.data i).columns = (family.source i).source.columns :=
    congrArg ActualGaussSource.columns (hpool.original i)
  have hideal : (pool.data i).ideal = (family.source i).source.ideal :=
    congrArg ActualGaussSource.ideal (hpool.original i)
  intro j _
  have hj : j.val ∈ (family.source i).source.columns :=
    hcolumns ▸ (Finset.mem_filter.mp j.property).1
  obtain ⟨hmem, hextract, hresidual⟩ := hold j.val hj
  have hpower0 : (family.source i).first.poolPower.val = 1 := by
    rw [hfamily.poolPower i]
    change (⊤ : Ideal (𝓞 K)) = 1
    exact Ideal.one_eq_top.symm
  rw [hpower0, mul_one] at hextract
  have hν : MaskedQuotientCRT.primeExponent q.val
      ((family.source i).source.ideal j.val) = e.multiplicity := by
    simpa only [hideal] using (Finset.mem_filter.mp j.property).2
  dsimp only [columnFact]
  refine ⟨hmem, ?_, ?_⟩
  · rw [hdeletion, supportExtract_union_factor _
      (call.workingRaw.columnExterior ((family.source i).ancestor j.val)).property.1,
      hextract, ← hresidual, supportExtract_singleton_power]
    change (family.source i).first.selected.val * q.val.val.asIdeal ^
        MaskedQuotientCRT.primeExponent q.val ((family.source i).source.ideal j.val) = _
    rw [hν, hselected, hpower]
    rfl
  · change ((pool.data i).residualPresentation q.val e.multiplicity j).residual.val = _
    rw [((pool.data i).residualPresentation q.val e.multiplicity j).residual_eq_supportResidual,
      hideal, hresidual, supportResidual_twice, hdeletion]

private theorem expansion_column_facts {F : FirstPresentation call p}
    {family : FirstCauchyFamily F} (hF : F.Realizes) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) : physicalColumnFacts (expansion.source i) := by
  cases expansion with
  | direct => exact first_column_facts hF hfamily i
  | pooled pool count index source =>
    obtain ⟨_, hpool, horigin⟩ := hexpansion
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      exact pool_main_column_facts pool hpool (index i).1 (source i) hm
        (first_column_facts hF hfamily (index i).1)
    | inr qe =>
      have he : pool.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      exact pool_error_column_facts pool hpool hfamily (index i).1 qe.1 qe.2 (source i) he
        (first_column_facts hF hfamily (index i).1)

private theorem cover_frozen_ideal {source : PhysicalSource call p}
    (cover : OriginalCover source) (hcover : cover.Realizes)
    (hsource : physicalColumnFacts source) (a : cover.cover.labels) :
    frozenSourceIdeal (cover.first a).plainDivisor₁ (cover.first a).plainDivisor₂
        (cover.first a).keep (cover.first a).witness.2 =
      source.first.selected.val * source.first.poolPower.val := by
  obtain ⟨i, hi, hlabel⟩ := hcover.labels a
  obtain ⟨hancestor, hextract, _⟩ := hsource i hi
  have hkey : call.workingRaw.originalReindex.supportExtractionLabel
      source.first.fullDeletion (source.ancestor i) = (cover.first a).key := by
    rw [← hcover.label i hi, hlabel, hcover.first a]
  have hmem : source.ancestor i ∈
      (cover.first a).originalColumns.image call.workingRaw.originalReindex.index := by
    have hfibre := congrArg
      (fun S : Finset call.workingRaw.Column => source.ancestor i ∈ S)
      (call.workingRaw.originalReindex.supportExtractionLabel_fibre
        source.first.fullDeletion (cover.first a))
    simp only [Finset.mem_filter, Finset.mem_image] at hfibre
    exact Finset.mem_image.mpr (Eq.mp hfibre ⟨hancestor, hkey⟩)
  obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hmem
  rw [← hxi,
    call.workingRaw.originalReindex.ideal_product x ((cover.first a).original_subset hx),
    (cover.first a).extract_ideal x hx] at hextract
  exact (cover.first a).frozenSourceIdeal_eq.trans hextract

/-- This identity is determined by the original source trace and the
literal cover. In particular the three pool valuations retain their
complete powers, not merely the support radical. -/
theorem firstFrozenIdeal_eq {packet : RawLeafPacket call p}
    (hpacket : packet.Realizes) (side : Bool) :
    firstFrozenIdeal packet side =
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, hraw, rfl⟩
  have hphysical : physicalColumnFacts
      (trace.second.source (raw.index j).val.1.1).physical := by
    rw [htrace.second.physical]
    exact expansion_column_facts htrace.first htrace.cauchy trace.expansion
      htrace.expansion (raw.index j).val.1.1
  cases side
  · exact cover_frozen_ideal (raw.covers.left (raw.index j).val.1.1)
      (hraw (raw.index j).val.1.1).1 hphysical (raw.index j).val.1.2.2.2.1
  · exact cover_frozen_ideal (raw.covers.right (raw.index j).val.1.1)
      (hraw (raw.index j).val.1.1).2 hphysical (raw.index j).val.1.2.2.2.2.1

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.firstFrozenIdeal_eq
