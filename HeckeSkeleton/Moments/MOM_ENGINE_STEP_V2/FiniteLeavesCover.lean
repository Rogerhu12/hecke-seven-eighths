import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A common original-fibre constructor for the S6 covers

The direct, main and valuation sources have different column types.
Only their original ancestor map is used below.  Once its injectivity,
residual ideal and complete extraction fibres are established, one
construction supplies every field of `OriginalCover.Realizes`.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- Elementary original-column facts, before any second source or leaf
estimate. The saturation clause states that the actual source contains
the whole original occurrence fibre of each of its columns. -/
structure OriginalFibreInput (source : PhysicalSource call p) : Prop where
  maps : ∀ i ∈ source.source.columns,
    source.ancestor i ∈ call.workingRaw.exteriorColumns
  injective : Set.InjOn source.ancestor (source.source.columns : Set source.Column)
  residual : ∀ i ∈ source.source.columns,
    (source.source.ideal i).val =
      supportResidual (call.workingRaw.columnExterior (source.ancestor i)).val
        source.first.fullDeletion
  saturated : ∀ i ∈ source.source.columns,
    ∀ v ∈ call.workingRaw.exteriorColumns,
    call.workingRaw.originalReindex.supportExtractionLabel source.first.fullDeletion v =
      call.workingRaw.originalReindex.supportExtractionLabel source.first.fullDeletion
        (source.ancestor i) →
    ∃ j ∈ source.source.columns, source.ancestor j = v

namespace OriginalFibreInput

variable {source : PhysicalSource call p} (h : OriginalFibreInput source)

def label (i : source.Column) :=
  call.workingRaw.originalReindex.supportExtractionLabel source.first.fullDeletion
    (source.ancestor i)

def labels := source.source.columns.image (label (source := source))

def representative (a : labels (source := source)) : source.Column :=
  Classical.choose (Finset.mem_image.mp a.property)

theorem representative_spec (a : labels (source := source)) :
    representative a ∈ source.source.columns ∧ label (representative a) = a.val :=
  Classical.choose_spec (Finset.mem_image.mp a.property)

include h in
theorem label_mem (a : labels (source := source)) :
    a.val ∈ (childCartesianColumns call.workingRaw.originalPlain₁
      call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots).image
        (SupportCartesian.extractionKey source.first.fullDeletion) := by
  rw [← call.workingRaw.originalReindex.supportExtractionLabel_image
    source.first.fullDeletion]
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp a.property
  exact Finset.mem_image.mpr ⟨source.ancestor i, h.maps i hi, he⟩

def first (a : labels (source := source)) :
    SupportCartesianBranch call.workingRaw.originalPlain₁
      call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots
      source.first.fullDeletion :=
  SupportCartesianBranch.ofKey call.workingRaw.originalPlain₁_nonzero
    call.workingRaw.originalPlain₂_nonzero a.val (h.label_mem a)

theorem first_key (a : labels (source := source)) : (h.first a).key = a.val :=
  SupportCartesianBranch.ofKey_key _ _ _ _

theorem reconstructed_label (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns) :
    call.workingRaw.originalReindex.supportExtractionLabel source.first.fullDeletion
      (call.workingRaw.originalIndex ((h.first a).reconstruct x)) = a.val := by
  have hm := (h.first a).reconstruct_mem x hx
  rw [call.workingRaw.originalReindex.supportExtractionLabel_index
    source.first.fullDeletion _ ((h.first a).original_subset hm)]
  rw [(h.first a).originalColumns_eq_filter] at hm
  exact (Finset.mem_filter.mp hm).2.trans (h.first_key a)

theorem lift_exists (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns) :
    ∃ i ∈ source.source.columns,
      source.ancestor i = call.workingRaw.originalIndex ((h.first a).reconstruct x) := by
  apply h.saturated (representative a) (representative_spec a).1
  · exact call.workingRaw.originalIndex_mem _
      ((h.first a).original_subset ((h.first a).reconstruct_mem x hx))
  · exact (h.reconstructed_label a x hx).trans (representative_spec a).2.symm

def index (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card) : source.Column :=
  if hx : x ∈ (h.first a).residualColumns then
    Classical.choose (h.lift_exists a x hx)
  else representative a

theorem index_spec (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns) :
    h.index a x ∈ source.source.columns ∧
      source.ancestor (h.index a x) =
        call.workingRaw.originalIndex ((h.first a).reconstruct x) := by
  rw [index, dif_pos hx]
  exact Classical.choose_spec (h.lift_exists a x hx)

theorem index_maps (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns) :
    h.index a x ∈ source.source.columns.filter (fun i => label i = a.val) := by
  refine Finset.mem_filter.mpr ⟨(h.index_spec a x hx).1, ?_⟩
  change call.workingRaw.originalReindex.supportExtractionLabel
    source.first.fullDeletion (source.ancestor (h.index a x)) = a.val
  rw [(h.index_spec a x hx).2]
  exact h.reconstructed_label a x hx

theorem index_injective (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns)
    (y : AllocationColumn K (h.first a).keep.card)
    (hy : y ∈ (h.first a).residualColumns) (he : h.index a x = h.index a y) : x = y := by
  have ha := congrArg source.ancestor he
  rw [(h.index_spec a x hx).2, (h.index_spec a y hy).2] at ha
  have hr := call.workingRaw.originalReindex.injective
    ((h.first a).original_subset ((h.first a).reconstruct_mem x hx))
    ((h.first a).original_subset ((h.first a).reconstruct_mem y hy)) ha
  have hh := congrArg (h.first a).residual hr
  simpa only [(h.first a).residual_reconstruct x hx,
    (h.first a).residual_reconstruct y hy] using hh

theorem index_surjective (a : labels (source := source))
    (i : source.Column)
    (hi : i ∈ source.source.columns.filter (fun i => label i = a.val)) :
    ∃ x ∈ (h.first a).residualColumns, h.index a x = i := by
  have hi₀ := (Finset.mem_filter.mp hi).1
  let v := call.workingRaw.originalCoordinates (source.ancestor i)
  have hv : v ∈ (h.first a).originalColumns := by
    rw [(h.first a).originalColumns_eq_filter]
    refine Finset.mem_filter.mpr
      ⟨call.workingRaw.originalCoordinates_mem _ (h.maps i hi₀), ?_⟩
    have hl := call.workingRaw.originalReindex.supportExtractionLabel_index
      source.first.fullDeletion v
      (call.workingRaw.originalCoordinates_mem _ (h.maps i hi₀))
    rw [call.workingRaw.originalIndex_coordinates] at hl
    exact hl.symm.trans ((Finset.mem_filter.mp hi).2.trans (h.first_key a).symm)
  let x := (h.first a).residual v
  have hx : x ∈ (h.first a).residualColumns := (h.first a).residual_mem v hv
  refine ⟨x, hx, h.injective (h.index_spec a x hx).1 hi₀ ?_⟩
  rw [(h.index_spec a x hx).2, (h.first a).reconstruct_residual v hv,
    call.workingRaw.originalIndex_coordinates]

theorem index_ideal (a : labels (source := source))
    (x : AllocationColumn K (h.first a).keep.card)
    (hx : x ∈ (h.first a).residualColumns) :
    (source.source.ideal (h.index a x)).val = allocationColumnIdeal x := by
  rw [h.residual _ (h.index_spec a x hx).1, (h.index_spec a x hx).2,
    call.workingRaw.originalIndex_ideal_product _
      ((h.first a).original_subset ((h.first a).reconstruct_mem x hx)),
    (h.first a).residual_ideal _ ((h.first a).reconstruct_mem x hx),
    (h.first a).residual_reconstruct x hx]

def reindex (a : labels (source := source)) :
    CartesianSourceReindex
      (source.source.columns.filter (fun i => label i = a.val))
      source.source.ideal (h.first a).keep.card where
  plain₁ := SupportCartesian.plainResidual call.workingRaw.originalPlain₁
    source.first.fullDeletion (h.first a).plainExtract₁
  plain₂ := SupportCartesian.plainResidual call.workingRaw.originalPlain₂
    source.first.fullDeletion (h.first a).plainExtract₂
  slots j := SupportCartesian.primeLive
    (call.workingRaw.exteriorSlots (SlotRestriction.index (h.first a).keep j))
    source.first.fullDeletion
  index := h.index a
  maps := h.index_maps a
  injective := fun _ hx _ hy he => h.index_injective a _ hx _ hy he
  surjective := h.index_surjective a
  ideal_product := h.index_ideal a

def atlas (a : labels (source := source)) :
    SourceCartesianAtlas
      (source.source.columns.filter (fun i => label i = a.val)) source.source.ideal :=
  SourceCartesianAtlas.ofReindex (h.reindex a)
    ⟨representative a, Finset.mem_filter.mpr (representative_spec a)⟩

def cover : OriginalCover source where
  cover := {
    Label := SupportCartesian.ExtractionKey K call.localizedData.geometry.slotCount
    labels := labels (source := source)
    label := label (source := source)
    maps := fun i hi => Finset.mem_image_of_mem _ hi
    branch := h.atlas }
  label := Function.Embedding.refl _
  first := h.first

theorem cover_realizes : h.cover.Realizes where
  labels a := Finset.mem_image.mp a.property
  label _ _ := rfl
  first := h.first_key
  count _ := rfl
  plain₁ _ := rfl
  plain₂ _ := rfl
  slots _ := HEq.rfl
  index a x hx := (h.index_spec a x hx).2

include h in
theorem exists_cover : ∃ cover : OriginalCover source, cover.Realizes :=
  ⟨h.cover, h.cover_realizes⟩

end OriginalFibreInput
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves.OriginalFibreInput.exists_cover
