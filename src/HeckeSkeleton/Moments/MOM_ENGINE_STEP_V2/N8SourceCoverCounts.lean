module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceIndexBasic
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoverCardinality

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Counting the actual first cover labels in N8a

The public cover contract identifies every label with an original
occurrence-extraction tuple.  The image equality below derives the
finite count from that dictionary.  The subsequent divisor bound uses
only the original per-column extraction identity and the existing
slot cap; there is no assumed bound on a cover's cardinality.
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

namespace OriginalCover

variable {source : PhysicalSource call p} (cover : OriginalCover source)

/-- Every remaining branch slot is an actual surviving original slot. -/
theorem branch_slotCount_le (hcover : cover.Realizes) (a : cover.cover.labels) :
    (cover.cover.branch a).slotCount ≤ c.geometry.slots := by
  calc
    _ = (cover.first a).keep.card := (hcover.count a).symm
    _ ≤ call.localizedData.geometry.slotCount := by
      simpa only [Fintype.card_fin] using
        (Finset.card_le_univ (cover.first a).keep)
    _ = call.node.data.geometry.slotCount := rfl
    _ ≤ c.geometry.slots := call.slots_le

/-- The exact image of the source's actual cover labels. -/
theorem label_image_eq (hcover : cover.Realizes) :
    cover.cover.labels.image cover.label = source.source.columns.image
      (fun i => call.workingRaw.originalReindex.supportExtractionLabel
        source.first.fullDeletion (source.ancestor i)) := by
  ext key
  constructor
  · intro hkey
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hkey
    obtain ⟨i, hi, hlabel⟩ := hcover.labels ⟨a, ha⟩
    apply Finset.mem_image.mpr
    refine ⟨i, hi, ?_⟩
    rw [← hcover.label i hi, hlabel]
  · intro hkey
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_image.mpr
      ⟨cover.cover.label i, cover.cover.maps i hi, hcover.label i hi⟩

/-- The actual cover image embeds into the original parent's fixed
common-ideal extraction carrier. -/
theorem label_image_subset_originalAtlas (hcover : cover.Realizes)
    (D : Ideal (𝓞 K))
    (hcolumns : ∀ i ∈ source.source.columns,
      source.ancestor i ∈ call.workingRaw.exteriorColumns)
    (hextract : ∀ i ∈ source.source.columns,
      supportExtract (call.workingRaw.columnExterior (source.ancestor i)).val
        source.first.fullDeletion = D) :
    cover.cover.labels.image cover.label ⊆
      call.workingRaw.originalAtlas.labels source.first.fullDeletion D := by
  rw [cover.label_image_eq hcover]
  intro key hkey
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkey
  apply Finset.mem_image.mpr
  refine ⟨source.ancestor i, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨hcolumns i hi, hextract i hi⟩

/-- The original label embedding prevents any hidden repeated copy. -/
theorem labels_card_le_originalAtlas (hcover : cover.Realizes)
    (D : Ideal (𝓞 K))
    (hcolumns : ∀ i ∈ source.source.columns,
      source.ancestor i ∈ call.workingRaw.exteriorColumns)
    (hextract : ∀ i ∈ source.source.columns,
      supportExtract (call.workingRaw.columnExterior (source.ancestor i)).val
        source.first.fullDeletion = D) :
    cover.cover.labels.card ≤
      (call.workingRaw.originalAtlas.labels source.first.fullDeletion D).card := by
  have hc := Finset.card_le_card
    (cover.label_image_subset_originalAtlas hcover D hcolumns hextract)
  rwa [Finset.card_image_of_injective _ cover.label.injective] at hc

/-- The two plain occurrences are included together with every prime
occurrence.  All extracted coordinates are divisors of the same D. -/
theorem labels_card_le_divisorPower (hcover : cover.Realizes)
    (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hcolumns : ∀ i ∈ source.source.columns,
      source.ancestor i ∈ call.workingRaw.exteriorColumns)
    (hextract : ∀ i ∈ source.source.columns,
      supportExtract (call.workingRaw.columnExterior (source.ancestor i)).val
        source.first.fullDeletion = D) :
    cover.cover.labels.card ≤ (idealDivisors D).card ^ (c.geometry.slots + 2) := by
  apply (cover.labels_card_le_originalAtlas hcover D hcolumns hextract).trans
  apply call.workingRaw.originalAtlas.labels_card_le_cap c.geometry.slots
  · exact call.slots_le
  · exact hD

end OriginalCover

namespace N8Source

/-- A uniform small-power bound for each actual original cover.  The
constant is chosen before the call, source, cover and extracted ideal. -/
theorem originalCover_uniform_subpower (c : TargetContext K)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (p : SourceParameters c),
      ∀ (source : PhysicalSource call p) (cover : OriginalCover source),
      cover.Realizes → ∀ D : Ideal (𝓞 K), D ≠ 0 →
      (Ideal.absNorm D : ℝ) ≤ call.base ^ B →
      (∀ i ∈ source.source.columns,
        source.ancestor i ∈ call.workingRaw.exteriorColumns) →
      (∀ i ∈ source.source.columns,
        supportExtract (call.workingRaw.columnExterior (source.ancestor i)).val
          source.first.fullDeletion = D) →
      (cover.cover.labels.card : ℝ) ≤ C * call.base ^ ε := by
  obtain ⟨C, hC, hbound⟩ := support_tuple_multiplicity_subpower (K := K)
    (c.geometry.slots + 2) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro call p source cover hcover D hD hnorm hcolumns hextract
  have hbase_pos : 0 < call.base := call.base_pos
  have hcard : (cover.cover.labels.card : ℝ) ≤
      (idealDivisorCount D : ℝ) ^ (c.geometry.slots + 2) := by
    exact_mod_cast cover.labels_card_le_divisorPower hcover D hD hcolumns hextract
  exact hcard.trans (hbound call.base call.domain.scale.le D hnorm)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalCover.label_image_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.originalCover_uniform_subpower
