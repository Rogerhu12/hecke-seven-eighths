import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteLeavesCover

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! Original-support identities used to instantiate the common S6 cover. -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem original_label_eq (P : Finset (Ideal (𝓞 K)))
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns) :
    call.workingRaw.originalReindex.supportExtractionLabel P v =
      SupportCartesian.extractionKey P (call.workingRaw.originalCoordinates v) := by
  simpa only [call.workingRaw.originalIndex_coordinates] using
    call.workingRaw.originalReindex.supportExtractionLabel_index P
      (call.workingRaw.originalCoordinates v)
      (call.workingRaw.originalCoordinates_mem v hv)

theorem original_label_union_left (S T : Finset (Ideal (𝓞 K)))
    (v w : call.workingRaw.Column)
    (hv : v ∈ call.workingRaw.exteriorColumns)
    (hw : w ∈ call.workingRaw.exteriorColumns)
    (he : call.workingRaw.originalReindex.supportExtractionLabel (S ∪ T) v =
      call.workingRaw.originalReindex.supportExtractionLabel (S ∪ T) w) :
    call.workingRaw.originalReindex.supportExtractionLabel S v =
      call.workingRaw.originalReindex.supportExtractionLabel S w := by
  rw [original_label_eq (S ∪ T) v hv, original_label_eq (S ∪ T) w hw] at he
  rw [original_label_eq S v hv, original_label_eq S w hw]
  apply Prod.ext
  · apply Prod.ext
    · have hh := congrArg (fun a => supportExtract a.1.1 S) he
      simpa only [SupportCartesian.extractionKey, supportExtract_union_left] using hh
    · have hh := congrArg (fun a => supportExtract a.1.2 S) he
      simpa only [SupportCartesian.extractionKey, supportExtract_union_left] using hh
  · funext i
    have hh := congrArg (fun a => supportExtract (a.2 i) S) he
    simpa only [SupportCartesian.extractionKey, supportExtract_union_left] using hh

theorem original_extract_congr (P : Finset (Ideal (𝓞 K)))
    (v w : call.workingRaw.Column)
    (hv : v ∈ call.workingRaw.exteriorColumns)
    (hw : w ∈ call.workingRaw.exteriorColumns)
    (he : call.workingRaw.originalReindex.supportExtractionLabel P v =
      call.workingRaw.originalReindex.supportExtractionLabel P w) :
    supportExtract (call.workingRaw.columnExterior v).val P =
      supportExtract (call.workingRaw.columnExterior w).val P := by
  let b := SupportCartesianBranch.ofColumn (P := P)
    call.workingRaw.originalPlain₁_nonzero call.workingRaw.originalPlain₂_nonzero
    (call.workingRaw.originalCoordinates v) (call.workingRaw.originalCoordinates_mem v hv)
  have hvb : call.workingRaw.originalCoordinates v ∈ b.originalColumns := b.witness_mem
  have hwb : call.workingRaw.originalCoordinates w ∈ b.originalColumns := by
    rw [b.originalColumns_eq_filter]
    refine Finset.mem_filter.mpr ⟨call.workingRaw.originalCoordinates_mem w hw, ?_⟩
    exact (original_label_eq P w hw).symm.trans
      (he.symm.trans (original_label_eq P v hv))
  have hvp := call.workingRaw.originalIndex_ideal_product
    (call.workingRaw.originalCoordinates v) (call.workingRaw.originalCoordinates_mem v hv)
  have hwp := call.workingRaw.originalIndex_ideal_product
    (call.workingRaw.originalCoordinates w) (call.workingRaw.originalCoordinates_mem w hw)
  simp only [call.workingRaw.originalIndex_coordinates] at hvp hwp
  rw [hvp, hwp, b.extract_ideal _ hvb, b.extract_ideal _ hwb]

/-- A source with an original column equivalence and a fixed common
ideal has the complete original extraction fibres. -/
theorem fibreInput_of_common
    (source : PhysicalSource call p) (e : source.Column ≃ call.workingRaw.Column)
    (ancestor : source.ancestor = e)
    (D : Ideal (𝓞 K))
    (columns : ∀ i, i ∈ source.source.columns ↔
      e i ∈ call.workingRaw.exteriorColumns ∧
        supportExtract (call.workingRaw.columnExterior (e i)).val
          source.first.fullDeletion = D)
    (residual : ∀ i ∈ source.source.columns,
      (source.source.ideal i).val =
        supportResidual (call.workingRaw.columnExterior (e i)).val
          source.first.fullDeletion) : OriginalFibreInput source where
  maps i hi := by simpa only [ancestor] using ((columns i).mp hi).1
  injective := by simpa only [ancestor] using e.injective.injOn
  residual i hi := by simpa only [ancestor] using residual i hi
  saturated i hi v hv he := by
    refine ⟨e.symm v, (columns _).mpr ⟨by simpa only [e.apply_symm_apply] using hv, ?_⟩, ?_⟩
    · rw [e.apply_symm_apply]
      exact (original_extract_congr source.first.fullDeletion v (e i)
        hv ((columns i).mp hi).1 (by simpa only [ancestor] using he)).trans
          ((columns i).mp hi).2
    · simp only [ancestor, e.apply_symm_apply]

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : Blueprint.FirstCauchyKey F)

def selectedIdeal : Ideal (𝓞 K) :=
  if Blueprint.FirstCauchyKey.side key then key.1.val.2 else key.1.val.1

theorem data_columns (i : F.source.Column) :
    i ∈ (Blueprint.FirstCauchyKey.data key).columns ↔
      i ∈ F.source.columns ∧
        supportExtract (F.source.ideal i).val (primeSupport key.1.val.1) =
          selectedIdeal key := by
  unfold Blueprint.FirstCauchyKey.data selectedIdeal
  split_ifs
  · rw [(Blueprint.FirstCauchyKey.piece key).right_columns]
    exact Finset.mem_filter
  · rw [(Blueprint.FirstCauchyKey.piece key).left_columns]
    exact Finset.mem_filter

theorem data_residual (i : F.source.Column) :
    ((Blueprint.FirstCauchyKey.data key).ideal i).val =
      supportResidual (F.source.ideal i).val (primeSupport key.1.val.1) := by
  unfold Blueprint.FirstCauchyKey.data
  split_ifs
  · rw [(Blueprint.FirstCauchyKey.piece key).right_ideal]
    exact (Blueprint.FirstCauchyKey.block key).right_residual i
  · rw [(Blueprint.FirstCauchyKey.piece key).left_ideal]
    exact (Blueprint.FirstCauchyKey.block key).left_residual i

theorem selected_support :
    primeSupport (selectedIdeal key) = primeSupport key.1.val.1 := by
  unfold selectedIdeal
  split_ifs
  · exact (commonSupportPool_support_eq F.source.columns F.source.columns
      (fun i => (F.source.ideal i).val) (fun i => (F.source.ideal i).val)
      key.1.val key.1.property).symm
  · rfl

end FirstCauchyKey

/-- Coherent reindexing of a first Cauchy source preserves the original
support fibres.  All hypotheses are individual-column identities. -/
theorem fibreInput_of_first
    (F : FirstPresentation call p) (hF : F.Realizes)
    (key : Blueprint.FirstCauchyKey F) (source : PhysicalSource call p)
    (e : source.Column ≃ F.source.Column)
    (ancestor : ∀ i, source.ancestor i = F.index (e i))
    (columns : ∀ i, i ∈ source.source.columns ↔
      e i ∈ (Blueprint.FirstCauchyKey.data key).columns)
    (ideal : ∀ i, source.source.ideal i = (Blueprint.FirstCauchyKey.data key).ideal (e i))
    (deletion : source.first.fullDeletion = primeSupport key.1.val.1) :
    OriginalFibreInput source := by
  have hmem (i : F.source.Column) :
      i ∈ F.source.columns ↔ F.index i ∈ call.workingRaw.exteriorColumns := by
    rw [← hF.columns]
    constructor
    · intro hi
      exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
      exact F.index.injective he ▸ hj
  apply fibreInput_of_common source (e.trans F.index) (funext ancestor)
    (FirstCauchyKey.selectedIdeal key)
  · intro i
    rw [columns i, FirstCauchyKey.data_columns, hmem, hF.ideal, deletion]
  · intro i _
    rw [ideal i, FirstCauchyKey.data_residual, hF.ideal, deletion]

theorem fibreInput_congr
    (source target : PhysicalSource call p) (h : OriginalFibreInput source)
    (e : target.Column ≃ source.Column)
    (ancestor : ∀ i, target.ancestor i = source.ancestor (e i))
    (columns : ∀ i, i ∈ target.source.columns ↔ e i ∈ source.source.columns)
    (ideal : ∀ i, target.source.ideal i = source.source.ideal (e i))
    (deletion : target.first.fullDeletion = source.first.fullDeletion) :
    OriginalFibreInput target where
  maps i hi := by rw [ancestor]; exact h.maps _ ((columns i).mp hi)
  injective := by
    intro i hi j hj he
    apply e.injective
    apply h.injective ((columns i).mp hi) ((columns j).mp hj)
    simpa only [ancestor] using he
  residual i hi := by
    rw [ideal, ancestor, deletion]
    exact h.residual _ ((columns i).mp hi)
  saturated i hi v hv he := by
    obtain ⟨j, hj, hjv⟩ := h.saturated (e i) ((columns i).mp hi) v hv
      (by simpa only [deletion, ancestor] using he)
    refine ⟨e.symm j, (columns _).mpr ?_, ?_⟩
    · simpa only [e.apply_symm_apply] using hj
    · simpa only [ancestor, e.apply_symm_apply] using hjv

theorem original_residual_count_congr
    (S : Finset (Ideal (𝓞 K))) (q : HeightOneSpectrum (𝓞 K))
    (v w : call.workingRaw.Column)
    (hv : v ∈ call.workingRaw.exteriorColumns)
    (hw : w ∈ call.workingRaw.exteriorColumns)
    (he : call.workingRaw.originalReindex.supportExtractionLabel (S ∪ {q.asIdeal}) v =
      call.workingRaw.originalReindex.supportExtractionLabel (S ∪ {q.asIdeal}) w) :
    (normalizedFactors (supportResidual (call.workingRaw.columnExterior v).val S)).count
        q.asIdeal =
      (normalizedFactors (supportResidual (call.workingRaw.columnExterior w).val S)).count
        q.asIdeal := by
  have hh := congrArg (fun I : Ideal (𝓞 K) => (normalizedFactors I).count q.asIdeal)
    (original_extract_congr (S ∪ {q.asIdeal}) v w hv hw he)
  simp only [supportExtract_count, Finset.mem_union, Finset.mem_singleton_self,
    or_true, if_true] at hh
  by_cases hq : q.asIdeal ∈ S
  · simp only [supportResidual_count, hq, if_true]
  · simpa only [supportResidual_count, hq, if_false] using hh

/-- Valuation extraction is closed under the larger, actual occurrence
label. It is the same proof for exponents 1, 6 and 7. -/
theorem fibreInput_of_residual
    (source target : PhysicalSource call p) (h : OriginalFibreInput source)
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    {P : PowerScaleExteriorPool (Arithmetic.data c) bad Z ell eps}
    (d : FirstGaussPoolData (Arithmetic.context c) P source.Column)
    (dcolumns : d.columns = source.source.columns)
    (dideal : d.ideal = source.source.ideal)
    (q : ExteriorPrime (Arithmetic.data c)) (n : ℕ)
    (e : target.Column ≃ d.valuationColumns q n)
    (columns : ∀ i, i ∈ target.source.columns)
    (ancestor : ∀ i, target.ancestor i = source.ancestor (e i).val)
    (ideal : ∀ i, (target.source.ideal i).val =
      supportResidual (source.source.ideal (e i).val).val {q.val.asIdeal})
    (deletion : target.first.fullDeletion = source.first.fullDeletion ∪ {q.val.asIdeal}) :
    OriginalFibreInput target := by
  have hold (i : target.Column) : (e i).val ∈ source.source.columns := by
    rw [← dcolumns]
    exact (Finset.mem_filter.mp (e i).property).1
  refine {
    maps := ?_
    injective := ?_
    residual := ?_
    saturated := ?_ }
  · intro i _
    rw [ancestor]
    exact h.maps _ (hold i)
  · intro i hi j hj he
    apply e.injective
    apply Subtype.ext
    apply h.injective (hold i) (hold j)
    simpa only [ancestor] using he
  · intro i _
    rw [ideal, h.residual _ (hold i), supportResidual_twice, deletion, ancestor]
  · intro i hi v hv he
    have he' : call.workingRaw.originalReindex.supportExtractionLabel
        (source.first.fullDeletion ∪ {q.val.asIdeal}) v =
      call.workingRaw.originalReindex.supportExtractionLabel
        (source.first.fullDeletion ∪ {q.val.asIdeal}) (source.ancestor (e i).val) := by
      simpa only [deletion, ancestor] using he
    have hbase := original_label_union_left source.first.fullDeletion {q.val.asIdeal}
      v (source.ancestor (e i).val) hv (h.maps _ (hold i)) he'
    obtain ⟨j, hj, hjv⟩ := h.saturated (e i).val (hold i) v hv hbase
    have hjn : j ∈ d.valuationColumns q n := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa only [dcolumns] using hj, ?_⟩
      change (normalizedFactors (d.ideal j).val).count q.val.asIdeal = n
      have hn := (Finset.mem_filter.mp (e i).property).2
      change (normalizedFactors (d.ideal (e i).val).val).count q.val.asIdeal = n at hn
      rw [dideal, h.residual _ hj]
      rw [dideal, h.residual _ (hold i)] at hn
      apply (original_residual_count_congr source.first.fullDeletion q.val
        (source.ancestor j) (source.ancestor (e i).val)
        (h.maps _ hj) (h.maps _ (hold i)) ?_).trans hn
      simpa only [hjv] using he'
    refine ⟨e.symm ⟨j, hjn⟩, columns _, ?_⟩
    simpa only [ancestor, e.apply_symm_apply] using hjv

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeaves.fibreInput_of_common
