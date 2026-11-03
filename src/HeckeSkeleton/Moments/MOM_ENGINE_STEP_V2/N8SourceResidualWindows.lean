import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceAllocationMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceNormBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original norm window passes through both actual extractions

Every residual ideal divides the same original-column ideal recorded
by its ancestor.  This passes the original profile window to direct,
main and error sources and to the actual reconstructed second residual
columns.  It also bounds the combined first and pool extraction without
charging a second independent pool prime.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum
open HeckePort.Moments HeckePort.Moments.Support
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance n8ResidualWindowsCircleFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace N8Source

theorem supportExtract_dvd_original (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : Finset (Ideal (𝓞 K))) : supportExtract I P ∣ I :=
  ⟨supportResidual I P, (support_reconstruct I hI P).symm⟩

theorem supportResidual_dvd_original (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : Finset (Ideal (𝓞 K))) : supportResidual I P ∣ I :=
  ⟨supportExtract I P, (support_reconstruct I hI P).symm.trans (mul_comm _ _)⟩

theorem commonSupportPool_norm {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (hI : ∀ i ∈ left, I i ≠ 0) (hJ : ∀ j ∈ right, J j ≠ 0)
    (M : ℝ) (hleft : ∀ i ∈ left, (Ideal.absNorm (I i) : ℝ) ≤ M)
    (hright : ∀ j ∈ right, (Ideal.absNorm (J j) : ℝ) ≤ M)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hDE : DE ∈ commonSupportPool left right I J) :
    (Ideal.absNorm DE.1 : ℝ) ≤ M ∧ (Ideal.absNorm DE.2 : ℝ) ≤ M := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hDE
  have hi := (Finset.mem_product.mp hij).1
  have hj := (Finset.mem_product.mp hij).2
  exact ⟨(norm_le_of_dvd (hI ij.1 hi)
      (supportExtract_dvd_original _ (hI ij.1 hi) _)).trans (hleft ij.1 hi),
    (norm_le_of_dvd (hJ ij.2 hj)
      (supportExtract_dvd_original _ (hJ ij.2 hj) _)).trans (hright ij.2 hj)⟩

end N8Source

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

theorem source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (i : Fin family.count) (j : (family.source i).Column) :
    ((family.source i).source.ideal j).val ∣
      (call.workingRaw.columnExterior ((family.source i).ancestor j)).val := by
  rw [family.original_ideal_residual hF hf i j]
  exact N8Source.supportResidual_dvd_original _
    (call.workingRaw.columnExterior ((family.source i).ancestor j)).property.1 _

end FirstCauchyFamily

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem main_source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : Fin family.count) (source : PhysicalSource call p)
    (horigin : pool.MainOrigin i source) (j : source.Column) :
    (source.source.ideal j).val ∣ (call.workingRaw.columnExterior (source.ancestor j)).val := by
  rcases horigin with ⟨hcol, hsource, ha, _, _, _, _, _⟩
  apply N8Source.transport_ideal_dictionary source.source
    ((pool.data i).mainSource (family.source i).source.coefficient)
    source.ancestor (family.source i).ancestor hcol hsource ha
    (fun x I => I.val ∣ (call.workingRaw.columnExterior x).val) _ j
  intro x
  change ((pool.data i).ideal x).val ∣
    (call.workingRaw.columnExterior ((family.source i).ancestor x)).val
  rw [pool.data_ideal_eq hpool i x]
  exact family.source_ideal_dvd_original hF hf i x

theorem error_source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : Fin family.count) (q : pool.pool.primes)
    (e : AmplifierValuation) (source : PhysicalSource call p)
    (horigin : pool.ErrorOrigin i q e source) (j : source.Column) :
    (source.source.ideal j).val ∣ (call.workingRaw.columnExterior (source.ancestor j)).val := by
  rcases horigin with
    ⟨hcol, hsource, ha, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  apply N8Source.transport_ideal_dictionary source.source
    ((pool.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
    source.ancestor (fun x : (pool.data i).valuationColumns q.val e.multiplicity =>
      (family.source i).ancestor x.val) hcol hsource ha
    (fun x I => I.val ∣ (call.workingRaw.columnExterior x).val) _ j
  intro x
  have hdiv : ((pool.data i).residualPresentation q.val e.multiplicity x).residual.val ∣
      ((pool.data i).ideal x.val).val :=
    ⟨q.val.val.asIdeal ^ e.multiplicity,
      ((pool.data i).residualPresentation q.val e.multiplicity x).reconstructed.trans
        (mul_comm _ _)⟩
  apply hdiv.trans
  rw [pool.data_ideal_eq hpool i x.val]
  exact family.source_ideal_dvd_original hF hf i x.val

theorem source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (hpool : pool.Realizes) (i : pool.Index) (source : PhysicalSource call p)
    (horigin : pool.Origin i source) (j : source.Column) :
    (source.source.ideal j).val ∣ (call.workingRaw.columnExterior (source.ancestor j)).val := by
  rcases i with ⟨i, branch⟩
  cases branch with
  | inl u => exact pool.main_source_ideal_dvd_original hF hf hpool i source horigin j
  | inr qe => exact pool.error_source_ideal_dvd_original hF hf hpool i qe.1 qe.2 source horigin j

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

theorem source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count)
    (j : (expansion.source i).Column) :
    ((expansion.source i).source.ideal j).val ∣
      (call.workingRaw.columnExterior ((expansion.source i).ancestor j)).val := by
  cases expansion with
  | direct => exact family.source_ideal_dvd_original hF hf i j
  | pooled pool count index source =>
    exact pool.source_ideal_dvd_original hF hf hexpansion.2.1 (index i) (source i)
      (hexpansion.2.2 i) j

end PoolExpansion

namespace SecondFamily

variable {expansion : PoolExpansion family} (second : SecondFamily expansion)

theorem source_ideal_dvd_original (hF : F.Realizes) (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (hsecond : second.Realizes)
    (i : Fin expansion.count) :
    ∀ j : (second.source i).physical.Column,
      ((second.source i).physical.source.ideal j).val ∣
        (call.workingRaw.columnExterior ((second.source i).physical.ancestor j)).val := by
  let property (s : PhysicalSource call p) : Prop :=
    ∀ j : s.Column, (s.source.ideal j).val ∣
      (call.workingRaw.columnExterior (s.ancestor j)).val
  have hs : property (expansion.source i) :=
    expansion.source_ideal_dvd_original hF hf hexpansion i
  exact Eq.mpr (congrArg property (hsecond.physical i)) hs

theorem source_column_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (hexpansion : expansion.Realizes)
    (hsecond : second.Realizes) (i : Fin expansion.count)
    (j : (second.source i).physical.Column)
    (hj : j ∈ (second.source i).physical.source.columns) :
    (Arithmetic.data c).exteriorNorm ((second.source i).physical.source.ideal j) ≤
      call.base ^ N8Source.columnExponent c := by
  exact (norm_le_of_dvd
    (call.workingRaw.columnExterior ((second.source i).physical.ancestor j)).property.1
    (second.source_ideal_dvd_original hF hf hexpansion hsecond i j)).trans
      (N8Source.original_column_norm input large _
        (second.original_columns_extract hF hf hexpansion hsecond i j hj).1)

theorem combined_extraction_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (hexpansion : expansion.Realizes)
    (hsecond : second.Realizes) (i : Fin expansion.count)
    (hne : (second.source i).physical.source.columns.Nonempty) :
    (Ideal.absNorm ((second.source i).physical.first.selected.val *
      (second.source i).physical.first.poolPower.val) : ℝ) ≤
        call.base ^ N8Source.columnExponent c := by
  obtain ⟨j, hj⟩ := hne
  have h := second.original_columns_extract hF hf hexpansion hsecond i j hj
  have hd := N8Source.supportExtract_dvd_original _
    (call.workingRaw.columnExterior ((second.source i).physical.ancestor j)).property.1
    (second.source i).physical.first.fullDeletion
  rw [h.2] at hd
  exact (norm_le_of_dvd
    (call.workingRaw.columnExterior ((second.source i).physical.ancestor j)).property.1 hd).trans
      (N8Source.original_column_norm input large _ h.1)

theorem common_norm (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (hexpansion : expansion.Realizes)
    (hsecond : second.Realizes) (i : Fin expansion.count)
    (DE : (second.source i).CommonLabel) :
    (Ideal.absNorm DE.val.1 : ℝ) ≤ call.base ^ N8Source.columnExponent c ∧
      (Ideal.absNorm DE.val.2 : ℝ) ≤ call.base ^ N8Source.columnExponent c :=
  N8Source.commonSupportPool_norm _ _ _ _
    (fun j _ => ((second.source i).physical.source.ideal j).property.1)
    (fun j _ => ((second.source i).physical.source.ideal j).property.1) _
    (second.source_column_norm input large hF hf hexpansion hsecond i)
    (second.source_column_norm input large hF hf hexpansion hsecond i) _ DE.property

end SecondFamily

namespace SourceClassKey

variable {source : SecondSource call p} {LC RC : OriginalCover source.physical}
variable (key : SourceClassKey source.stage LC.cover RC.cover)

theorem rightReindex_index_mem
    (j : AllocationColumn K (SourceClassKey.rightSlots key))
    (hj : j ∈ childCartesianColumns (SourceClassKey.rightReindex key).plain₁
      (SourceClassKey.rightReindex key).plain₂ (SourceClassKey.rightReindex key).slots) :
    (SourceClassKey.rightReindex key).index j ∈ source.physical.source.columns := by
  have h := (SourceClassKey.rightReindex key).maps j hj
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).1

theorem rightResidual_norm_le (M : ℝ)
    (hcolumns : ∀ j ∈ source.physical.source.columns,
      (Arithmetic.data c).exteriorNorm (source.physical.source.ideal j) ≤ M)
    (j : AllocationColumn K (SourceClassKey.rightSlots key))
    (hj : j ∈ childCartesianColumns (SourceClassKey.rightReindex key).plain₁
      (SourceClassKey.rightReindex key).plain₂ (SourceClassKey.rightReindex key).slots) :
    (Ideal.absNorm ((SourceClassKey.block key).rightResidual
      ((SourceClassKey.rightReindex key).index j)).val : ℝ) ≤ M := by
  rw [(SourceClassKey.block key).right_residual]
  exact (norm_le_of_dvd
    (source.physical.source.ideal ((SourceClassKey.rightReindex key).index j)).property.1
    (N8Source.supportResidual_dvd_original _
      (source.physical.source.ideal ((SourceClassKey.rightReindex key).index j)).property.1 _)).trans
        (hcolumns _ (key.rightReindex_index_mem j hj))

end SourceClassKey

namespace N8Source

/-- The inner-divisor harmonic estimate now has all of its quantitative
conditions derived from the original call and source dictionaries. -/
theorem original_allocation_index_mass (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (trace : SourceTrace call p), trace.Realizes →
      ∀ (i : Fin trace.expansion.count)
        (LC RC : OriginalCover (trace.second.source i).physical),
        LC.Realizes → RC.Realizes →
        ∀ key : SourceClassKey (trace.second.source i).stage LC.cover RC.cover,
          key.allocationIndexMass ≤ C * call.base ^ ε := by
  obtain ⟨C, hC, hmass⟩ := actual_allocation_index_mass c (columnExponent c) ε
    (columnExponent_pos c).le hε
  refine ⟨C, hC, ?_⟩
  intro call input large p trace htrace i LC RC hLC hRC key
  have hbase_pos : 0 < call.base := call.base_pos
  apply hmass call p (trace.second.source i) LC RC hLC hRC key
  exact key.rightResidual_norm_le _
    (trace.second.source_column_norm input large htrace.first htrace.cauchy
      htrace.expansion htrace.second i)

end N8Source
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondFamily.combined_extraction_norm
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Source.original_allocation_index_mass
