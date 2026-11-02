import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOccurrenceFacts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryPhaseFacts
import Lean.Elab.Command

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: imports [mono_ms={ms}]"
    stderr.flush

/-!
# The same original column through both occurrence extractions

The two support branches reconstruct the original occurrence tuple.
Their source indices retain the original ancestor, including the
dependent count casts between the first branch and its actual atlas.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace OrdinaryOriginalCoordinates

section Atlas

variable {A : SArithmeticData K} {ι : Type*} {k : ℕ}
variable {columns : Finset ι} {ideal : ι → A.Exterior}

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.dictionary"
    stderr.flush

/-- The four computational fields are independent of the support
proofs which are transported by the residual atlas constructors. -/
private def dictionary (R : CartesianSourceReindex columns ideal k) :=
  ((R.plain₁, R.plain₂), (R.slots, R.index))

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.dictionary_mp"
    stderr.flush

private theorem dictionary_mp {other : Finset ι} (hc : columns = other)
    (hT : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex other ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    dictionary (Eq.mp hT R) = dictionary R := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.dictionary_mp.proof"
    stderr.flush
  subst other
  rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.dictionary_mpr"
    stderr.flush

private theorem dictionary_mpr {other : Finset ι} (hc : columns = other)
    (hT : CartesianSourceReindex other ideal k =
      CartesianSourceReindex columns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    dictionary (Eq.mpr hT R) = dictionary R := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.dictionary_mpr.proof"
    stderr.flush
  subst other
  rfl

variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
variable (d : T.labels P D)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_dictionary"
    stderr.flush

private theorem residualReindex_dictionary :
    dictionary (T.residualReindex P D J hJ d) =
      ((SupportCartesian.plainResidual T.reindex.plain₁ P
          (T.branch P D d).plainExtract₁,
        SupportCartesian.plainResidual T.reindex.plain₂ P
          (T.branch P D d).plainExtract₂),
        ((fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch P D d).keep j)) P),
          fun x => T.reindex.index ((T.branch P D d).reconstruct x))) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.residualReindex_dictionary.proof"
    stderr.flush
  have hfibre := (T.commonFibre_eq_full P D d).symm
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.fibre"
    stderr.flush
  have hlabel :
      columns.filter (fun i =>
          T.reindex.supportExtractionLabel P i = (T.branch P D d).key) =
        columns.filter (fun i => T.reindex.supportExtractionLabel P i = d.val) := by
    rw [T.branch_key P D d]
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.label"
    stderr.flush
  have hbranch :=
    (T.reindex.supportExtractionLabel_fibre P (T.branch P D d)).symm
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.branch"
    stderr.flush
  unfold SourceCartesianAtlas.residualReindex
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.unfoldResidualReindex"
    stderr.flush
  rw [dictionary_mpr hfibre, dictionary_mp hlabel]
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.transportFibreLabel"
    stderr.flush
  unfold CartesianSourceReindex.supportResidualLabelBranch
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_dictionary.unfoldLabelBranch"
    stderr.flush
  rw [dictionary_mpr hbranch] <;> rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_plain₁"
    stderr.flush

theorem residualReindex_plain₁ :
    (T.residualReindex P D J hJ d).plain₁ =
      SupportCartesian.plainResidual T.reindex.plain₁ P
        (T.branch P D d).plainExtract₁ :=
  congrArg (fun x => x.1.1) (residualReindex_dictionary T P D J hJ d)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_plain₂"
    stderr.flush

theorem residualReindex_plain₂ :
    (T.residualReindex P D J hJ d).plain₂ =
      SupportCartesian.plainResidual T.reindex.plain₂ P
        (T.branch P D d).plainExtract₂ :=
  congrArg (fun x => x.1.2) (residualReindex_dictionary T P D J hJ d)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_slots"
    stderr.flush

theorem residualReindex_slots :
    (T.residualReindex P D J hJ d).slots =
      fun j => SupportCartesian.primeLive
        (T.reindex.slots (SlotRestriction.index (T.branch P D d).keep j)) P :=
  congrArg (fun x => x.2.1) (residualReindex_dictionary T P D J hJ d)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_index"
    stderr.flush

theorem residualReindex_index (x : AllocationColumn K (T.branch P D d).keep.card) :
    (T.residualReindex P D J hJ d).index x =
      T.reindex.index ((T.branch P D d).reconstruct x) :=
  congrFun (congrArg (fun x => x.2.2)
    (residualReindex_dictionary T P D J hJ d)) x

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_cartesian"
    stderr.flush

theorem residualReindex_cartesian :
    (T.residualReindex P D J hJ d).cartesian = (T.branch P D d).residualColumns := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.residualReindex_cartesian.proof"
    stderr.flush
  change childCartesianColumns _ _ _ = _
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: residualReindex_cartesian.change"
    stderr.flush
  rw [residualReindex_plain₁, residualReindex_plain₂, residualReindex_slots,
    SupportCartesianBranch.residualColumns]

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero"
    stderr.flush

theorem residualReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ (T.residualReindex P D J hJ d).plain₁) : I ≠ 0 := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero.proof"
    stderr.flush
  rw [residualReindex_plain₁] at hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact supportResidual_ne_zero J P

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero"
    stderr.flush

theorem residualReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ (T.residualReindex P D J hJ d).plain₂) : I ≠ 0 := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero.proof"
    stderr.flush
  rw [residualReindex_plain₂] at hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact supportResidual_ne_zero J P

end Atlas

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.allocationColumn_cast_roundtrip"
    stderr.flush

private theorem allocationColumn_cast_roundtrip {m n : ℕ} (hc : m = n)
    (x : AllocationColumn K n) :
    cast (congrArg (AllocationColumn K) hc)
      (cast (congrArg (AllocationColumn K) hc.symm) x) = x := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.allocationColumn_cast_roundtrip.proof"
    stderr.flush
  subst n
  rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.allocationColumnIdeal_cast"
    stderr.flush

theorem allocationColumnIdeal_cast {m n : ℕ} (hc : m = n)
    (x : AllocationColumn K m) :
    allocationColumnIdeal (cast (congrArg (AllocationColumn K) hc) x) =
      allocationColumnIdeal x := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.allocationColumnIdeal_cast.proof"
    stderr.flush
  subst n
  rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.residualColumns_coprime"
    stderr.flush

theorem residualColumns_coprime {k : ℕ}
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
    {P : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch S₁ S₂ slots P) (hP : ∀ Q ∈ P, Prime Q)
    (x : AllocationColumn K b.keep.card) (hx : x ∈ b.residualColumns) :
    IsCoprime (allocationColumnIdeal x) (∏ Q ∈ P, Q) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.residualColumns_coprime.proof"
    stderr.flush
  have hr : supportResidual (allocationColumnIdeal (b.reconstruct x)) P =
      allocationColumnIdeal x := by
    rw [b.residual_ideal _ (b.reconstruct_mem x hx), b.residual_reconstruct x hx]
  rw [← hr]
  exact IsCoprime.prod_right_iff.mpr
    ((outside_iff_coprime P hP
      ⟨_, supportResidual_ne_zero (allocationColumnIdeal (b.reconstruct x)) P⟩).mp
        (residual_outside P hP (allocationColumnIdeal (b.reconstruct x))))

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OrdinaryOriginalCoordinates.cartesian_mem_cast"
    stderr.flush

private theorem cartesian_mem_cast {m n : ℕ} (hc : m = n)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (slots : Fin m → Finset (HeightOneSpectrum (𝓞 K)))
    (other : Fin n → Finset (HeightOneSpectrum (𝓞 K)))
    (hslots : HEq slots other) (x : AllocationColumn K m) :
    x ∈ childCartesianColumns S₁ S₂ slots ↔
      cast (congrArg (AllocationColumn K) hc) x ∈
        childCartesianColumns S₁ S₂ other := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OrdinaryOriginalCoordinates.cartesian_mem_cast.proof"
    stderr.flush
  subst n
  have he := eq_of_heq hslots
  subst other
  rfl

end OrdinaryOriginalCoordinates

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace OriginalCover.Realizes

variable {source : PhysicalSource call p} {cover : OriginalCover source}
variable (hcover : cover.Realizes) (a : cover.cover.labels)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OriginalCover.Realizes.cartesian_mem"
    stderr.flush

theorem cartesian_mem (x : AllocationColumn K (cover.cover.branch a).slotCount) :
    x ∈ (cover.cover.branch a).reindex.cartesian ↔
      cast (congrArg (AllocationColumn K) (hcover.count a).symm) x ∈
        (cover.first a).residualColumns := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.cartesian_mem.proof"
    stderr.flush
  change x ∈ childCartesianColumns _ _ _ ↔
    cast (congrArg (AllocationColumn K) (hcover.count a).symm) x ∈
      childCartesianColumns _ _ _
  rw [hcover.plain₁ a, hcover.plain₂ a]
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.cartesian_mem.plainFields"
    stderr.flush
  exact OrdinaryOriginalCoordinates.cartesian_mem_cast (hcover.count a).symm
    _ _ _ _ (hcover.slots a) x

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OriginalCover.Realizes.ancestor_index [mono_ms={ms}]"
    stderr.flush

theorem ancestor_index (x : AllocationColumn K (cover.cover.branch a).slotCount)
    (hx : x ∈ (cover.cover.branch a).reindex.cartesian) :
    source.ancestor ((cover.cover.branch a).reindex.index x) =
      call.workingRaw.originalIndex ((cover.first a).reconstruct
        (cast (congrArg (AllocationColumn K) (hcover.count a).symm) x)) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.ancestor_index.proof"
    stderr.flush
  have h := hcover.index a
    (cast (congrArg (AllocationColumn K) (hcover.count a).symm) x)
    ((hcover.cartesian_mem a x).mp hx)
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.ancestor_index.index"
    stderr.flush
  exact (congrArg
    (fun y : AllocationColumn K (cover.cover.branch a).slotCount =>
      source.ancestor ((cover.cover.branch a).reindex.index y))
    (OrdinaryOriginalCoordinates.allocationColumn_cast_roundtrip
      (hcover.count a) x)).symm.trans h

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before OriginalCover.Realizes.ancestor_index_of_count [mono_ms={ms}]"
    stderr.flush

/-- Align count proofs while the source and cover are abstract. Concrete
packets then use exactly their supplied count proof in the result. -/
include hcover in
private theorem ancestor_index_of_count
    (hcount : (cover.first a).keep.card = (cover.cover.branch a).slotCount)
    (x : AllocationColumn K (cover.cover.branch a).slotCount)
    (hx : x ∈ (cover.cover.branch a).reindex.cartesian) :
    source.ancestor ((cover.cover.branch a).reindex.index x) =
      call.workingRaw.originalIndex ((cover.first a).reconstruct
        (cast (congrArg (AllocationColumn K) hcount.symm) x)) := by
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.ancestor_index_of_count.proof [mono_ms={ms}]"
    stderr.flush
  exact hcover.ancestor_index a x hx
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: OriginalCover.Realizes.ancestor_index_of_count.returned [mono_ms={ms}]"
    stderr.flush

end OriginalCover.Realizes

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_deletionPrime [mono_ms={ms}]"
    stderr.flush

theorem realizes_deletionPrime (hpacket : packet.Realizes) :
    ∀ Q ∈ packet.second.physical.first.fullDeletion, Prime Q := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_deletionPrime.proof"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_deletionPrime.packet"
    stderr.flush
  change ∀ Q ∈ (trace.second.source (raw.index j).val.1.1).physical.first.fullDeletion,
    Prime Q
  rw [htrace.second.physical]
  exact OrdinaryPhaseFacts.deletion_prime htrace.cauchy trace.expansion htrace.expansion _

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstPlain₁"
    stderr.flush

theorem realizes_firstPlain₁ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₁ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₁
        packet.second.physical.first.fullDeletion
        (packet.firstBranch side).plainExtract₁ := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_firstPlain₁.proof"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₁.packet"
    stderr.flush
  cases side with
  | false =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₁.false"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).1.plain₁ (raw.index j).val.1.2.2.2.1
  | true =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₁.true"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).2.plain₁ (raw.index j).val.1.2.2.2.2.1

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstPlain₂"
    stderr.flush

theorem realizes_firstPlain₂ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₂ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₂
        packet.second.physical.first.fullDeletion
        (packet.firstBranch side).plainExtract₂ := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_firstPlain₂.proof"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₂.packet"
    stderr.flush
  cases side with
  | false =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₂.false"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).1.plain₂ (raw.index j).val.1.2.2.2.1
  | true =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstPlain₂.true"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).2.plain₂ (raw.index j).val.1.2.2.2.2.1

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstSlots"
    stderr.flush

theorem realizes_firstSlots (hpacket : packet.Realizes) (side : Bool) :
    HEq (packet.firstAtlas side).reindex.slots
      (fun i : Fin (packet.firstBranch side).keep.card =>
        SupportCartesian.primeLive
          (call.workingRaw.exteriorSlots
            (SlotRestriction.index (packet.firstBranch side).keep i))
          packet.second.physical.first.fullDeletion) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_firstSlots.proof"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstSlots.packet"
    stderr.flush
  cases side with
  | false =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstSlots.false"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).1.slots (raw.index j).val.1.2.2.2.1
  | true =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstSlots.true"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).2.slots (raw.index j).val.1.2.2.2.2.1

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstCartesian [mono_ms={ms}]"
    stderr.flush

theorem realizes_firstCartesian (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount) :
    x ∈ (packet.firstAtlas side).reindex.cartesian ↔
      cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x ∈
        (packet.firstBranch side).residualColumns := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_firstCartesian.proof"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstCartesian.packet"
    stderr.flush
  cases side with
  | false =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstCartesian.false"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).1.cartesian_mem
      (raw.index j).val.1.2.2.2.1 x
  | true =>
    run_tac do
      let stderr ← IO.getStderr
      stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstCartesian.true"
      stderr.flush
    exact (hraw (raw.index j).val.1.1).2.cartesian_mem
      (raw.index j).val.1.2.2.2.2.1 x

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstIndex_of_count [mono_ms={ms}]"
    stderr.flush

/-- Keep the count proof independent of the realization witness while
eliminating that witness. The public statement supplies its original
count proof only after this transport has been checked. -/
private theorem realizes_firstIndex_of_count (hpacket : packet.Realizes) (side : Bool)
    (hcount : (packet.firstBranch side).keep.card = (packet.firstAtlas side).slotCount)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount)
    (hx : x ∈ (packet.firstAtlas side).reindex.cartesian) :
    packet.second.physical.ancestor ((packet.firstAtlas side).reindex.index x) =
      call.workingRaw.originalIndex ((packet.firstBranch side).reconstruct
        (cast (congrArg (AllocationColumn K) hcount.symm) x)) := by
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.proof [mono_ms={ms}]"
    stderr.flush
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.packet [mono_ms={ms}]"
    stderr.flush
  cases side with
  | false =>
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.false [mono_ms={ms}]"
      stderr.flush
    have h := OriginalCover.Realizes.ancestor_index_of_count
      (hraw (raw.index j).val.1.1).1 (raw.index j).val.1.2.2.2.1 hcount x hx
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.false.index [mono_ms={ms}]"
      stderr.flush
    exact h
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.false.returned [mono_ms={ms}]"
      stderr.flush
  | true =>
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.true [mono_ms={ms}]"
      stderr.flush
    have h := OriginalCover.Realizes.ancestor_index_of_count
      (hraw (raw.index j).val.1.1).2 (raw.index j).val.1.2.2.2.2.1 hcount x hx
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.true.index [mono_ms={ms}]"
      stderr.flush
    exact h
    run_tac do
      let stderr ← IO.getStderr
      let ms ← IO.monoMsNow
      stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.true.returned [mono_ms={ms}]"
      stderr.flush
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: realizes_firstIndex_of_count.returned [mono_ms={ms}]"
    stderr.flush

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.realizes_firstIndex [mono_ms={ms}]"
    stderr.flush

theorem realizes_firstIndex (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount)
    (hx : x ∈ (packet.firstAtlas side).reindex.cartesian) :
    packet.second.physical.ancestor ((packet.firstAtlas side).reindex.index x) =
      call.workingRaw.originalIndex ((packet.firstBranch side).reconstruct
        (cast (congrArg (AllocationColumn K)
          (packet.realizes_firstCount hpacket side).symm) x)) := by
  run_tac do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.realizes_firstIndex.proof [mono_ms={ms}]"
    stderr.flush
  exact realizes_firstIndex_of_count packet hpacket side
    (packet.realizes_firstCount hpacket side) x hx

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.secondColumn [mono_ms={ms}]"
    stderr.flush

/-- The actual source column of a second residual occurrence tuple. -/
def secondColumn : (side : Bool) →
    AllocationColumn K (packet.secondBranch side).keep.card → packet.second.physical.Column
  | false => packet.leftReindex.index
  | true => packet.rightReindex.index

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.secondColumn_eq"
    stderr.flush

theorem secondColumn_eq (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    packet.secondColumn side x =
      (packet.firstAtlas side).reindex.index ((packet.secondBranch side).reconstruct x) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.secondColumn_eq.proof"
    stderr.flush
  cases side <;>
    exact OrdinaryOriginalCoordinates.residualReindex_index _ _ _ _ _ _ x

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.leftReindex_cartesian"
    stderr.flush

theorem leftReindex_cartesian :
    packet.leftReindex.cartesian = (packet.secondBranch false).residualColumns :=
  OrdinaryOriginalCoordinates.residualReindex_cartesian _ _ _ _ _ _

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.rightReindex_cartesian"
    stderr.flush

theorem rightReindex_cartesian :
    packet.rightReindex.cartesian = (packet.secondBranch true).residualColumns :=
  OrdinaryOriginalCoordinates.residualReindex_cartesian _ _ _ _ _ _

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.leftReindex_plain₁_ne_zero"
    stderr.flush

theorem leftReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.leftReindex.plain₁) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero _ _ _ _ _ _ I hI

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.leftReindex_plain₂_ne_zero"
    stderr.flush

theorem leftReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.leftReindex.plain₂) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero _ _ _ _ _ _ I hI

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.rightReindex_plain₁_ne_zero"
    stderr.flush

theorem rightReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.rightReindex.plain₁) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero _ _ _ _ _ _ I hI

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.rightReindex_plain₂_ne_zero"
    stderr.flush

theorem rightReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.rightReindex.plain₂) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero _ _ _ _ _ _ I hI

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.secondReconstruct_mem"
    stderr.flush

theorem secondReconstruct_mem (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.secondBranch side).reconstruct x ∈ (packet.firstAtlas side).reindex.cartesian :=
  (packet.secondBranch side).original_subset ((packet.secondBranch side).reconstruct_mem x hx)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.secondColumn_ideal"
    stderr.flush

theorem secondColumn_ideal (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.second.physical.source.ideal (packet.secondColumn side x)).val =
      allocationColumnIdeal ((packet.secondBranch side).reconstruct x) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.secondColumn_ideal.proof"
    stderr.flush
  rw [packet.secondColumn_eq]
  exact (packet.firstAtlas side).reindex.ideal_product _ (packet.secondReconstruct_mem side x hx)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.firstResidualColumn"
    stderr.flush

/-- The first residual tuple after undoing the second extraction. -/
def firstResidualColumn (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    AllocationColumn K (packet.firstBranch side).keep.card :=
  cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm)
    ((packet.secondBranch side).reconstruct x)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.firstResidualColumn_mem"
    stderr.flush

theorem firstResidualColumn_mem (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    packet.firstResidualColumn hpacket side x ∈ (packet.firstBranch side).residualColumns :=
  (packet.realizes_firstCartesian hpacket side _).mp (packet.secondReconstruct_mem side x hx)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.firstResidualColumn_ideal"
    stderr.flush

theorem firstResidualColumn_ideal (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    allocationColumnIdeal (packet.firstResidualColumn hpacket side x) =
      allocationColumnIdeal ((packet.secondBranch side).reconstruct x) :=
  OrdinaryOriginalCoordinates.allocationColumnIdeal_cast
    (packet.realizes_firstCount hpacket side).symm
    ((packet.secondBranch side).reconstruct x)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.secondColumn_coprime_deletion"
    stderr.flush

theorem secondColumn_coprime_deletion (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    IsCoprime (packet.second.physical.source.ideal (packet.secondColumn side x)).val
      phases.deletionIdeal.val := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.secondColumn_coprime_deletion.proof"
    stderr.flush
  rw [packet.secondColumn_ideal side x hx, ← packet.firstResidualColumn_ideal hpacket side x]
  exact OrdinaryOriginalCoordinates.residualColumns_coprime (packet.firstBranch side)
    (packet.realizes_deletionPrime hpacket) _ (packet.firstResidualColumn_mem hpacket side x hx)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.ancestor_secondColumn"
    stderr.flush

theorem ancestor_secondColumn (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    packet.second.physical.ancestor (packet.secondColumn side x) =
      call.workingRaw.originalIndex ((packet.firstBranch side).reconstruct
        (packet.firstResidualColumn hpacket side x)) := by
  run_tac do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates step: RawLeafPacket.ancestor_secondColumn.proof"
    stderr.flush
  rw [packet.secondColumn_eq]
  exact packet.realizes_firstIndex hpacket side _ (packet.secondReconstruct_mem side x hx)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: before RawLeafPacket.originalColumn_mem"
    stderr.flush

theorem originalColumn_mem (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.firstBranch side).reconstruct (packet.firstResidualColumn hpacket side x) ∈
      childCartesianColumns call.workingRaw.originalPlain₁ call.workingRaw.originalPlain₂
        call.workingRaw.exteriorSlots :=
  (packet.firstBranch side).original_subset
    ((packet.firstBranch side).reconstruct_mem _ (packet.firstResidualColumn_mem hpacket side x hx))

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    let ms ← IO.monoMsNow
    stderr.putStrLn s!"MOM_ENGINE_STEP_V2 OrdinaryOriginalCoordinates checkpoint: all declarations complete [mono_ms={ms}]"
    stderr.flush

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ancestor_secondColumn
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.secondColumn_ideal

