import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOccurrenceFacts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryPhaseFacts

set_option linter.unusedSectionVars false
set_option autoImplicit false

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

/-- The four computational fields are independent of the support
proofs which are transported by the residual atlas constructors. -/
private def dictionary (R : CartesianSourceReindex columns ideal k) :=
  ((R.plain₁, R.plain₂), (R.slots, R.index))

private theorem dictionary_cast {other : Finset ι} (hc : columns = other)
    (hT : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex other ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    dictionary (cast hT R) = dictionary R := by
  subst other
  rfl

variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
variable (d : T.labels P D)

private theorem residualReindex_dictionary :
    dictionary (T.residualReindex P D J hJ d) =
      ((SupportCartesian.plainResidual T.reindex.plain₁ P
          (T.branch P D d).plainExtract₁,
        SupportCartesian.plainResidual T.reindex.plain₂ P
          (T.branch P D d).plainExtract₂),
        ((fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch P D d).keep j)) P),
          fun x => T.reindex.index ((T.branch P D d).reconstruct x))) := by
  have hfibre := (T.commonFibre_eq_full P D d).symm
  have hlabel :
      columns.filter (fun i =>
          T.reindex.supportExtractionLabel P i = (T.branch P D d).key) =
        columns.filter (fun i => T.reindex.supportExtractionLabel P i = d.val) := by
    rw [T.branch_key P D d]
  have hbranch :=
    (T.reindex.supportExtractionLabel_fibre P (T.branch P D d)).symm
  unfold SourceCartesianAtlas.residualReindex
  rw [dictionary_cast hfibre, dictionary_cast hlabel]
  unfold CartesianSourceReindex.supportResidualLabelBranch
  rw [dictionary_cast hbranch]

theorem residualReindex_plain₁ :
    (T.residualReindex P D J hJ d).plain₁ =
      SupportCartesian.plainResidual T.reindex.plain₁ P
        (T.branch P D d).plainExtract₁ :=
  congrArg (fun x => x.1.1) (residualReindex_dictionary T P D J hJ d)

theorem residualReindex_plain₂ :
    (T.residualReindex P D J hJ d).plain₂ =
      SupportCartesian.plainResidual T.reindex.plain₂ P
        (T.branch P D d).plainExtract₂ :=
  congrArg (fun x => x.1.2) (residualReindex_dictionary T P D J hJ d)

theorem residualReindex_slots :
    (T.residualReindex P D J hJ d).slots =
      fun j => SupportCartesian.primeLive
        (T.reindex.slots (SlotRestriction.index (T.branch P D d).keep j)) P :=
  congrArg (fun x => x.2.1) (residualReindex_dictionary T P D J hJ d)

theorem residualReindex_index (x : AllocationColumn K (T.branch P D d).keep.card) :
    (T.residualReindex P D J hJ d).index x =
      T.reindex.index ((T.branch P D d).reconstruct x) :=
  congrFun (congrArg (fun x => x.2.2)
    (residualReindex_dictionary T P D J hJ d)) x

theorem residualReindex_cartesian :
    (T.residualReindex P D J hJ d).cartesian = (T.branch P D d).residualColumns := by
  change childCartesianColumns _ _ _ = _
  rw [residualReindex_plain₁, residualReindex_plain₂, residualReindex_slots]

theorem residualReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ (T.residualReindex P D J hJ d).plain₁) : I ≠ 0 := by
  rw [residualReindex_plain₁] at hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact supportResidual_ne_zero J P

theorem residualReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ (T.residualReindex P D J hJ d).plain₂) : I ≠ 0 := by
  rw [residualReindex_plain₂] at hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact supportResidual_ne_zero J P

end Atlas

private theorem allocationColumn_cast_roundtrip {m n : ℕ} (hc : m = n)
    (x : AllocationColumn K n) :
    cast (congrArg (AllocationColumn K) hc)
      (cast (congrArg (AllocationColumn K) hc.symm) x) = x := by
  subst n
  rfl

theorem allocationColumnIdeal_cast {m n : ℕ} (hc : m = n)
    (x : AllocationColumn K m) :
    allocationColumnIdeal (cast (congrArg (AllocationColumn K) hc) x) =
      allocationColumnIdeal x := by
  subst n
  rfl

theorem residualColumns_coprime {k : ℕ}
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
    {P : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch S₁ S₂ slots P) (hP : ∀ Q ∈ P, Prime Q)
    (x : AllocationColumn K b.keep.card) (hx : x ∈ b.residualColumns) :
    IsCoprime (allocationColumnIdeal x) (∏ Q ∈ P, Q) := by
  have hr : supportResidual (allocationColumnIdeal (b.reconstruct x)) P =
      allocationColumnIdeal x := by
    rw [b.residual_ideal _ (b.reconstruct_mem x hx), b.residual_reconstruct x hx]
  rw [← hr]
  exact IsCoprime.prod_right_iff.mpr
    ((outside_iff_coprime P hP
      ⟨_, supportResidual_ne_zero (allocationColumnIdeal (b.reconstruct x)) P⟩).mp
        (residual_outside P hP (allocationColumnIdeal (b.reconstruct x))))

private theorem cartesian_mem_cast {m n : ℕ} (hc : m = n)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (slots : Fin m → Finset (HeightOneSpectrum (𝓞 K)))
    (other : Fin n → Finset (HeightOneSpectrum (𝓞 K)))
    (hslots : HEq slots other) (x : AllocationColumn K m) :
    x ∈ childCartesianColumns S₁ S₂ slots ↔
      cast (congrArg (AllocationColumn K) hc) x ∈
        childCartesianColumns S₁ S₂ other := by
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

theorem cartesian_mem (x : AllocationColumn K (cover.cover.branch a).slotCount) :
    x ∈ (cover.cover.branch a).reindex.cartesian ↔
      cast (congrArg (AllocationColumn K) (hcover.count a).symm) x ∈
        (cover.first a).residualColumns := by
  change x ∈ childCartesianColumns _ _ _ ↔
    cast (congrArg (AllocationColumn K) (hcover.count a).symm) x ∈
      childCartesianColumns _ _ _
  rw [hcover.plain₁ a, hcover.plain₂ a]
  exact OrdinaryOriginalCoordinates.cartesian_mem_cast (hcover.count a).symm
    _ _ _ _ (hcover.slots a) x

theorem ancestor_index (x : AllocationColumn K (cover.cover.branch a).slotCount)
    (hx : x ∈ (cover.cover.branch a).reindex.cartesian) :
    source.ancestor ((cover.cover.branch a).reindex.index x) =
      call.workingRaw.originalIndex ((cover.first a).reconstruct
        (cast (congrArg (AllocationColumn K) (hcover.count a).symm) x)) := by
  have h := hcover.index a
    (cast (congrArg (AllocationColumn K) (hcover.count a).symm) x)
    ((hcover.cartesian_mem a x).mp hx)
  simpa only [OrdinaryOriginalCoordinates.allocationColumn_cast_roundtrip] using h

end OriginalCover.Realizes

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_deletionPrime (hpacket : packet.Realizes) :
    ∀ Q ∈ packet.second.physical.first.fullDeletion, Prime Q := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  change ∀ Q ∈ (trace.second.source (raw.index j).val.1.1).physical.first.fullDeletion,
    Prime Q
  rw [htrace.second.physical]
  exact OrdinaryPhaseFacts.deletion_prime htrace.cauchy trace.expansion htrace.expansion _

theorem realizes_firstPlain₁ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₁ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₁
        packet.second.physical.first.fullDeletion
        (packet.firstBranch side).plainExtract₁ := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.plain₁ (raw.index j).val.1.2.2.2.1
  | true => exact (hraw (raw.index j).val.1.1).2.plain₁ (raw.index j).val.1.2.2.2.2.1

theorem realizes_firstPlain₂ (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstAtlas side).reindex.plain₂ =
      SupportCartesian.plainResidual call.workingRaw.originalPlain₂
        packet.second.physical.first.fullDeletion
        (packet.firstBranch side).plainExtract₂ := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.plain₂ (raw.index j).val.1.2.2.2.1
  | true => exact (hraw (raw.index j).val.1.1).2.plain₂ (raw.index j).val.1.2.2.2.2.1

theorem realizes_firstSlots (hpacket : packet.Realizes) (side : Bool) :
    HEq (packet.firstAtlas side).reindex.slots
      (fun i : Fin (packet.firstBranch side).keep.card =>
        SupportCartesian.primeLive
          (call.workingRaw.exteriorSlots
            (SlotRestriction.index (packet.firstBranch side).keep i))
          packet.second.physical.first.fullDeletion) := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.slots (raw.index j).val.1.2.2.2.1
  | true => exact (hraw (raw.index j).val.1.1).2.slots (raw.index j).val.1.2.2.2.2.1

theorem realizes_firstCartesian (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount) :
    x ∈ (packet.firstAtlas side).reindex.cartesian ↔
      cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x ∈
        (packet.firstBranch side).residualColumns := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.cartesian_mem
      (raw.index j).val.1.2.2.2.1 x
  | true => exact (hraw (raw.index j).val.1.1).2.cartesian_mem
      (raw.index j).val.1.2.2.2.2.1 x

theorem realizes_firstIndex (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount)
    (hx : x ∈ (packet.firstAtlas side).reindex.cartesian) :
    packet.second.physical.ancestor ((packet.firstAtlas side).reindex.index x) =
      call.workingRaw.originalIndex ((packet.firstBranch side).reconstruct
        (cast (congrArg (AllocationColumn K)
          (packet.realizes_firstCount hpacket side).symm) x)) := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side with
  | false => exact (hraw (raw.index j).val.1.1).1.ancestor_index
      (raw.index j).val.1.2.2.2.1 x hx
  | true => exact (hraw (raw.index j).val.1.1).2.ancestor_index
      (raw.index j).val.1.2.2.2.2.1 x hx

/-- The actual source column of a second residual occurrence tuple. -/
def secondColumn : (side : Bool) →
    AllocationColumn K (packet.secondBranch side).keep.card → packet.second.physical.Column
  | false => packet.leftReindex.index
  | true => packet.rightReindex.index

theorem secondColumn_eq (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    packet.secondColumn side x =
      (packet.firstAtlas side).reindex.index ((packet.secondBranch side).reconstruct x) := by
  cases side <;>
    exact OrdinaryOriginalCoordinates.residualReindex_index _ _ _ _ _ _ x

theorem leftReindex_cartesian :
    packet.leftReindex.cartesian = (packet.secondBranch false).residualColumns :=
  OrdinaryOriginalCoordinates.residualReindex_cartesian _ _ _ _ _ _

theorem rightReindex_cartesian :
    packet.rightReindex.cartesian = (packet.secondBranch true).residualColumns :=
  OrdinaryOriginalCoordinates.residualReindex_cartesian _ _ _ _ _ _

theorem leftReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.leftReindex.plain₁) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero _ _ _ _ _ _ I hI

theorem leftReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.leftReindex.plain₂) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero _ _ _ _ _ _ I hI

theorem rightReindex_plain₁_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.rightReindex.plain₁) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₁_ne_zero _ _ _ _ _ _ I hI

theorem rightReindex_plain₂_ne_zero (I : Ideal (𝓞 K))
    (hI : I ∈ packet.rightReindex.plain₂) : I ≠ 0 :=
  OrdinaryOriginalCoordinates.residualReindex_plain₂_ne_zero _ _ _ _ _ _ I hI

theorem secondReconstruct_mem (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.secondBranch side).reconstruct x ∈ (packet.firstAtlas side).reindex.cartesian :=
  (packet.secondBranch side).original_subset ((packet.secondBranch side).reconstruct_mem x hx)

theorem secondColumn_ideal (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.second.physical.source.ideal (packet.secondColumn side x)).val =
      allocationColumnIdeal ((packet.secondBranch side).reconstruct x) := by
  rw [packet.secondColumn_eq]
  exact (packet.firstAtlas side).reindex.ideal_product _ (packet.secondReconstruct_mem side x hx)

/-- The first residual tuple after undoing the second extraction. -/
def firstResidualColumn (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    AllocationColumn K (packet.firstBranch side).keep.card :=
  cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm)
    ((packet.secondBranch side).reconstruct x)

theorem firstResidualColumn_mem (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    packet.firstResidualColumn hpacket side x ∈ (packet.firstBranch side).residualColumns :=
  (packet.realizes_firstCartesian hpacket side _).mp (packet.secondReconstruct_mem side x hx)

theorem firstResidualColumn_ideal (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card) :
    allocationColumnIdeal (packet.firstResidualColumn hpacket side x) =
      allocationColumnIdeal ((packet.secondBranch side).reconstruct x) :=
  OrdinaryOriginalCoordinates.allocationColumnIdeal_cast _ _

theorem secondColumn_coprime_deletion (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    IsCoprime (packet.second.physical.source.ideal (packet.secondColumn side x)).val
      phases.deletionIdeal.val := by
  rw [packet.secondColumn_ideal side x hx, ← packet.firstResidualColumn_ideal hpacket side x]
  exact OrdinaryOriginalCoordinates.residualColumns_coprime (packet.firstBranch side)
    (packet.realizes_deletionPrime hpacket) _ (packet.firstResidualColumn_mem hpacket side x hx)

theorem ancestor_secondColumn (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    packet.second.physical.ancestor (packet.secondColumn side x) =
      call.workingRaw.originalIndex ((packet.firstBranch side).reconstruct
        (packet.firstResidualColumn hpacket side x)) := by
  rw [packet.secondColumn_eq]
  exact packet.realizes_firstIndex hpacket side _ (packet.secondReconstruct_mem side x hx)

theorem originalColumn_mem (hpacket : packet.Realizes) (side : Bool)
    (x : AllocationColumn K (packet.secondBranch side).keep.card)
    (hx : x ∈ (packet.secondBranch side).residualColumns) :
    (packet.firstBranch side).reconstruct (packet.firstResidualColumn hpacket side x) ∈
      childCartesianColumns call.workingRaw.originalPlain₁ call.workingRaw.originalPlain₂
        call.workingRaw.exteriorSlots :=
  (packet.firstBranch side).original_subset
    ((packet.firstBranch side).reconstruct_mem _ (packet.firstResidualColumn_mem hpacket side x hx))

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ancestor_secondColumn
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.secondColumn_ideal

