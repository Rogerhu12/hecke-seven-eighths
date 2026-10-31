import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CharacterRecipePreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# The original mesh in the actual retained children

A count bound and a total-length identity do not bound individual slot
lengths. The raw source therefore retains its original slot embedding
and its individual length identities. Allocation, the fixed capacity
deletion, clipping, normalization and time freezing compose that same
embedding. Every actual surviving slot has exactly its original length.

The final statements apply to the already chosen left and right children
of `ActualNormalizedPairFamily`. They inherit any mesh satisfied by the
original parent, with that same value; no equality with the auxiliary
capacity mesh and no mesh bound on the final children is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}

private theorem mesh_selectedSlotIndex_injective {n : ℕ}
    (keep : Finset (Fin n)) : Function.Injective (selectedSlotIndex keep) := by
  intro i j hij
  apply keep.equivFin.symm.injective
  apply Subtype.ext
  exact hij

private theorem mesh_allocationIndex_injective {n : ℕ}
    (keep : Finset (Fin n)) : Function.Injective (SlotRestriction.index keep) :=
  mesh_selectedSlotIndex_injective keep

private theorem mesh_finCast_injective {n m : ℕ} (h : n = m) :
    Function.Injective (Fin.cast h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

/-- An individual retained slot is identified with one actual original
slot, and its length is unchanged. This records no mesh inequality. -/
structure SlotLengthEmbedding (parent child : MomentData K ω ψ) where
  index : Fin child.geometry.slotCount ↪ Fin parent.geometry.slotCount
  length_eq : ∀ i, (child.geometry.slots i).length =
    (parent.geometry.slots (index i)).length

namespace SlotLengthEmbedding

variable {parent child : MomentData K ω ψ} (E : SlotLengthEmbedding parent child)

def refl (d : MomentData K ω ψ) : SlotLengthEmbedding d d where
  index := ⟨fun i => i, fun _ _ h => h⟩
  length_eq _ := rfl

def clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    SlotLengthEmbedding parent (clipPlainData child a Z hZ) where
  index := E.index
  length_eq := E.length_eq

def normalized (B : ℝ) (hB : 0 < B) :
    SlotLengthEmbedding parent (normalizedMomentProfiles child B hB) where
  index := E.index
  length_eq := E.length_eq

def restricted (keep : Finset (Fin child.geometry.slotCount)) :
    SlotLengthEmbedding parent (child.restrictSlots keep) where
  index := ⟨fun i => E.index (selectedSlotIndex keep i),
    E.index.injective.comp (mesh_selectedSlotIndex_injective keep)⟩
  length_eq i := E.length_eq (selectedSlotIndex keep i)

def frozen (t : ℝ) : SlotLengthEmbedding parent (frozenMomentProfiles child t) where
  index := E.index
  length_eq := E.length_eq

/-- The actual joint row filter leaves the slot dictionary untouched. -/
def jointRows (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior)
    (budget : ℝ) : SlotLengthEmbedding parent (jointRowBudgetData child support budget) where
  index := E.index
  length_eq := E.length_eq

theorem fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh) :
    child.geometry.fitsMesh mesh :=
  fun i => (E.length_eq i).le.trans (hparent (E.index i))

theorem slotCount_le : child.geometry.slotCount ≤ parent.geometry.slotCount := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective E.index E.index.injective

end SlotLengthEmbedding

/-- The primitive source dictionary is fixed before Fourier parameters
and capacity deletion. Its entries concern original individual slots,
not a final child or an aggregate length bound. -/
structure OriginalSlotDictionary (parent : MomentData K ω ψ)
    {k : ℕ} (length : Fin k → ℝ) where
  index : Fin k ↪ Fin parent.geometry.slotCount
  length_eq : ∀ i, length i = (parent.geometry.slots (index i)).length

namespace OriginalSlotDictionary

variable {parent : MomentData K ω ψ} {k : ℕ} {length : Fin k → ℝ}

/-- The common case in which the raw source uses a literal selection of
the original parent's slots requires no extra length proof. -/
def ofParentIndex (parent : MomentData K ω ψ)
    (index : Fin k ↪ Fin parent.geometry.slotCount) :
    OriginalSlotDictionary parent (fun i => (parent.geometry.slots (index i)).length) where
  index := index
  length_eq _ := rfl

theorem fitsMesh (raw : OriginalSlotDictionary parent length)
    {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh) (i : Fin k) :
    length i ≤ mesh := (raw.length_eq i).le.trans (hparent (raw.index i))

end OriginalSlotDictionary

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)
variable {parent : MomentData K ω ψ}

/-- The raw allocated calibration uses its original count cast, then
the actual allocation's retained indices. The calibration's individual
length identities supply the geometric part of this embedding. -/
def originalSlotEmbedding (raw : OriginalSlotDictionary parent s.length) (ξ : V) :
    SlotLengthEmbedding parent (D.data ξ) where
  index := ⟨fun i => raw.index
    (SlotRestriction.index s.allocation.keep (Fin.cast (D.count ξ) i)),
    raw.index.injective.comp
      ((mesh_allocationIndex_injective s.allocation.keep).comp
        (mesh_finCast_injective (D.count ξ)))⟩
  length_eq i := (D.lengths ξ i).trans (raw.length_eq _)

namespace NormalizedCapacityData.Child

variable {D} {G : D.NormalizedCapacityData} (out : G.Child)

/-- This is the same selected index used by the character recipe, now
continued through the original allocation. It is an embedding, not
merely a comparison of the two numbers of slots. -/
def retainedOriginalSourceIndex (ξ : V) :
    Fin (out.frozenData ξ).geometry.slotCount ↪ Fin k where
  toFun i := SlotRestriction.index s.allocation.keep (out.retainedSourceIndex ξ i)
  inj' := (mesh_allocationIndex_injective s.allocation.keep).comp
    ((mesh_finCast_injective (D.count ξ)).comp
      (mesh_selectedSlotIndex_injective
        (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
          (Finset.univ \ out.removed))))

/-- Every actual live length, including after clipping and freezing,
is the literal length of the original unallocated source slot. -/
theorem frozen_slot_length_source (ξ : V)
    (i : Fin (out.frozenData ξ).geometry.slotCount) :
    ((out.frozenData ξ).geometry.slots i).length =
      s.length (out.retainedOriginalSourceIndex ξ i) :=
  D.lengths ξ (selectedSlotIndex
    (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
      (Finset.univ \ out.removed)) i)

/-- No child is chosen here: the embedding belongs to the given
capacity child and its already fixed removed set. -/
def originalSlotEmbedding (raw : OriginalSlotDictionary parent s.length) (ξ : V) :
    SlotLengthEmbedding parent (out.frozenData ξ) where
  index := ⟨fun i => raw.index (out.retainedOriginalSourceIndex ξ i),
    raw.index.injective.comp (out.retainedOriginalSourceIndex ξ).injective⟩
  length_eq i := (out.frozen_slot_length_source ξ i).trans (raw.length_eq _)

theorem originalSlotEmbedding_index
    (raw : OriginalSlotDictionary parent s.length) (ξ : V)
    (i : Fin (out.frozenData ξ).geometry.slotCount) :
    (out.originalSlotEmbedding raw ξ).index i =
      raw.index (SlotRestriction.index s.allocation.keep (out.retainedSourceIndex ξ i)) := rfl

/-- Any original parent mesh, with exactly the same value, is inherited
by this chosen child. The auxiliary capacity mesh is irrelevant here. -/
theorem frozen_fits_parent_mesh (raw : OriginalSlotDictionary parent s.length)
    {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh) (ξ : V) :
    (out.frozenData ξ).geometry.fitsMesh mesh :=
  (out.originalSlotEmbedding raw ξ).fitsMesh hparent

end NormalizedCapacityData.Child
end ActualAllocatedSource.Calibration

namespace ActualNormalizedPairFamily

variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
variable (labels : Finset Λ) (parent : MomentData K ω ψ)

/-- Only the original per-side source slot dictionaries are supplied.
The two capacity deletions and all final child geometry are derived. -/
structure ParentSlotDictionaries where
  left : ∀ b ∈ labels, OriginalSlotDictionary parent (family.leftSource b).length
  right : ∀ b ∈ labels, OriginalSlotDictionary parent (family.rightSource b).length

namespace ParentSlotDictionaries

variable {family labels parent} (raw : family.ParentSlotDictionaries labels parent)

def leftEmbedding (b : family.active labels) (ξ : V) :
    SlotLengthEmbedding parent (family.leftData labels b ξ) :=
  (family.leftChild labels b).originalSlotEmbedding
    (raw.left b.val (Finset.mem_filter.mp b.property).1) ξ

def rightEmbedding (b : family.active labels) (ξ : V) :
    SlotLengthEmbedding parent (family.rightData labels b ξ) :=
  (family.rightChild labels b).originalSlotEmbedding
    (raw.right b.val (Finset.mem_filter.mp b.property).1) ξ

theorem left_slot_length (b : family.active labels) (ξ : V)
    (i : Fin (family.leftData labels b ξ).geometry.slotCount) :
    ((family.leftData labels b ξ).geometry.slots i).length =
      (parent.geometry.slots ((raw.leftEmbedding b ξ).index i)).length :=
  (raw.leftEmbedding b ξ).length_eq i

theorem right_slot_length (b : family.active labels) (ξ : V)
    (i : Fin (family.rightData labels b ξ).geometry.slotCount) :
    ((family.rightData labels b ξ).geometry.slots i).length =
      (parent.geometry.slots ((raw.rightEmbedding b ξ).index i)).length :=
  (raw.rightEmbedding b ξ).length_eq i

theorem left_fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh)
    (b : family.active labels) (ξ : V) :
    (family.leftData labels b ξ).geometry.fitsMesh mesh :=
  (raw.leftEmbedding b ξ).fitsMesh hparent

theorem right_fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh)
    (b : family.active labels) (ξ : V) :
    (family.rightData labels b ξ).geometry.fitsMesh mesh :=
  (raw.rightEmbedding b ξ).fitsMesh hparent

/-- Both sides of the actual family use the same original mesh, even
when their Fourier parameters, slot selections and deletions differ. -/
theorem fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh)
    (b : family.active labels) (ξ η : V) :
    (family.leftData labels b ξ).geometry.fitsMesh mesh ∧
      (family.rightData labels b η).geometry.fitsMesh mesh :=
  ⟨raw.left_fitsMesh hparent b ξ, raw.right_fitsMesh hparent b η⟩

theorem slotCounts (b : family.active labels) (ξ η : V) :
    (family.leftData labels b ξ).geometry.slotCount ≤ parent.geometry.slotCount ∧
      (family.rightData labels b η).geometry.slotCount ≤ parent.geometry.slotCount :=
  ⟨(raw.leftEmbedding b ξ).slotCount_le, (raw.rightEmbedding b η).slotCount_le⟩

end ParentSlotDictionaries
end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozen_slot_length_source
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozen_fits_parent_mesh
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.ParentSlotDictionaries.fitsMesh
