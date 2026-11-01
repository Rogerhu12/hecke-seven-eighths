import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrames
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation

/-!
# The stored passive frame and its original occurrence dictionary

The explicit passive frame is the existing factor-frame constructor
on exactly the same actual allocation. Its witness comes from the
same attached label and nonempty finite carrier.

The original slot dictionary is restricted only by the first stored
allocation's keep map. A passive child then uses that map followed by
its own keep map. Neither construction chooses a new occurrence or
changes its original length.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments
open CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (paid : FixedChildCharacters K B.keep.card)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
variable (firstSign : ℝ) (rectangle : Bool)

/-- Both constructors store the same actual witness; the nonempty
proof is the one already contained in the original attached label. -/
theorem frame_eq_factors_frame :
    frame W B A paid C R side M a firstSign rectangle =
      ((table W B A paid).factors R side
        (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
        (columnExterior W B A) (columnExterior_val_of_mem W B A)
        firstSign rectangle).frame C a.val.1 a.val.2
          ((Finset.mem_filter.mp a.property).2) := rfl

variable {ω ψ : HeckeCharacter K}

/-- The table's pre-passive slots are the original first allocation's
retained occurrences, with their original lengths. -/
def tableOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent (table W B A paid).length where
  index :=
    { toFun := fun i => slots.index (SlotRestriction.index B.keep i)
      inj' := by
        intro i j hij
        have he := slots.index.injective hij
        apply B.keep.equivFin.symm.injective
        apply Subtype.ext
        exact he }
  length_eq i := slots.length_eq (SlotRestriction.index B.keep i)

@[simp] theorem tableOriginalSlots_index (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (tableOriginalSlots W B A paid parent slots).index i =
      slots.index (SlotRestriction.index B.keep i) := rfl

theorem tableOriginalSlots_length (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (table W B A paid).length i =
      (parent.geometry.slots (slots.index (SlotRestriction.index B.keep i))).length :=
  slots.length_eq (SlotRestriction.index B.keep i)

/-- The negative right source preserves the same occurrence lengths. -/
def frameOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent
      (frame W B A paid C R side M a firstSign rectangle).source.length := by
  cases side <;> exact tableOriginalSlots W B A paid parent slots

@[simp] theorem frameOriginalSlots_index (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (frameOriginalSlots W B A paid C R side M a firstSign rectangle parent slots).index i =
      slots.index (SlotRestriction.index B.keep i) := by
  cases side <;> rfl

/-- A child retains two actual keep maps in order. No new embedding
or capacity choice is used to identify the original slot. -/
theorem frame_childLength_eq_parent (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length)
    (i : Fin (frame W B A paid C R side M a firstSign rectangle).source.allocation.keep.card) :
    (frame W B A paid C R side M a firstSign rectangle).source.childLength i =
      (parent.geometry.slots (slots.index (SlotRestriction.index B.keep
        (SlotRestriction.index
          (frame W B A paid C R side M a firstSign rectangle).source.allocation.keep i)))).length := by
  cases side <;> exact slots.length_eq _

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame_eq_factors_frame
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.tableOriginalSlots
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frameOriginalSlots
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame_childLength_eq_parent
