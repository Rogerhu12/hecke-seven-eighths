import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityChild
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudget

/-!
# The original character recipes in the actual retained children

The term calibration identifies masked coefficients.  That alone does
not identify either factor of plainBackground * rowCharacter.  The raw
MOM_BASE recipe therefore specifies these character identities before
any Fourier parameter, profile normalization or capacity choice.

Every operation used by the producer preserves those identities.  Slot
restriction selects the original one-prime recipes by the literal
selectedSlotIndex; it never chooses another finite ray family.  No
closure property of theta, moment estimate or final admissibility is
assumed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

namespace FixedChildCharacters

/-- Select literal original slot recipes.  The plain character, its
finite correction, the mask and the fixed ray set stay identical. -/
def selectSlots {k n : ℕ} (T : FixedChildCharacters F k) (index : Fin n → Fin k) :
    FixedChildCharacters F n where
  plain := T.plain
  slot i := T.slot (index i)
  plainTwist := T.plainTwist
  slotTwist i := T.slotTwist (index i)
  mask := T.mask
  fixedRay := T.fixedRay
  plainTwist_mem := T.plainTwist_mem
  slotTwist_mem i := T.slotTwist_mem (index i)

namespace Calibration

variable {k : ℕ} {T : FixedChildCharacters F k} {d : MomentData F ω ψ}
variable {count : d.geometry.slotCount = k}
variable {u : HeckeGeneral.Analysis.NonzeroIdeal F} {g h' : A.R}
variable (D : T.Calibration (σ := σ) d count u g h')

def clippedProfiles (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    T.Calibration (σ := σ) (clipPlainData d a Z hZ) count u g h' where
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plain := D.plain
  slot := D.slot

def normalizedProfiles (B : ℝ) (hB : 0 < B) :
    T.Calibration (σ := σ) (normalizedMomentProfiles d B hB) count u g h' where
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plain := D.plain
  slot := D.slot

def frozenProfiles (t : ℝ) :
    T.Calibration (σ := σ) (frozenMomentProfiles d t) count u g h' where
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plain := D.plain
  slot := D.slot

def jointRows (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) :
    T.Calibration (σ := σ) (jointRowBudgetData d support budget) count u g h' where
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plain := D.plain
  slot := D.slot

/-- The actual restriction composes the old count transport with the
original selected index, so no source-slot relabelling is presumed. -/
def restricted (keep : Finset (Fin d.geometry.slotCount)) :
    (T.selectSlots (fun i : Fin keep.card => Fin.cast count (selectedSlotIndex keep i))).Calibration
      (σ := σ) (d.restrictSlots keep) rfl u g h' where
  fixedRay_mem_theta := D.fixedRay_mem_theta
  plain := D.plain
  slot i p := D.slot (selectedSlotIndex keep i) p

end Calibration
end FixedChildCharacters

/-- The whole-conjugation choice belongs to the original source branch;
it is fixed before the Fourier variables and all profile operations. -/
def parentPlainCharacter (parent : MomentData F ω ψ) (conjugated : Bool) :
    HeckeCharacter F :=
  if conjugated then parent.plainBackground⁻¹ else parent.plainBackground

/-- These are identities on the raw data, including all its possible
rows.  They do not follow merely from the masked term calibration and
are the corresponding narrow arithmetic recipe from MOM_BASE. -/
structure ParentCharacterRecipe {X : Type*} (parent : MomentData F ω ψ)
    (data : X → MomentData F ω ψ) (conjugated : Bool)
    (row : HeckeGeneral.Analysis.NonzeroIdeal F → HeckeCharacter F) : Prop where
  background : ∀ ξ, (data ξ).plainBackground = parentPlainCharacter parent conjugated
  rowCharacter : ∀ ξ, (data ξ).rowCharacter = row
  theta : ∀ ξ, (data ξ).theta = parent.theta

namespace ParentCharacterRecipe

variable {X : Type*} {parent : MomentData F ω ψ} {data : X → MomentData F ω ψ}
variable {conjugated : Bool}
variable {row : HeckeGeneral.Analysis.NonzeroIdeal F → HeckeCharacter F}
variable (R : ParentCharacterRecipe parent data conjugated row)

include R

theorem clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    ParentCharacterRecipe parent (fun ξ => clipPlainData (data ξ) a Z hZ) conjugated row :=
  ⟨R.background, R.rowCharacter, R.theta⟩

theorem normalized (B : X → ℝ) (hB : ∀ ξ, 0 < B ξ) :
    ParentCharacterRecipe parent
      (fun ξ => normalizedMomentProfiles (data ξ) (B ξ) (hB ξ)) conjugated row :=
  ⟨R.background, R.rowCharacter, R.theta⟩

theorem frozen (t : X → ℝ) :
    ParentCharacterRecipe parent (fun ξ => frozenMomentProfiles (data ξ) (t ξ)) conjugated row :=
  ⟨R.background, R.rowCharacter, R.theta⟩

theorem restricted (keep : ∀ ξ, Finset (Fin (data ξ).geometry.slotCount)) :
    ParentCharacterRecipe parent (fun ξ => (data ξ).restrictSlots (keep ξ)) conjugated row :=
  ⟨R.background, R.rowCharacter, R.theta⟩

theorem jointRows (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) :
    ParentCharacterRecipe parent
      (fun ξ => jointRowBudgetData (data ξ) support budget) conjugated row :=
  ⟨R.background, R.rowCharacter, R.theta⟩

end ParentCharacterRecipe

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

theorem frozen_rowCharacter_eq (ξ : V) :
    (out.frozenData ξ).rowCharacter = (D.data ξ).rowCharacter := rfl

theorem frozen_commonMask_eq (ξ : V) :
    (out.frozenData ξ).commonMask = (D.data ξ).commonMask := rfl

theorem frozen_inverseBackground_eq (ξ : V) :
    (out.frozenData ξ).inverseBackground = (D.data ξ).inverseBackground := rfl

/-- The same original background (or its whole conjugate), the same
row-character recipe and the same theta set reach the final child. -/
theorem frozen_parentCharacterRecipe
    {parent : MomentData F ω ψ} {conjugated : Bool}
    {row : HeckeGeneral.Analysis.NonzeroIdeal F → HeckeCharacter F}
    (R : ParentCharacterRecipe parent D.data conjugated row) :
    ParentCharacterRecipe parent out.frozenData conjugated row := by
  refine ⟨?_, ?_, ?_⟩
  · intro ξ
    exact (out.frozen_plainBackground_eq ξ).trans (R.background ξ)
  · intro ξ
    exact (out.frozen_rowCharacter_eq ξ).trans (R.rowCharacter ξ)
  · intro ξ
    exact (out.frozen_theta_eq ξ).trans (R.theta ξ)

/-- This is the actual retained slot index inside the already allocated
source.  It includes both the calibration's count cast and the one
uniform capacity deletion chosen before all Fourier parameters. -/
def retainedSourceIndex (ξ : V) :
    Fin (out.frozenData ξ).geometry.slotCount → Fin s.allocation.keep.card :=
  fun i => Fin.cast (D.count ξ) (selectedSlotIndex
    (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
      (Finset.univ \ out.removed)) i)

def retainedSourceCharacters (ξ : V) (h : H) :
    FixedChildCharacters F (out.frozenData ξ).geometry.slotCount :=
  ((s.characters h).restrictSlots s.allocation.keep).selectSlots (out.retainedSourceIndex ξ)

theorem retainedSourceCharacters_plain (ξ : V) (h : H) :
    (out.retainedSourceCharacters ξ h).plain = (s.characters h).plain := rfl

theorem retainedSourceCharacters_plainTwist (ξ : V) (h : H) :
    (out.retainedSourceCharacters ξ h).plainTwist = (s.characters h).plainTwist := rfl

theorem retainedSourceCharacters_fixedRay (ξ : V) (h : H) :
    (out.retainedSourceCharacters ξ h).fixedRay = (s.characters h).fixedRay := rfl

theorem retainedSourceCharacters_mask (ξ : V) (h : H) :
    (out.retainedSourceCharacters ξ h).mask = (s.characters h).mask := rfl

theorem retainedSourceCharacters_slot (ξ : V) (h : H)
    (i : Fin (out.frozenData ξ).geometry.slotCount) :
    (out.retainedSourceCharacters ξ h).slot i =
      (s.characters h).slot
        (SlotRestriction.index s.allocation.keep (out.retainedSourceIndex ξ i)) := rfl

theorem retainedSourceCharacters_slotTwist (ξ : V) (h : H)
    (i : Fin (out.frozenData ξ).geometry.slotCount) :
    (out.retainedSourceCharacters ξ h).slotTwist i =
      (s.characters h).slotTwist
        (SlotRestriction.index s.allocation.keep (out.retainedSourceIndex ξ i)) := rfl

/-- The original one-ideal and one-prime dictionaries themselves reach
the literal normalized, clipped, restricted and frozen output.  The
source plain term, finite twists, common mask and selected slot terms
are all computed from the original calibration. -/
def frozen_termCalibration (ξ : V) (h : H) :
    (out.retainedSourceCharacters ξ h).Calibration (σ := σ)
      (out.frozenData ξ) rfl (s.row h).momentIdeal
        (s.extractedFactor h) (s.row h).element :=
  let normalized := ((D.dictionary ξ h).clippedProfiles D.parameters s.base
      (zero_lt_one.trans s.base_gt_one)).normalizedProfiles
        (G.radius ξ) (G.radius_pos ξ)
  let selected := normalized.restricted
    (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
      (Finset.univ \ out.removed))
  selected.frozenProfiles (D.height ξ)

def frozen_termDictionary (ξ : V) (h : H) :
    ChildHeckeTermDictionary (σ := σ) (out.frozenData ξ)
      (s.row h).momentIdeal (s.extractedFactor h) (s.row h).element :=
  (out.frozen_termCalibration ξ h).toDictionary

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.Calibration.restricted
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozen_parentCharacterRecipe
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozen_termDictionary
