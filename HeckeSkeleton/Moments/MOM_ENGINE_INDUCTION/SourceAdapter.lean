import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceData
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Family

/-!
# Exact paired-family map for the generic source data

The transparent source aliases refer directly to the canonical
`HeckeSkeleton.SourceData` interface. Every index, finite sector, evaluated
model, row cutoff and selected slot is retained.  The identifications are definitional and introduce no energy
estimate or analytic input.  This module does not import `Moments.lean`,
so the source declarations can later consume it without an import cycle.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField
open HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)
variable (S : Source.MomentSourceData K c)

local instance sourceAdapterSectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The family uses the one fixed source datum and the original complete
models evaluated at their actual external height and shift parameters. -/
def sourceFamily (M : Source.SourceMomentModelsFor K c S) :
    SourceFamily K c.family.omega (targetCharacter K c)
      (fun Z T => Source.SourceMomentIndexFor K c S Z T)
      (SixthUnitClasses K (places K c)) where
  slots := c.geometry.slots
  kappa := 2 * c.family.B - 1
  mesh := (momentMesh K c.family).val
  loss := c.family.lamA
  rowExponent := S.rowExponent
  shell := fun _ _ i => (Source.momentBlock i).shell
  bin := fun _ _ i => (Source.momentBlock i).bin
  plainLength := fun _ _ i => (Source.momentWitness i).plainLength
  selected := fun _ _ i => i.selected
  noSlots := fun _ _ i => i.noSlots
  noSlots_shell := fun _ _ _ => rfl
  noSlots_bin := fun _ _ _ => rfl
  noSlots_plainLength := fun _ _ _ => rfl
  noSlots_selected := fun _ _ _ => rfl
  model := fun _ _ i s => Source.pairedModel M i s

variable {K c S}

@[simp] theorem sourceFamily_base (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).base i = Source.momentBase i := rfl

@[simp] theorem sourceFamily_rowWidth (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).rowWidth i = Source.rowWidth i := rfl

@[simp] theorem sourceFamily_selectedLength (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).selectedLength i = Source.selectedLength i := rfl

@[simp] theorem sourceFamily_parameters (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).parameters i = Source.pairedParameters i := rfl

@[simp] theorem sourceFamily_capacity (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).capacity i ↔ Source.pairedCapacity i := Iff.rfl

@[simp] theorem sourceFamily_energy (M : Source.SourceMomentModelsFor K c S)
    {Z T : ℝ} (i : Source.SourceMomentIndexFor K c S Z T) :
    (sourceFamily K c S M).energy i = Source.pairedModelEnergy M i := rfl

@[simp] theorem sourceFamily_uniformBound (M : Source.SourceMomentModelsFor K c S)
    (E power : ∀ Z T, Source.SourceMomentIndexFor K c S Z T → ℝ)
    (eligible : ∀ Z T, Source.SourceMomentIndexFor K c S Z T → Prop) :
    (sourceFamily K c S M).UniformBound E power eligible ↔
      Source.UniformMomentBound E power eligible := Iff.rfl

@[simp] theorem sourceFamily_zeroSlotBound (M : Source.SourceMomentModelsFor K c S) :
    (sourceFamily K c S M).ZeroSlotBound ↔
      Source.UniformMomentBound (fun _ _ i => Source.pairedModelEnergy M i.noSlots)
        (fun _ _ i => Source.rowWidth i) (fun _ _ _ => True) := Iff.rfl

@[simp] theorem sourceFamily_positiveSlotBound (M : Source.SourceMomentModelsFor K c S) :
    (sourceFamily K c S M).PositiveSlotBound ↔
      Source.UniformMomentBound (fun _ _ i => Source.pairedModelEnergy M i)
        (fun _ _ i => Source.rowWidth i)
        (fun _ _ i => Source.pairedCapacity i ∧ i.selected.Nonempty) := Iff.rfl

@[simp] theorem sourceFamily_primeProductBound
    (M : Source.SourceMomentModelsFor K c S) (κ : ℝ) :
    (sourceFamily K c S M).PrimeProductBound κ ↔
      Source.PairedPrimeProductBound M κ := Iff.rfl

end HeckeSkeleton.Moments.EngineInduction
