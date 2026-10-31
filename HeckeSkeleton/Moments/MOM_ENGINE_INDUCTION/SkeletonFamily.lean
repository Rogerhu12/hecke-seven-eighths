import HeckeSkeleton.Moments
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Induction

/-!
# Exact specialization to the exploratory source skeleton

This file records the definitionally exact map to the original source
indices, masks, sectors and finite energies.  It does not construct the
unfinished expansion or moment models.  At the task's base revision,
`SourceMomentIndex` already depends on `highExpansion`, whose construction
is admitted.  Therefore the declarations in this specialization inherit
that upstream axiom dependency; the general induction and `Family.lean`
are deliberately independent of it.

The conditional wrappers below also require an assembly of the parent
reduction, using finite sums or finite positive child measures.  That
hypothesis is stronger than the published
`EngineStep.paired_child_step`, which controls an already produced child.
This file does not construct the missing parent assembly.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

universe u

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local instance : Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The actual source family, retaining every selected slot and every
original unit sector.  External heights are evaluated exactly as in
`pairedModel`. -/
def actualSourceFamily (M : SourceMomentModels K c) :
    SourceFamily K c.family.omega (targetCharacter K c)
      (fun Z T => SourceMomentIndex K c Z T) (SixthUnitClasses K (places K c)) where
  slots := c.geometry.slots
  kappa := 2 * c.family.B - 1
  mesh := (momentMesh K c.family).val
  loss := c.family.lamA
  shell := fun _ _ i => (momentBlock i).shell
  bin := fun _ _ i => (momentBlock i).bin
  plainLength := fun _ _ i => (momentWitness i).plainLength
  selected := fun _ _ i => i.selected
  noSlots := fun _ _ i => i.noSlots
  noSlots_shell := fun _ _ _ => rfl
  noSlots_bin := fun _ _ _ => rfl
  noSlots_plainLength := fun _ _ _ => rfl
  noSlots_selected := fun _ _ _ => rfl
  model := fun _ _ i s => pairedModel M i s

variable {K c}

@[simp] theorem actualSourceFamily_base (M : SourceMomentModels K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T) :
    (actualSourceFamily K c M).base i = momentBase i := rfl

@[simp] theorem actualSourceFamily_selectedLength (M : SourceMomentModels K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T) :
    (actualSourceFamily K c M).selectedLength i = selectedLength i := rfl

@[simp] theorem actualSourceFamily_parameters (M : SourceMomentModels K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T) :
    (actualSourceFamily K c M).parameters i = pairedParameters i := rfl

@[simp] theorem actualSourceFamily_capacity (M : SourceMomentModels K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T) :
    (actualSourceFamily K c M).capacity i ↔ pairedCapacity i := Iff.rfl

@[simp] theorem actualSourceFamily_energy (M : SourceMomentModels K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T) :
    (actualSourceFamily K c M).energy i = pairedModelEnergy M i := rfl

@[simp] theorem actualSourceFamily_uniformBound (M : SourceMomentModels K c)
    (E power : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndex K c Z T → Prop) :
    (actualSourceFamily K c M).UniformBound E power eligible ↔
      UniformMomentBound E power eligible := Iff.rfl

@[simp] theorem actualSourceFamily_zeroSlotBound (M : SourceMomentModels K c) :
    (actualSourceFamily K c M).ZeroSlotBound ↔
      UniformMomentBound (fun _ _ i => pairedModelEnergy M i.noSlots)
        (fun _ _ _ => 1) (fun _ _ _ => True) := Iff.rfl

@[simp] theorem actualSourceFamily_positiveSlotBound (M : SourceMomentModels K c) :
    (actualSourceFamily K c M).PositiveSlotBound ↔
      UniformMomentBound (fun _ _ i => pairedModelEnergy M i)
        (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := Iff.rfl

@[simp] theorem actualSourceFamily_primeProductBound
    (M : SourceMomentModels K c) (κ : ℝ) :
    (actualSourceFamily K c M).PrimeProductBound κ ↔
      PairedPrimeProductBound K c M κ := Iff.rfl

/-- Conditional source zero-slot statement with the parent reduction
explicit.  Its conclusion is the original unrestricted uniform
bound.  The original skeleton declaration has no argument for this
additional assembly hypothesis. -/
theorem paired_zero_slot_models_of_parent_reduction (M : SourceMomentModels K c)
    (hassembly : ParentReductionInput.{u} (actualSourceFamily K c M)
      (fun _ _ i => i.noSlots) (fun _ _ _ => True)) :
    UniformMomentBound (fun _ _ i => pairedModelEnergy M i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True) := by
  exact (actualSourceFamily_zeroSlotBound M).mp
    (paired_zero_slot_models (actualSourceFamily K c M) hassembly)

/-- Conditional positive-slot source statement below the endpoint,
retaining the original prime-product premise and exact source capacity,
and displaying the additional parent-assembly hypothesis. -/
theorem paired_positive_below_one_of_parent_reduction (M : SourceMomentModels K c)
    (hB : c.family.B < 1)
    (hprime : PairedPrimeProductBound K c M (2 * c.family.B - 1))
    (hassembly : c.family.B < 1 →
      PairedPrimeProductBound K c M (2 * c.family.B - 1) →
        Nonempty (ParentReductionInput.{u} (actualSourceFamily K c M)
          (fun _ _ i => i)
          (fun _ _ i => (actualSourceFamily K c M).positiveEligible i))) :
    UniformMomentBound (fun _ _ i => pairedModelEnergy M i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  have hκ : (actualSourceFamily K c M).kappa < 1 := by
    change 2 * c.family.B - 1 < 1
    linarith
  exact (actualSourceFamily_positiveSlotBound M).mp
    (paired_positive_below_one (actualSourceFamily K c M) hκ
      ((actualSourceFamily_primeProductBound M (2 * c.family.B - 1)).mpr hprime)
      (fun _ _ => hassembly hB hprime))

/-- Conditional exact endpoint statement.  The parent assembly takes the
absolute endpoint prime-product bound, with no zero-free premise. -/
theorem paired_positive_endpoint_of_parent_reduction (M : SourceMomentModels K c)
    (hB : c.family.B = 1)
    (hprime : PairedPrimeProductBound K c M 1)
    (hassembly : c.family.B = 1 → PairedPrimeProductBound K c M 1 →
      Nonempty (ParentReductionInput.{u} (actualSourceFamily K c M)
        (fun _ _ i => i)
        (fun _ _ i => (actualSourceFamily K c M).positiveEligible i))) :
    UniformMomentBound (fun _ _ i => pairedModelEnergy M i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  have hκ : (actualSourceFamily K c M).kappa = 1 := by
    change 2 * c.family.B - 1 = 1
    linarith
  exact (actualSourceFamily_positiveSlotBound M).mp
    (paired_positive_endpoint (actualSourceFamily K c M) hκ
      ((actualSourceFamily_primeProductBound M 1).mpr hprime)
      (fun _ _ => hassembly hB hprime))

end HeckeSkeleton.Moments.EngineInduction
