import HeckeSkeleton.Moments
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceConsumers

/-!
# Exact migration map from the existing source types

This integration adapter retains the original expansion, all dependent
index fields, all finite sectors and the complete model data.  It does
not construct a second expansion or model family.  The constant row
exponent records the current skeleton's literal `m = 1` convention; the
shared dyadic correction can change that one choice together with the
corresponding parameter identifications.

Unlike the generic source modules, this file imports `Moments.lean`.
Its declarations therefore inherit the unfinished global expansion's
axiom dependency and belong only to the separate source-integration
audit.  None of the equivalences below removes that dependency.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.TIP

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The one original expansion, with its current literal row exponent.
There is no default or alternate unfinished choice in the generic API. -/
def skeletonMomentSourceData : Source.MomentSourceData K c where
  expansion := (targetData K c).expansion
  rowExponent := fun _ => 1

variable {K c} {Z T : ℝ}

/-- All seven fields of the original index, without discarding slots. -/
def sourceIndexOfSkeleton (i : SourceMomentIndex K c Z T) :
    Source.SourceMomentIndexFor K c (skeletonMomentSourceData K c) Z T :=
  ⟨i.block, i.label, i.t, i.t_lower, i.t_upper, i.subdivision, i.selected⟩

/-- The inverse index map retains the same block and witness proof fields. -/
def sourceIndexToSkeleton
    (i : Source.SourceMomentIndexFor K c (skeletonMomentSourceData K c) Z T) :
    SourceMomentIndex K c Z T :=
  ⟨i.block, i.label, i.t, i.t_lower, i.t_upper, i.subdivision, i.selected⟩

@[simp] theorem sourceIndexToSkeleton_ofSkeleton (i : SourceMomentIndex K c Z T) :
    sourceIndexToSkeleton (sourceIndexOfSkeleton i) = i := by
  cases i
  rfl

@[simp] theorem sourceIndexOfSkeleton_toSkeleton
    (i : Source.SourceMomentIndexFor K c (skeletonMomentSourceData K c) Z T) :
    sourceIndexOfSkeleton (sourceIndexToSkeleton i) = i := by
  cases i
  rfl

/-- The migration preserves the complete scale-dependent index type. -/
def skeletonSourceIndexEquiv :
    SourceMomentIndex K c Z T ≃
      Source.SourceMomentIndexFor K c (skeletonMomentSourceData K c) Z T where
  toFun := sourceIndexOfSkeleton
  invFun := sourceIndexToSkeleton
  left_inv := sourceIndexToSkeleton_ofSkeleton
  right_inv := sourceIndexOfSkeleton_toSkeleton

@[simp] theorem sourceIndexOfSkeleton_noSlots (i : SourceMomentIndex K c Z T) :
    sourceIndexOfSkeleton i.noSlots = (sourceIndexOfSkeleton i).noSlots := rfl

@[simp] theorem sourceIndexToSkeleton_noSlots
    (i : Source.SourceMomentIndexFor K c (skeletonMomentSourceData K c) Z T) :
    sourceIndexToSkeleton i.noSlots = (sourceIndexToSkeleton i).noSlots := rfl

@[simp] theorem sourceIndexOfSkeleton_base (i : SourceMomentIndex K c Z T) :
    Source.momentBase (sourceIndexOfSkeleton i) = momentBase i := rfl

@[simp] theorem sourceIndexOfSkeleton_inverseParameters
    (i : SourceMomentIndex K c Z T) :
    Source.inverseParameters (sourceIndexOfSkeleton i) = inverseParameters i := rfl

@[simp] theorem sourceIndexOfSkeleton_pairedParameters
    (i : SourceMomentIndex K c Z T) :
    Source.pairedParameters (sourceIndexOfSkeleton i) = pairedParameters i := rfl

@[simp] theorem sourceIndexOfSkeleton_inverseCapacity
    (i : SourceMomentIndex K c Z T) :
    Source.inverseCapacity (sourceIndexOfSkeleton i) ↔ inverseCapacity i := Iff.rfl

@[simp] theorem sourceIndexOfSkeleton_pairedCapacity
    (i : SourceMomentIndex K c Z T) :
    Source.pairedCapacity (sourceIndexOfSkeleton i) ↔ pairedCapacity i := Iff.rfl

/-- Reuse all seven original model fields.  In particular the unmarked
model still has independent `U,D`, rather than a source-index argument. -/
def sourceModelsOfSkeleton (M : SourceMomentModels K c) :
    Source.SourceMomentModelsFor K c (skeletonMomentSourceData K c) where
  dimension := M.dimension
  inverse Z T i := M.inverse Z T (sourceIndexToSkeleton i)
  paired Z T i := M.paired Z T (sourceIndexToSkeleton i)
  unmarked := M.unmarked
  heights Z T i := M.heights Z T (sourceIndexToSkeleton i)
  realShifts Z T i := M.realShifts Z T (sourceIndexToSkeleton i)
  imagShifts Z T i := M.imagShifts Z T (sourceIndexToSkeleton i)

@[simp] theorem sourceModelsOfSkeleton_inverseModel (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) (s : SixthUnitClasses K (places K c)) :
    Source.inverseModel (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) s =
      inverseModel M i s := by
  cases i
  rfl

@[simp] theorem sourceModelsOfSkeleton_pairedModel (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) (s : SixthUnitClasses K (places K c)) :
    Source.pairedModel (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) s =
      pairedModel M i s := by
  cases i
  rfl

@[simp] theorem sourceModelsOfSkeleton_unmarkedModel (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) (s : SixthUnitClasses K (places K c)) :
    Source.unmarkedModel (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) s =
      unmarkedModel M i s := by
  cases i
  rfl

@[simp] theorem sourceModelsOfSkeleton_markedEnergy (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) :
    Source.markedModelEnergy (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) =
      markedModelEnergy M i := by
  cases i
  rfl

@[simp] theorem sourceModelsOfSkeleton_pairedEnergy (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) :
    Source.pairedModelEnergy (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) =
      pairedModelEnergy M i := by
  cases i
  rfl

@[simp] theorem sourceModelsOfSkeleton_amplifiedEnergy (M : SourceMomentModels K c)
    (i : SourceMomentIndex K c Z T) :
    Source.amplifiedModelEnergy (sourceModelsOfSkeleton M) (sourceIndexOfSkeleton i) =
      amplifiedModelEnergy M i := by
  cases i
  rfl

@[simp] theorem sourceIndexOfSkeleton_physicalPlainEnergy
    (i : SourceMomentIndex K c Z T) :
    Source.physicalPlainEnergy (sourceIndexOfSkeleton i) = physicalPlainEnergy i := rfl

/-- No uniform quantifier is moved by the dependent index equivalence. -/
theorem skeleton_uniformMomentBound_iff
    (E power : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndex K c Z T → Prop) :
    Source.UniformMomentBound
      (fun Z T i => E Z T (sourceIndexToSkeleton i))
      (fun Z T i => power Z T (sourceIndexToSkeleton i))
      (fun Z T i => eligible Z T (sourceIndexToSkeleton i)) ↔
        UniformMomentBound E power eligible := by
  constructor
  · rintro ⟨A, ceiling, hA, hc, hb⟩
    refine ⟨A, ceiling, hA, hc, ?_⟩
    intro τ hτ hτc
    obtain ⟨Z₀, C, hZ₀, hC, hbound⟩ := hb τ hτ hτc
    refine ⟨Z₀, C, hZ₀, hC, ?_⟩
    intro Z hZ i hbin heligible
    simpa only [sourceIndexToSkeleton_ofSkeleton, sourceIndexOfSkeleton_base] using
      hbound Z hZ (sourceIndexOfSkeleton i) hbin heligible
  · rintro ⟨A, ceiling, hA, hc, hb⟩
    refine ⟨A, ceiling, hA, hc, ?_⟩
    intro τ hτ hτc
    obtain ⟨Z₀, C, hZ₀, hC, hbound⟩ := hb τ hτ hτc
    refine ⟨Z₀, C, hZ₀, hC, ?_⟩
    intro Z hZ i hbin heligible
    exact hbound Z hZ (sourceIndexToSkeleton i) hbin heligible

/-- The original unrestricted zero-slot target has exactly the generic
source statement, evaluated at the same no-slot models. -/
theorem skeleton_zeroSlotBound_iff (M : SourceMomentModels K c) :
    Source.UniformMomentBound
      (fun _ _ i => Source.pairedModelEnergy (sourceModelsOfSkeleton M) i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True) ↔
    UniformMomentBound (fun _ _ i => pairedModelEnergy M i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True) := by
  exact skeleton_uniformMomentBound_iff
    (fun _ _ i => pairedModelEnergy M i.noSlots) (fun _ _ _ => 1) (fun _ _ _ => True)

/-- The original positive-slot target keeps the exact physical capacity
and every selected slot under the generic source map. -/
theorem skeleton_positiveSlotBound_iff (M : SourceMomentModels K c) :
    Source.UniformMomentBound
      (fun _ _ i => Source.pairedModelEnergy (sourceModelsOfSkeleton M) i)
      (fun _ _ _ => 1)
      (fun _ _ i => Source.pairedCapacity i ∧ i.selected.Nonempty) ↔
    UniformMomentBound (fun _ _ i => pairedModelEnergy M i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  exact skeleton_uniformMomentBound_iff (fun _ _ i => pairedModelEnergy M i)
    (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty)

/-- The independent prime-product input uses the same rows, masks,
physical exponent and finite sectors after the source-type migration. -/
theorem skeleton_primeProductBound_iff (M : SourceMomentModels K c) (κ : ℝ) :
    Source.PairedPrimeProductBound (sourceModelsOfSkeleton M) κ ↔
      PairedPrimeProductBound K c M κ := by
  unfold Source.PairedPrimeProductBound PairedPrimeProductBound
  exact skeleton_uniformMomentBound_iff _ _ _

/-- The clean source consumer reaches the original `PSource` statement
after exact reindexing.  The hypotheses are the proved model estimates and
the original finite-sector comparison, not an assumed physical source. -/
theorem skeleton_plainSource_of_generic_model_bounds (M : SourceMomentModels K c)
    (hpositive : Source.UniformMomentBound
      (fun _ _ i => Source.pairedModelEnergy (sourceModelsOfSkeleton M) i)
      (fun _ _ _ => 1)
      (fun _ _ i => Source.pairedCapacity i ∧ i.selected.Nonempty))
    (hzero : Source.UniformMomentBound
      (fun _ _ i => Source.pairedModelEnergy (sourceModelsOfSkeleton M) i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True))
    (hreindex : ∀ Z T (i : SourceMomentIndex K c Z T),
      physicalPlainEnergy i ≤ pairedModelEnergy M i) :
    PSource c.geometry (targetData K c) c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  apply Source.plainSource_of_model_bounds (sourceModelsOfSkeleton M)
    (targetData K c) rfl rfl hpositive hzero
  intro Z T i
  exact hreindex Z T (sourceIndexToSkeleton i)

end HeckeSkeleton.Moments.EngineInduction
