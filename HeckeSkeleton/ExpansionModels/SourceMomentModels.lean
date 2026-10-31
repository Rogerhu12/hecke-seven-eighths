import HeckeSkeleton.Moments
import HeckeSkeleton.ExpansionModels.SharedWitnessRecipe

/-!
# SourceMomentModels generated from a single independent inverse family

This adapter is intentionally separate from the verified Mathlib-only files.
It imports the original, admitted skeleton for its types.  It has no new
admitted declaration, but its import closure is not an axiom-free project.

`SourceModelRecipe` is algebraic/profile data, with no calibration equality,
detector estimate, energy bound, or admissibility predicate as a field.
This generic adapter remains useful independently of the named source.
The named `momentModels` now uses the single raw recipe in `Core.lean` and
`Base.lean`, rather than an independent choice.  That wiring is not a
construction of the still unfinished analytic detector or D-EXPANSION.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.ExpansionRecipe

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The inverse model is already a two-scale family.  Its source index is
represented only through U,D and the common finite-dimensional parameters.
Slot profiles have no row-parameter arguments: they are row-independent. -/
structure SourceModelRecipe where
  dimension : ℕ
  inverseFamily : ℝ → ℝ → SixthUnitClasses K (places K c) →
    (Fin dimension → ℝ) → (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    MomentData K c.family.omega (targetCharacter K c)
  plainTest : ∀ Z T, SourceMomentIndex K c Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) → IdealTest K
  physicalSlot : ∀ Z T, SourceMomentIndex K c Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    Fin c.geometry.slots → PrimeWindow K
  slotCoefficient : ∀ Z T, SourceMomentIndex K c Z T →
    SixthUnitClasses K (places K c) →
    Fin c.geometry.slots → HeckeCharacter K
  heights : ∀ Z T, SourceMomentIndex K c Z T → Fin dimension → ℝ
  realShifts : ∀ Z T, SourceMomentIndex K c Z T →
    NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : ∀ Z T, SourceMomentIndex K c Z T →
    NonzeroIdeal K → Fin dimension → ℝ

variable {K c}

def SourceModelRecipe.physicalGeometry (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (ξ : Fin F.dimension → ℝ) :
    SlotGeometry K where
  slotCount := c.geometry.slots
  slots := F.physicalSlot Z T i s ξ

/-- The nonpositive-shell branch only makes the constructor total.  Actual
retained blocks use the positive branch.  It is not an analytic assertion. -/
def SourceModelRecipe.rowGeometry (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (ξ : Fin F.dimension → ℝ) :
    SlotGeometry K where
  slotCount := c.geometry.slots
  slots j := if h : 0 < (momentBlock i).shell then
    (F.physicalSlot Z T i s ξ j).changeBase (momentBlock i).shell h
    else F.physicalSlot Z T i s ξ j

def SourceModelRecipe.fullModel (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (ξ : Fin F.dimension → ℝ)
    (σ τ : NonzeroIdeal K → Fin F.dimension → ℝ) :
    MomentData K c.family.omega (targetCharacter K c) :=
  { F.inverseFamily (momentBase i)
      ((momentBase i) ^ (momentWitness i).inverseLength) s ξ σ τ with
    plainTest₁ := F.plainTest Z T i s ξ σ τ
    plainTest₂ := F.plainTest Z T i s ξ σ τ
    geometry := F.rowGeometry i s ξ
    slotCoefficient := F.slotCoefficient Z T i s }

/-- Explicit candidate for MI-M-MODELS once the actual detector supplies F.
Inverse/paired are the same full recipe, restricted to the selected slots.
Unmarked retains independent U,D and no source-index argument. -/
def momentModelsFromRecipe (F : SourceModelRecipe K c) : SourceMomentModels K c where
  dimension := F.dimension
  inverse _Z _T i s ξ σ τ := (F.fullModel i s ξ σ τ).restrictSlots i.selected
  paired _Z _T i s ξ σ τ := (F.fullModel i s ξ σ τ).restrictSlots i.selected
  unmarked := F.inverseFamily
  heights := F.heights
  realShifts := F.realShifts
  imagShifts := F.imagShifts

/-- Independent-scale coherence is built into the data constructor; it is
not a later hypothesis about two arbitrary model choices. -/
theorem momentModelsFromRecipe_inverse_unmarked (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) :
    inversePolynomial (inverseModel (momentModelsFromRecipe F) i s) u
      ((momentBase i) ^ (momentWitness i).inverseLength) 0 =
    inversePolynomial (unmarkedModel (momentModelsFromRecipe F) i s) u
      ((momentBase i) ^ (momentWitness i).inverseLength) 0 := rfl

theorem momentModelsFromRecipe_plain_copies (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (pairedModel (momentModelsFromRecipe F) i s)
      (pairedModel (momentModelsFromRecipe F) i s).plainTest₁ u N t =
    plainPolynomial (pairedModel (momentModelsFromRecipe F) i s)
      (pairedModel (momentModelsFromRecipe F) i s).plainTest₂ u N t := rfl

theorem momentModelsFromRecipe_models_equal (F : SourceModelRecipe K c)
    {Z T : ℝ} (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) :
    inverseModel (momentModelsFromRecipe F) i s =
      pairedModel (momentModelsFromRecipe F) i s := rfl

end HeckeSkeleton.ExpansionRecipe
