import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaPrime

/-!
# One finite original profile window for the complete engine

The output orders, independent exceptional-volume orders and the
single-character prime orders are joined before any original profile
or moving source is supplied. Restriction keeps the exact same Schwartz
representatives on each actual side. The first and twice-transformed
windows therefore come from one primitive finite seminorm bound.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineProfileOrders

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

def orders (output volume : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (output ∪ volume) ∪ CanonicalFullKappaPrime.orders

def originalOrders (output volume : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  OriginalProfileAtomBounds.profileOrders (orders output volume) ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders (orders output volume))

theorem output_subset (output volume : Finset (ℕ × ℕ)) : output ⊆ orders output volume := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)

theorem volume_subset (output volume : Finset (ℕ × ℕ)) : volume ⊆ orders output volume := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hp)

theorem prime_subset (output volume : Finset (ℕ × ℕ)) :
    CanonicalFullKappaPrime.orders ⊆ orders output volume := Finset.subset_union_right

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {d : MomentData K ω ψ} {amplitude : ℝ}
variable {output volume : Finset (ℕ × ℕ)}

def firstWindow
    (raw : RawProfileWindow rowDomain heightDomain window
      (originalOrders output volume) d amplitude) :
    RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders (orders output volume)) d amplitude :=
  raw.restrictOrders Finset.subset_union_left

def secondWindow
    (raw : RawProfileWindow rowDomain heightDomain window
      (originalOrders output volume) d amplitude) :
    RawProfileWindow rowDomain heightDomain window
      (CanonicalLogProfiles.sourceOrders
        (CanonicalLogProfiles.sourceOrders (orders output volume))) d amplitude :=
  raw.restrictOrders Finset.subset_union_right

@[simp] theorem firstWindow_primeRep
    (raw : RawProfileWindow rowDomain heightDomain window
      (originalOrders output volume) d amplitude) :
    (firstWindow raw).primeRep = raw.primeRep := rfl

@[simp] theorem secondWindow_primeRep
    (raw : RawProfileWindow rowDomain heightDomain window
      (originalOrders output volume) d amplitude) :
    (secondWindow raw).primeRep = raw.primeRep := rfl

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineProfileOrders

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineProfileOrders.firstWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineProfileOrders.secondWindow
