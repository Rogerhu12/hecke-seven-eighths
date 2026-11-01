import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput

/-!
# Original analytic profiles on the actual passive branches

An occurrence allocation changes the two norm scales and retains a
subset of the prime slots.  Its smooth functions are exactly the old
functions.  The original Schwartz representatives, seminorm bounds and
open prime annulus therefore pass to the allocated table without an
extra analytic cost.

The final constructors use the actual enlarged smooth table and the
actual live passive label.  Their input is the already computed
original profile certificate; no finished branch window is assumed.
The clipping cost still uses the new branch's actual parameters.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable (E : W.SchwartzModel window)

/-- The actual allocation preserves both plain representatives and
selects the original representatives of exactly the retained slots. -/
def allocate (allocation : ActualColumnAllocation K k) :
    (W.allocate allocation).SchwartzModel window where
  left := E.left
  right := E.right
  slot j := E.slot (SlotRestriction.index allocation.keep j)
  left_eq := E.left_eq
  right_eq := E.right_eq
  slot_eq j := E.slot_eq (SlotRestriction.index allocation.keep j)
  left_support := E.left_support
  right_support := E.right_support
  slot_support j := E.slot_support (SlotRestriction.index allocation.keep j)

@[simp] theorem allocate_left (allocation : ActualColumnAllocation K k) (r : Bool) :
    (E.allocate allocation).left r = E.left r := rfl

@[simp] theorem allocate_right (allocation : ActualColumnAllocation K k) (r : Bool) :
    (E.allocate allocation).right r = E.right r := rfl

@[simp] theorem allocate_slot (allocation : ActualColumnAllocation K k)
    (j : Fin allocation.keep.card) :
    (E.allocate allocation).slot j = E.slot (SlotRestriction.index allocation.keep j) := rfl

theorem allocate_prime_support (allocation : ActualColumnAllocation K k)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    ∀ j, Function.support ((E.allocate allocation).slot j) ⊆ Set.Ioo (1 : ℝ) 2 :=
  fun j => hprime (SlotRestriction.index allocation.keep j)

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

namespace CanonicalLiteralFullKappaInput.ComputedProfiles

variable {s : Finset (ℕ × ℕ)} {originalBound : ℝ}
variable (T : CanonicalLiteralFullKappaInput.ComputedProfiles W window s originalBound)

/-- All finite orders and numerical bounds were selected before the
passive label.  The actual quotient operation preserves them. -/
def allocate (allocation : ActualColumnAllocation K k) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (W.allocate allocation) window s originalBound where
  model := T.model.allocate allocation
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  original_bound := T.original_bound
  left_bound := T.left_bound
  right_bound := T.right_bound
  slot_bound r j := T.slot_bound r (SlotRestriction.index allocation.keep j)
  prime_window := T.model.allocate_prime_support allocation T.prime_window

@[simp] theorem allocate_bound (allocation : ActualColumnAllocation K k) :
    (T.allocate allocation).bound = T.bound := rfl

@[simp] theorem allocate_rawCoefficient (allocation : ActualColumnAllocation K k)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.allocate allocation).rawCoefficient hcompact hpositive firstSign rectangle =
      T.rawCoefficient hcompact hpositive firstSign rectangle := rfl

/-- This compares the two certificates at the same explicit parameter
record. It does not identify different branch clipping parameters. -/
@[simp] theorem allocate_coefficient (allocation : ActualColumnAllocation K k)
    (Z : ℝ) (parameters : RealParameters)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.allocate allocation).coefficient Z parameters hcompact hpositive firstSign rectangle =
      T.coefficient Z parameters hcompact hpositive firstSign rectangle := rfl

/-- The complete smooth carrier only replaces finite supports and
the arithmetic characters. Its individual norm functions are unchanged. -/
def passiveTable (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (CanonicalLiteralPassiveSource.profiles W allocation A paid) window s originalBound :=
  (T.allocate allocation).reprofile
    (CanonicalLiteralPassiveSource.profiles W allocation A paid)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem passiveTable_bound (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card) :
    (T.passiveTable allocation A paid).bound = T.bound := rfl

/-- A genuine live passive label gives its own quotient table. The
certificate is constructed by the two actual occurrence restrictions. -/
def passiveBranch (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((CanonicalLiteralPassiveSource.profiles W allocation A paid).allocate
        (CanonicalLiteralPassiveSource.branch W allocation A M a)) window s originalBound :=
  (T.passiveTable allocation A paid).allocate
    (CanonicalLiteralPassiveSource.branch W allocation A M a)

@[simp] theorem passiveBranch_bound (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    (T.passiveBranch allocation A paid M a).bound = T.bound := rfl

@[simp] theorem passiveBranch_slot (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })
    (j : Fin (CanonicalLiteralPassiveSource.branch W allocation A M a).keep.card) :
    (T.passiveBranch allocation A paid M a).model.slot j =
      T.model.slot (SlotRestriction.index allocation.keep
        (SlotRestriction.index (CanonicalLiteralPassiveSource.branch W allocation A M a).keep j)) :=
  rfl

theorem passiveBranch_prime_support (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    ∀ j, Function.support ((T.passiveBranch allocation A paid M a).model.slot j) ⊆
      Set.Ioo (1 : ℝ) 2 :=
  (T.passiveBranch allocation A paid M a).prime_window

@[simp] theorem passiveBranch_rawCoefficient (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.passiveBranch allocation A paid M a).rawCoefficient hcompact hpositive firstSign rectangle =
      T.rawCoefficient hcompact hpositive firstSign rectangle := rfl

end CanonicalLiteralFullKappaInput.ComputedProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.allocate
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.ComputedProfiles.allocate
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.ComputedProfiles.passiveTable
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.ComputedProfiles.passiveBranch
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.ComputedProfiles.passiveBranch_prime_support
