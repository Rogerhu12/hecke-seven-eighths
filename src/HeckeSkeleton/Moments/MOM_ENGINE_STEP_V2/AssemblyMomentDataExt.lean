module

public import HeckeGeneral.Analysis.MomentInputs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Extensionality for the original moving moment data

These helpers concern only the base data structures. They do not select
a calibration or a child, and do not assume any task statement. Exact
profile identities determine the finite supports. Exact allowed-row
identities determine the exhaustive row enumerations. Slot indices are
transported only along equality of their counts.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

universe u

variable {K : Type} [Field K] [NumberField K]

/-- Exact finite support is determined by the global ideal profile. -/
theorem idealTest_ext_profile {left right : IdealTest K}
    (hprofile : left.profile = right.profile) : left = right := by
  classical
  have hsupport : left.support = right.support := by
    funext row time scale
    apply Finset.ext
    intro I
    rw [left.support_spec, right.support_spec, hprofile]
  cases left
  cases right
  cases hprofile
  cases hsupport
  rfl

/-- A prime window is determined by its length and global profile. -/
theorem primeWindow_ext_profile {left right : PrimeWindow K}
    (hlength : left.length = right.length)
    (hprofile : left.profile = right.profile) : left = right := by
  classical
  have hsupport : left.support = right.support := by
    funext time scale
    apply Finset.ext
    intro q
    rw [left.support_spec, right.support_spec, hprofile]
  cases left
  cases right
  cases hlength
  cases hprofile
  cases hsupport
  rfl

/-- Transport through an intermediate slot count preserves the index
in the common original allocation. -/
theorem finCast_to_common {a b n : ℕ} (ha : a = n) (hb : b = n) (i : Fin a) :
    Fin.cast hb (Fin.cast (ha.trans hb.symm) i) = Fin.cast ha i := by
  apply Fin.ext
  rfl

/-- Pointwise equality after the count transport gives the heterogeneous
function equality required by a dependent slot-coefficient field. -/
theorem fin_fun_heq_of_cast {a b : ℕ} {α : Sort u}
    (hcount : a = b) (left : Fin a → α) (right : Fin b → α)
    (hvalue : ∀ i, left i = right (Fin.cast hcount i)) : HEq left right := by
  cases hcount
  exact heq_of_eq (funext hvalue)

/-- The slots are compared at the same original indices; the transport
does not choose a new ordering or replace a prime window. -/
theorem slotGeometry_ext_cast {left right : SlotGeometry K}
    (hcount : left.slotCount = right.slotCount)
    (hslots : ∀ i, left.slots i = right.slots (Fin.cast hcount i)) :
    left = right := by
  cases left with
  | mk n leftSlots =>
    cases right with
    | mk m rightSlots =>
      cases hcount
      have hslots' : leftSlots = rightSlots := funext hslots
      cases hslots'
      rfl

variable {ω ψ : HeckeCharacter K}

/-- The thirteen non-propositional fields determine the whole moment
record. The row enumeration follows from the allowed-row predicate;
only the slot-coefficient field needs heterogeneous equality because
its domain depends on the geometry's slot count. -/
theorem momentData_ext_fields {left right : MomentData K ω ψ}
    (htheta : left.theta = right.theta)
    (hinverseBackground : left.inverseBackground = right.inverseBackground)
    (hdirection : left.direction = right.direction)
    (hplainBackground : left.plainBackground = right.plainBackground)
    (hrowCharacter : left.rowCharacter = right.rowCharacter)
    (hallowed : left.allowedRow = right.allowedRow)
    (hmask : left.commonMask = right.commonMask)
    (hinverse : left.inverseTest = right.inverseTest)
    (hleft : left.plainTest₁ = right.plainTest₁)
    (hright : left.plainTest₂ = right.plainTest₂)
    (hgeometry : left.geometry = right.geometry)
    (hslotCoefficient : HEq left.slotCoefficient right.slotCoefficient) :
    left = right := by
  classical
  have hrows : left.rows = right.rows := by
    funext cutoff
    apply Finset.ext
    intro row
    rw [left.rows_spec, right.rows_spec, hallowed]
  cases left
  cases right
  cases htheta
  cases hinverseBackground
  cases hdirection
  cases hplainBackground
  cases hrowCharacter
  cases hallowed
  cases hrows
  cases hmask
  cases hinverse
  cases hleft
  cases hright
  cases hgeometry
  have hslot := eq_of_heq hslotCoefficient
  cases hslot
  rfl

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.idealTest_ext_profile
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.primeWindow_ext_profile
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.finCast_to_common
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.fin_fun_heq_of_cast
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.slotGeometry_ext_cast
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.momentData_ext_fields
