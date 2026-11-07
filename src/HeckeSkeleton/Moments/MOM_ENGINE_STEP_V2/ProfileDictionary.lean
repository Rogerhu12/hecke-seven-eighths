module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormula

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Global original-profile dictionaries for a calibrated source

Every formula names an actual parent representative. Its equality with
the child profile holds at all real arguments, for every row and time.
The side, rectangle and passive-allocation choices do not create a new
class of profile operations. The fixed shape and scalar allowance are
parameters supplied by the uniform construction certificate.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

inductive ParentProfileKind (call : Call c) where
  | inverse
  | plain (side : Bool)
  | prime (slot : Fin call.node.data.geometry.slotCount)

namespace ParentProfileKind

def representative {call : Call c} (kind : ParentProfileKind call)
    (input : ProfileInput call) (row : NonzeroIdeal K) (time : ℝ) : 𝓢(ℝ, ℂ) :=
  match kind with
  | .inverse => input.raw.inverseRep row time
  | .plain false => input.raw.leftRep row time
  | .plain true => input.raw.rightRep row time
  | .prime slot => input.raw.primeRep slot time

end ParentProfileKind

/-- The source selects one actual parent profile before the two new
Fourier variables. The equality is of whole Schwartz functions. -/
structure OriginalProfileFormula {call : Call c} (input : ProfileInput call) where
  kind : ParentProfileKind call
  row : NonzeroIdeal K
  time : ℝ
  formula : ProfileFormula
  original : formula.original = kind.representative input row time

namespace OriginalProfileFormula

variable {call : Call c} {input : ProfileInput call}

structure Bounded (f : OriginalProfileFormula input)
    (shape : ProfileShape) (scalarBound : ℝ) (window : Set ℝ) : Prop where
  shape_bound : f.formula.Bounded shape
  scalar : ‖f.formula.scalar‖ ≤ scalarBound
  support : f.formula.window (call.prepared.lower / 2)
    (2 * call.prepared.upper) ⊆ window

end OriginalProfileFormula

/-- This is the single global dictionary used by the raw-profile task.
Its only inequalities are explicit individual shape/scalar/support
conditions; it includes no capacity, child-energy or aggregate estimate. -/
structure GlobalProfileDictionary {call : Call c} (input : ProfileInput call)
    (data : EngineParameter → MomentData K c.family.omega (targetCharacter K c))
    (slots : ℕ) (count : ∀ ξ, (data ξ).geometry.slotCount = slots)
    (shape : ProfileShape) (scalarBound : ℝ) (window : Set ℝ) where
  slotEmbedding : Fin slots → Fin call.node.data.geometry.slotCount
  slotEmbedding_injective : Function.Injective slotEmbedding
  inverse : NonzeroIdeal K → ℝ → OriginalProfileFormula input
  plain : Bool → NonzeroIdeal K → ℝ → OriginalProfileFormula input
  prime : Fin slots → ℝ → OriginalProfileFormula input
  inverse_kind : ∀ u t, (inverse u t).kind = .inverse
  plain_kind : ∀ side u t, (plain side u t).kind = .plain side
  prime_kind : ∀ i t, (prime i t).kind = .prime (slotEmbedding i)
  inverse_bounded : ∀ u t, (inverse u t).Bounded shape scalarBound window
  plain_bounded : ∀ side u t, (plain side u t).Bounded shape scalarBound window
  prime_bounded : ∀ i t, (prime i t).Bounded shape scalarBound window
  inverse_eq : ∀ ξ u t x,
    (data ξ).inverseTest.profile u t x = (inverse u t).formula.value ξ x
  left_eq : ∀ ξ u t x,
    (data ξ).plainTest₁.profile u t x = (plain false u t).formula.value ξ x
  right_eq : ∀ ξ u t x,
    (data ξ).plainTest₂.profile u t x = (plain true u t).formula.value ξ x
  prime_eq : ∀ ξ (i : Fin (data ξ).geometry.slotCount) t x,
    ((data ξ).geometry.slots i).profile t x =
      (prime (Fin.cast (count ξ) i) t).formula.value ξ x

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
