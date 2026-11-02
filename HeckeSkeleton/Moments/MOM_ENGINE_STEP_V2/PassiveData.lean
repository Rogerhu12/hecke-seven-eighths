import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileDictionary

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original smooth supports and the residual coprimality expansion

The carrier is restored from the original smooth profiles, not from the
already masked second-allocation carrier. Both comparison rectangles
use one union of their actual quotient-scale supports. The fixed bad
primes and the paid moving support remain excluded occurrence by
occurrence. Only primes in `fullDeletion` absent from `paidSupport` are
expanded by finite Mobius inversion.

The coefficient task must prove that the paid source vanishes outside
its paid coprimality gate. Thus this restoration never removes a paid
mask. Every passive label is a genuine divisor and occurrence allocation
on this fixed carrier, with its actual sign and no duplicate labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global WholeAllocation

variable {K : Type} [Field K] [NumberField K]

variable {c : TargetContext K} {call : Call c}

/-- A single side's original smooth functions and actual quotient
scales. The formula is fixed globally, including dilation and scalar.
The two Boolean arguments are comparison rectangle and plain factor. -/
structure SmoothSideSupport (input : ProfileInput call) (k : ℕ) where
  slotEmbedding : Fin k → Fin call.node.data.geometry.slotCount
  slotEmbedding_injective : Function.Injective slotEmbedding
  plain : Bool → Bool → OriginalProfileFormula input
  plain_kind : ∀ rectangle side, (plain rectangle side).kind = .plain side
  plainScale : Bool → Bool → ℝ
  plainScale_pos : ∀ rectangle side, 0 < plainScale rectangle side
  prime : Fin k → OriginalProfileFormula input
  prime_kind : ∀ i, (prime i).kind = .prime (slotEmbedding i)
  prime_dilation : ∀ i, (prime i).formula.dilation = 1

namespace SmoothSideSupport

variable {input : ProfileInput call} {k : ℕ} (S : SmoothSideSupport input k)

def plainTest (_S : SmoothSideSupport input k) (side : Bool) : IdealTest K :=
  if side then call.node.data.plainTest₂ else call.node.data.plainTest₁

def rectangleSupport (rectangle side : Bool) : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  let f := S.plain rectangle side
  if f.formula.scalar = 0 then ∅ else
    (S.plainTest side).support f.row f.time
      (S.plainScale rectangle side / f.formula.dilation)

def smoothPlain (side : Bool) : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  S.rectangleSupport false side ∪ S.rectangleSupport true side

def length (i : Fin k) : ℝ :=
  (call.node.data.geometry.slots (S.slotEmbedding i)).length

def smoothSlot (i : Fin k) : Finset (HeightOneSpectrum (𝓞 K)) :=
  if (S.prime i).formula.scalar = 0 then ∅ else
    (call.node.data.geometry.slots (S.slotEmbedding i)).support
      (S.prime i).time (call.base ^ S.length i)

/-- These two gates remain in force before and after passive expansion.
The moving gate is the paid support, not the whole first deletion set. -/
def plainCarrier (paid : (Arithmetic.data c).Exterior) (side : Bool) :
    Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (S.smoothPlain side).filter
    (fun I => IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val)

def slotCarrier (paid : (Arithmetic.data c).Exterior) (i : Fin k) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (S.smoothSlot i).filter
    (fun q => IsCoprime q.asIdeal (Arithmetic.data c).cS ∧ IsCoprime q.asIdeal paid.val)

end SmoothSideSupport

namespace PassiveAllocation

abbrev Key (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  Σ D : Ideal (𝓞 K), primeSupport D → Finset (Fin (k + 2))

def candidates (mask : Ideal (𝓞 K)) (k : ℕ) : Finset (Key K k) :=
  (idealDivisors mask).sigma (fun D => AllocationMass.idealAllocations D (k + 2))

def sign {k : ℕ} (a : Key K k) : ℂ :=
  (moebius a.1 : ℂ) * AllocationMass.sign (primeSupport a.1) a.2

def idealCarrier (s : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) : Finset (Ideal (𝓞 K)) :=
  s.image (fun I => I.val)

/-- A carrier is computed from one smooth-support dictionary; it is
not the old allocation's already truncated `childPlain` support. -/
structure Carrier (K : Type) [Field K] [NumberField K] (k : ℕ) where
  plain : Bool → Finset (HeckeGeneral.Analysis.NonzeroIdeal K)
  slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))

variable {k : ℕ} (B : Carrier K k)

def columns (a : Key K k) : Finset (AllocationColumn K k) :=
  pairedAllocatedColumns a.1 a.2 (idealCarrier (B.plain false))
    (idealCarrier (B.plain true)) B.slots id id HeightOneSpectrum.asIdeal

def labels (mask : Ideal (𝓞 K)) : Finset (Key K k) :=
  (candidates mask k).filter (fun a => sign a ≠ 0 ∧ (columns B a).Nonempty)

/-- The witness comes from this exact restored finite carrier. -/
def allocation (mask : Ideal (𝓞 K)) (a : labels B mask) :
    ActualColumnAllocation K k where
  divisor := a.val.1
  selection := a.val.2
  plain₁ := idealCarrier (B.plain false)
  plain₂ := idealCarrier (B.plain true)
  slots := B.slots
  plain₁_nonzero := by
    intro I hI
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
    exact nonZeroDivisors.coe_ne_zero J
  plain₂_nonzero := by
    intro I hI
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
    exact nonZeroDivisors.coe_ne_zero J
  witness := (Finset.mem_filter.mp a.property).2.2.choose
  witness_mem := (Finset.mem_filter.mp a.property).2.2.choose_spec

end PassiveAllocation

namespace SmoothSideSupport

variable {input : ProfileInput call} {k : ℕ} (S : SmoothSideSupport input k)

def carrier (paid : (Arithmetic.data c).Exterior) : PassiveAllocation.Carrier K k where
  plain := S.plainCarrier paid
  slots := S.slotCarrier paid

end SmoothSideSupport

namespace OrdinaryData

variable {p : SourceParameters c} {packet : RawLeafPacket call p} (O : OrdinaryData packet)

def residualDeletion (_O : OrdinaryData packet) : Finset (Ideal (𝓞 K)) :=
  packet.second.physical.first.fullDeletion.filter
    (fun P => ¬P ∣ packet.second.physical.first.paidSupport.val)

def passiveMask : Ideal (𝓞 K) := ∏ I ∈ O.residualDeletion, I

def residualSlotCount : Bool → ℕ
  | false => (O.leftFrame false).source.allocation.keep.card
  | true => (O.rightFrame false).source.allocation.keep.card

def quotientScale (side rectangle plain : Bool) : ℝ :=
  if side then
    if plain then (O.rightFrame rectangle).source.scale₂ /
      idealNorm K ((O.rightFrame rectangle).source.allocation.plainDivisor (Fin.succ 0))
    else (O.rightFrame rectangle).source.scale₁ /
      idealNorm K ((O.rightFrame rectangle).source.allocation.plainDivisor 0)
  else
    if plain then (O.leftFrame rectangle).source.scale₂ /
      idealNorm K ((O.leftFrame rectangle).source.allocation.plainDivisor (Fin.succ 0))
    else (O.leftFrame rectangle).source.scale₁ /
      idealNorm K ((O.leftFrame rectangle).source.allocation.plainDivisor 0)

def residualLength : (side : Bool) → Fin (O.residualSlotCount side) → ℝ
  | false => (O.leftFrame false).source.childLength
  | true => (O.rightFrame false).source.childLength

/-- The carrier's numerical scales and surviving occurrence lengths
are those of the original second allocation, before passive expansion.
The coefficient task supplies the corresponding global profile and
paid-mask identities, rather than only an energy domination. -/
structure PassiveSupport (input : ProfileInput call) where
  side : ∀ s, SmoothSideSupport input (O.residualSlotCount s)
  scale_eq : ∀ s r a, (side s).plainScale r a = O.quotientScale s r a
  length_eq : ∀ s i, (side s).length i = O.residualLength s i

namespace PassiveSupport

variable {O} {input : ProfileInput call} (support : O.PassiveSupport input)

def carrier (side : Bool) :=
  (support.side side).carrier packet.second.physical.first.paidSupport

def labels (side : Bool) := PassiveAllocation.labels (support.carrier side) O.passiveMask

abbrev Label := support.labels false × support.labels true × (Bool × Bool)

def outer (b : support.Label) : ℝ :=
  packet.leaf.weight * ‖PassiveAllocation.sign b.1.val‖ *
    ‖PassiveAllocation.sign b.2.1.val‖

theorem outer_nonneg (b : support.Label) : 0 ≤ support.outer b :=
  mul_nonneg (mul_nonneg packet.leaf.weight_nonneg (norm_nonneg _)) (norm_nonneg _)

end PassiveSupport
end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
