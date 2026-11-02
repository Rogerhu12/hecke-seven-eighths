import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryData

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The fixed finite carrier of residual coprimality expansion

The passive mask is the original complete deletion ideal. Its divisors
and occurrence allocations determine the finite labels and their exact
Möbius signs. There is no freely chosen number of duplicate frames or
additional positive weight. The paid moving support remains a separate
field of the original source coordinates.
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

namespace PassiveAllocation

abbrev Key (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  Σ D : Ideal (𝓞 K), primeSupport D → Finset (Fin (k + 2))

def candidates (mask : Ideal (𝓞 K)) (k : ℕ) : Finset (Key K k) :=
  (idealDivisors mask).sigma (fun D => AllocationMass.idealAllocations D (k + 2))

def sign {k : ℕ} (a : Key K k) : ℂ :=
  (moebius a.1 : ℂ) * AllocationMass.sign (primeSupport a.1) a.2

def idealCarrier (s : Finset (NonzeroIdeal K)) : Finset (Ideal (𝓞 K)) :=
  s.image (fun I => I.val)

variable {k : ℕ} (B : ActualColumnAllocation K k)

def columns (a : Key K B.keep.card) : Finset (AllocationColumn K B.keep.card) :=
  pairedAllocatedColumns a.1 a.2 (idealCarrier B.childPlain₁)
    (idealCarrier B.childPlain₂) B.childSlots id id HeightOneSpectrum.asIdeal

def labels (mask : Ideal (𝓞 K)) : Finset (Key K B.keep.card) :=
  (candidates mask B.keep.card).filter
    (fun a => sign a ≠ 0 ∧ (columns B a).Nonempty)

/-- The witness comes from this exact finite allocated carrier. -/
def allocation (mask : Ideal (𝓞 K)) (a : labels B mask) :
    ActualColumnAllocation K B.keep.card where
  divisor := a.val.1
  selection := a.val.2
  plain₁ := idealCarrier B.childPlain₁
  plain₂ := idealCarrier B.childPlain₂
  slots := B.childSlots
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

namespace OrdinaryData

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

def passiveMask (_O : OrdinaryData packet) : Ideal (𝓞 K) :=
  ∏ I ∈ packet.second.physical.first.fullDeletion, I

abbrev leftOriginalAllocation := (O.leftFrame false).source.allocation
abbrev rightOriginalAllocation := (O.rightFrame false).source.allocation

def leftPassiveLabels := PassiveAllocation.labels O.leftOriginalAllocation O.passiveMask
def rightPassiveLabels := PassiveAllocation.labels O.rightOriginalAllocation O.passiveMask

abbrev PassiveLabel := O.leftPassiveLabels × O.rightPassiveLabels × (Bool × Bool)

def passiveOuter (b : O.PassiveLabel) : ℝ :=
  packet.leaf.weight * ‖PassiveAllocation.sign b.1.val‖ *
    ‖PassiveAllocation.sign b.2.1.val‖

theorem passiveOuter_nonneg (b : O.PassiveLabel) : 0 ≤ O.passiveOuter b :=
  mul_nonneg (mul_nonneg packet.leaf.weight_nonneg (norm_nonneg _)) (norm_nonneg _)

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
