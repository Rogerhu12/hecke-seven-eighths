module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exact raw leaf already supplies its ordinary allocation and binding

The divisor, the finite phase and both occurrence allocations are read
from the stored key. The two coefficient witnesses in `Live` prove that
both allocated Cartesian carriers are nonempty. The nonzero original
weight proves squarefreeness of the same divisor. No new allocation is
chosen and no row or kernel is changed.

The remaining N1 construction is the four individual rectangular
factorizations. Once these are available, their binding to the original
raw leaf is a direct single-atom identity, including the right star and
the negative first Fourier coordinate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open WholeAllocation UniqueFactorizationMonoid

attribute [local instance]
  actualGaussFiniteLeavesCircleCharacterFintype
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- The live allocation is the original independent divisor and the
original two occurrence allocations. -/
def ordinaryAllocation : liveSecondAllocationBranches (Ray := PUnit)
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.rightIdeal := by
  refine ⟨packet.allocation,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩⟩
  · by_contra hn
    apply packet.live.1
    change _ * (‖(moebius packet.allocation.1.val : ℂ)‖ * _) = 0
    simp only [moebius_of_not_squarefree hn, Int.cast_zero, norm_zero,
      zero_mul, mul_zero]
  · obtain ⟨h, hh, i, hi, hc⟩ := packet.live.2.1
    exact ⟨i, hi⟩
  · obtain ⟨h, hh, i, hi, hc⟩ := packet.live.2.2
    exact ⟨i, hi⟩

@[simp] theorem ordinaryAllocation_val :
    packet.ordinaryAllocation.val = packet.allocation := rfl

/-- The original pair of Fourier locations on the left. -/
def ordinaryLeftPoint (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.leftSlots) : EngineParameter :=
  WithLp.toLp 2 (packet.leaf.leftFirst h i, packet.leaf.leftSecond h i)

/-- The original pair on the conjugated right side has exactly one
negative first coordinate. -/
def ordinaryRightPoint (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.rightSlots) : EngineParameter :=
  WithLp.toLp 2 (-packet.leaf.rightFirst h i, packet.leaf.rightSecond h i)

/-- Primitive single-atom dictionary for any factorization of the four
rectangles on the exact original Fourier locations. -/
def ordinaryBinding
    (rectangles : HybridOrdinaryRectangles packet.R PUnit
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.leftIdeal packet.rightIdeal (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      packet.leftWhole packet.rightWhole packet.ordinaryLeftPoint
      packet.ordinaryRightPoint packet.ordinaryAllocation packet.leaf.exceptional) :
    packet.leaf.OrdinaryBinding rectangles where
  rows := Finset.Subset.refl _
  rows_zero _ hh hn := False.elim (hn hh)
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight _ _ := rfl
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient _ _ _ _ := rfl
  leftPoint h _ := ⟨0, fun i _ => (zero_add _).symm⟩
  rightPoint h _ := ⟨0, fun i _ => (zero_add _).symm⟩

/-- Assembly after the two individual rectangle factorizations have
been proved. This only fills the definitional original-source fields. -/
def ordinaryDataOfRectangles
    (rectangles : HybridOrdinaryRectangles packet.R PUnit
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.leftIdeal packet.rightIdeal (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      packet.leftWhole packet.rightWhole packet.ordinaryLeftPoint
      packet.ordinaryRightPoint packet.ordinaryAllocation packet.leaf.exceptional)
    (hleft : ∀ r i, i ∈ childCartesianColumns packet.leftReindex.plain₁
      packet.leftReindex.plain₂ packet.leftReindex.slots →
        rectangles.leftTerms r i = packet.originalLeftRectangle r i)
    (hright : ∀ r i, i ∈ childCartesianColumns packet.rightReindex.plain₁
      packet.rightReindex.plain₂ packet.rightReindex.slots →
        rectangles.rightTerms r i = packet.originalRightRectangle r i) :
    OrdinaryData packet where
  leftPoint := packet.ordinaryLeftPoint
  rightPoint := packet.ordinaryRightPoint
  branch := packet.ordinaryAllocation
  branch_eq := rfl
  rectangles := rectangles
  left_rectangle := hleft
  right_rectangle := hright
  binding := packet.ordinaryBinding rectangles

/-- A row translation is common to every column, so the residual
logarithmic locations give the same original polynomial norm. -/
def ordinaryBindingTranslated
    (x : Arithmetic.Orbit c → AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (y : Arithmetic.Orbit c → AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (rectangles : HybridOrdinaryRectangles packet.R PUnit
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.leftIdeal packet.rightIdeal (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      packet.leftWhole packet.rightWhole x y packet.ordinaryAllocation packet.leaf.exceptional)
    (hx : ∀ h ∈ packet.R.rows, ∃ z, ∀ i ∈ packet.leaf.left,
      packet.ordinaryLeftPoint h i = z + x h i)
    (hy : ∀ h ∈ packet.R.rows, ∃ z, ∀ i ∈ packet.leaf.right,
      packet.ordinaryRightPoint h i = z + y h i) :
    packet.leaf.OrdinaryBinding rectangles where
  rows := fun _ hh => hh
  rows_zero _ hh hn := False.elim (hn hh)
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight _ _ := rfl
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient _ _ _ _ := rfl
  leftPoint := hx
  rightPoint := hy

def ordinaryDataOfTranslatedRectangles
    (x : Arithmetic.Orbit c → AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (y : Arithmetic.Orbit c → AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (rectangles : HybridOrdinaryRectangles packet.R PUnit
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.leftIdeal packet.rightIdeal (fun _ => PUnit.unit) (fun _ => PUnit.unit)
      packet.leftWhole packet.rightWhole x y packet.ordinaryAllocation packet.leaf.exceptional)
    (hleft : ∀ r i, i ∈ childCartesianColumns packet.leftReindex.plain₁
      packet.leftReindex.plain₂ packet.leftReindex.slots →
        rectangles.leftTerms r i = packet.originalLeftRectangle r i)
    (hright : ∀ r i, i ∈ childCartesianColumns packet.rightReindex.plain₁
      packet.rightReindex.plain₂ packet.rightReindex.slots →
        rectangles.rightTerms r i = packet.originalRightRectangle r i)
    (hx : ∀ h ∈ packet.R.rows, ∃ z, ∀ i ∈ packet.leaf.left,
      packet.ordinaryLeftPoint h i = z + x h i)
    (hy : ∀ h ∈ packet.R.rows, ∃ z, ∀ i ∈ packet.leaf.right,
      packet.ordinaryRightPoint h i = z + y h i) :
    OrdinaryData packet where
  leftPoint := x
  rightPoint := y
  branch := packet.ordinaryAllocation
  branch_eq := rfl
  rectangles := rectangles
  left_rectangle := hleft
  right_rectangle := hright
  binding := packet.ordinaryBindingTranslated x y rectangles hx hy

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryAllocation
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBinding
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryDataOfRectangles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryDataOfTranslatedRectangles
