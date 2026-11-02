import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRawAtomFormula
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bAtomComparison
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bWholeBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalLabel

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Full-row exceptional frames from the original raw atoms

The shared single-column formulas from N1 apply before any row predicate
is imposed.  Here they construct fresh frames on the full original row
set.  The same stored allocation and original comparison are retained;
no ordinary certificate or restricted-row factor is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments WholeAllocation

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem t3b_allocated_mem_cartesian {k : ℕ} (D : Ideal (𝓞 K))
    (v : HeckePort.IdealMobiusDivisorSum.primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (i : AllocationColumn K k)
    (hi : i ∈ pairedAllocatedColumns D v S₁ S₂ S id id HeightOneSpectrum.asIdeal) :
    i ∈ childCartesianColumns S₁ S₂ S := by
  rw [paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

private theorem t3b_whole_of_terms {k : ℕ} (d : OrdinaryAtomTable (K := K) k)
    (i : AllocationColumn K k) {a b z : ℂ}
    (h₀ : d.term false i = a) (h₁ : d.term true i = b) (hz : z = a - b) :
    d.whole i = z := by
  change d.term false i - d.term true i = z
  exact (congrArg₂ (fun x y : ℂ => x - y) h₀ h₁).trans hz.symm

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)
variable (hpacket : packet.Realizes) (phases : OriginalPhaseData packet)

def t3bLeftFactors :=
  (packet.beforeAtomTable hpacket phases false).factors packet.R .left
    packet.allocation.2.1
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.leftReindex_plain₁_ne_zero packet.leftReindex_plain₂_ne_zero
    packet.leftIdeal packet.leftReindex.ideal_product packet.firstSign false

def t3bRightFactors :=
  (packet.beforeAtomTable hpacket phases true).factors packet.R .right
    packet.allocation.2.1
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.rightReindex_plain₁_ne_zero packet.rightReindex_plain₂_ne_zero
    packet.rightIdeal packet.rightReindex.ideal_product (-packet.firstSign) false

/-- The main left rectangle, with all original rows and the actual
independent inner divisor allocation. -/
def t3bLeftFrame :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c) packet.R
      PUnit.{1} .left packet.leaf.leftSlots :=
  (packet.t3bLeftFactors hpacket phases).frame (Arithmetic.context c)
    packet.allocation.1.val packet.allocation.2.2.1.val
    (Finset.mem_filter.mp packet.ordinaryAllocation.property).2.2.1

def t3bRightFrame :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c) packet.R
      PUnit.{1} .right packet.leaf.rightSlots :=
  (packet.t3bRightFactors hpacket phases).frame (Arithmetic.context c)
    packet.allocation.1.val packet.allocation.2.2.2.val
    (Finset.mem_filter.mp packet.ordinaryAllocation.property).2.2.2

def t3bLeftComparison :
    SecondCoefficientComparison (packet.t3bLeftFrame hpacket phases).dictionary :=
  (packet.beforeAtomTable hpacket phases false).t3bComparison
    (SecondColumnSide.left.phase PUnit.{1} packet.allocation.2.1)
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots

def t3bRightComparison :
    SecondCoefficientComparison (packet.t3bRightFrame hpacket phases).dictionary :=
  (packet.beforeAtomTable hpacket phases true).t3bComparison
    (SecondColumnSide.right.phase PUnit.{1} packet.allocation.2.1)
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots

@[simp] theorem t3bLeftFrame_columns :
    (packet.t3bLeftFrame hpacket phases).allocation.columns = packet.leaf.left := rfl

@[simp] theorem t3bRightFrame_columns :
    (packet.t3bRightFrame hpacket phases).allocation.columns = packet.leaf.right := rfl

theorem t3b_left_cartesian (i : AllocationColumn K packet.leaf.leftSlots)
    (hi : i ∈ packet.leaf.left) : i ∈ packet.leftReindex.cartesian := by
  exact t3b_allocated_mem_cartesian packet.allocation.1.val packet.allocation.2.2.1.val
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots i hi

theorem t3b_right_cartesian (i : AllocationColumn K packet.leaf.rightSlots)
    (hi : i ∈ packet.leaf.right) : i ∈ packet.rightReindex.cartesian := by
  exact t3b_allocated_mem_cartesian packet.allocation.1.val packet.allocation.2.2.2.val
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots i hi

theorem t3b_left_whole (i : AllocationColumn K packet.leaf.leftSlots)
    (hi : i ∈ packet.leftReindex.cartesian) :
    (packet.beforeAtomTable hpacket phases false).whole i = packet.leftWhole i := by
  exact t3b_whole_of_terms (packet.beforeAtomTable hpacket phases false) i
    (packet.beforeAtomTable_left hpacket phases false i hi)
    (packet.beforeAtomTable_left hpacket phases true i hi)
    (packet.leftWhole_eq_rectangle_sub hpacket i
      (packet.realizes_coefficient hpacket _))

theorem t3b_right_whole (i : AllocationColumn K packet.leaf.rightSlots)
    (hi : i ∈ packet.rightReindex.cartesian) :
    (packet.beforeAtomTable hpacket phases true).whole i = packet.rightWhole i := by
  exact t3b_whole_of_terms (packet.beforeAtomTable hpacket phases true) i
    (packet.beforeAtomTable_right hpacket phases false i hi)
    (packet.beforeAtomTable_right hpacket phases true i hi)
    (packet.rightWhole_eq_rectangle_sub hpacket i
      (packet.realizes_coefficient hpacket _))

/-- The complete left subtraction, followed by its original residual
character, is the stored leaf coefficient on every row. -/
theorem t3b_left_coefficient (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.leftSlots) (hi : i ∈ packet.leaf.left) :
    packet.leaf.leftCoefficient h i =
      (packet.t3bLeftFrame hpacket phases).centeredCoefficient
        (packet.t3bLeftComparison hpacket phases) h i := by
  let d := packet.beforeAtomTable hpacket phases false
  change packet.leaf.leftCoefficient h i =
    (d.t3bComparison (SecondColumnSide.left.phase PUnit.{1} packet.allocation.2.1)
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots).centeredCoefficient
        (Real.sqrt d.gauss₁ : ℂ)⁻¹
        (Real.sqrt d.gauss₂ : ℂ)⁻¹ (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i *
      (fixedLeftPhase PUnit.{1} packet.allocation.2.1 PUnit.unit : ℂ) *
      Arithmetic.embedding c ((Arithmetic.data c).sexticResidue
        (packet.leftIdeal i) (packet.R.frequency h))
  rw [d.t3bComparison_centeredCoefficient,
    packet.t3b_left_whole hpacket phases i (packet.t3b_left_cartesian i hi)]
  rfl

/-- The right side has the original star exactly once, after the full
subtraction and its actual negative residual frequency. -/
theorem t3b_right_coefficient (h : Arithmetic.Orbit c)
    (i : AllocationColumn K packet.leaf.rightSlots) (hi : i ∈ packet.leaf.right) :
    star (packet.leaf.rightCoefficient h i) =
      (packet.t3bRightFrame hpacket phases).centeredCoefficient
        (packet.t3bRightComparison hpacket phases) h i := by
  let d := packet.beforeAtomTable hpacket phases true
  change star (packet.leaf.rightCoefficient h i) = star (
    (d.t3bComparison (SecondColumnSide.right.phase PUnit.{1} packet.allocation.2.1)
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots).centeredCoefficient
        (Real.sqrt d.gauss₁ : ℂ)⁻¹
        (Real.sqrt d.gauss₂ : ℂ)⁻¹ (fun j => (Real.sqrt (d.gaussSlot j) : ℂ)⁻¹) i *
      (fixedRightPhase PUnit.{1} packet.allocation.2.1 PUnit.unit : ℂ) *
      Arithmetic.embedding c ((Arithmetic.data c).sexticResidue
        (packet.rightIdeal i) (-packet.R.frequency h)))
  rw [d.t3bComparison_centeredCoefficient,
    packet.t3b_right_whole hpacket phases i (packet.t3b_right_cartesian i hi)]
  rfl

theorem t3b_exceptional_integrand
    {theta : Finset (HeckeCharacter K)}
    (Q : PairedFiniteCharacters theta (Arithmetic.Orbit c))
    (hpredicate : packet.leaf.exceptional = Q.exceptional) (z : ℝ × ℝ) :
    packet.leaf.exceptionalIntegrand z =
      (packet.t3bLeftFrame hpacket phases).exceptionalMagnitude
        (packet.t3bRightFrame hpacket phases)
        (packet.t3bLeftComparison hpacket phases)
        (packet.t3bRightComparison hpacket phases) Q (WithLp.toLp 2 z) := by
  apply packet.leaf.t3b_exceptionalIntegrand_eq_centered_frames
    (Arithmetic.context c)
    (packet.t3bLeftFrame hpacket phases) (packet.t3bRightFrame hpacket phases)
    (packet.t3bLeftComparison hpacket phases) (packet.t3bRightComparison hpacket phases)
    Q rfl rfl rfl hpredicate
  · intro h _
    rfl
  · intro h _ i hi
    exact packet.t3b_left_coefficient hpacket phases h i hi
  · intro h _ i hi
    exact packet.t3b_right_coefficient hpacket phases h i hi
  · intro h _
    refine ⟨packet.leftRowTranslation h, ?_⟩
    intro i hi
    exact packet.ordinaryLeftPoint_eq_translation hpacket h i
      (packet.t3b_left_cartesian i hi)
  · intro h _
    refine ⟨packet.rightRowTranslation h, ?_⟩
    intro i hi
    exact packet.ordinaryRightPoint_eq_translation hpacket h i
      (packet.t3b_right_cartesian i hi)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_left_coefficient
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_right_coefficient
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_integrand
