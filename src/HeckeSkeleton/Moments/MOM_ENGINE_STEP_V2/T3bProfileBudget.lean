module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPointwise

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed original-profile orders for the exceptional estimate

The finite orders and their numerical coefficient are selected before
any moving call.  They control the original two plain representatives
and every original prime representative on the fixed parent annulus.
Their common amplitude gives an explicit fixed-degree polynomial.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

open EngineStep EngineInduction
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {p : SourceParameters c} {frame : SourceFrame}

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

def profileOrders (bounds : SourceBounds c p frame) : Finset (ℕ × ℕ) :=
  CanonicalLogProfiles.sourceOrders bounds.orders ∪ primeOrders ∪ {(0, 0)}

theorem zero_mem_profileOrders (bounds : SourceBounds c p frame) :
    (0, 0) ∈ profileOrders bounds :=
  Finset.mem_union_right _ (Finset.mem_singleton_self _)

structure ProfileBudget (bounds : SourceBounds c p frame) where
  coefficient : ℝ
  coefficient_one_le : 1 ≤ coefficient
  plain : ∀ (call : Call c) (input : ProfileInput call),
    call.frame = frame → profileOrders bounds ⊆ input.orders →
    ∀ (packet : RawLeafPacket call p) (hpacket : packet.Realizes) (plain : Bool),
      bounds.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (packet.t3bNormProfile hpacket input plain) ≤ coefficient * input.amplitude
  prime : ∀ (call : Call c) (input : ProfileInput call),
    call.frame = frame → profileOrders bounds ⊆ input.orders →
    ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
      ‖call.t3bPrimeNormProfile p input i x‖ ≤ coefficient * input.amplitude

theorem profileBudget_nonempty (bounds : SourceBounds c p frame) :
    Nonempty (ProfileBudget bounds) := by
  obtain ⟨Cplain, hCplain, hplain⟩ := exists_normProfile_bound c p frame bounds.orders
  obtain ⟨Cprime, hCprime, hprime⟩ := exists_primeProfile_bound c p frame
  refine ⟨⟨1 + Cplain + Cprime, by linarith, ?_, ?_⟩⟩
  · intro call input hframe horders packet hpacket plain
    have hord : CanonicalLogProfiles.sourceOrders bounds.orders ⊆ input.orders :=
      fun q hq => horders (Finset.mem_union_left _ (Finset.mem_union_left _ hq))
    exact (hplain call input hframe hord packet hpacket plain).trans
      (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans input.amplitude_one_le))
  · intro call input hframe horders i x
    have hord : primeOrders ⊆ input.orders :=
      fun q hq => horders (Finset.mem_union_left _ (Finset.mem_union_right _ hq))
    exact (hprime call input hframe hord i x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans input.amplitude_one_le))

theorem profile_amplitude_one (bounds : SourceBounds c p frame) (budget : ProfileBudget bounds)
    {call : Call c} (input : ProfileInput call) :
    1 ≤ budget.coefficient * input.amplitude :=
  one_le_mul_of_one_le_of_one_le budget.coefficient_one_le input.amplitude_one_le

/-- Every occurrence of the original representative contributes its
explicit fixed power, independent of the moving source indices. -/
theorem pointCoefficient_mul (bounds : SourceBounds c p frame) (P amplitude : ℝ) :
    pointCoefficient bounds (P * amplitude) =
      pointCoefficient bounds P * amplitude ^ (4 + 12 * c.geometry.slots) := by
  simp only [pointCoefficient, pairCoefficient, atomRadius, mul_pow, ← pow_mul,
    show 2 * (6 * c.geometry.slots) = 12 * c.geometry.slots by omega, pow_add]
  ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.profileBudget_nonempty
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.pointCoefficient_mul
