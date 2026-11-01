import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput

/-!
# Freezing the actual canonical children at their evaluation time

The canonical output evaluates every child at time zero. This alone
does not assert that a child's test functions are time independent.
Freezing those actual functions at zero proves that property while
preserving the complete evaluated polynomial, all integrals, and the
same positive Fourier kernels.

The complete moving recipe is transported literally to these frozen
children. Its displayed support and joint mask budgets remain those of
the original chosen child; there is no new child selection or arithmetic
admissibility assumption.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

@[simp] theorem normalizedPairedEnergy_freezeMomentTime
    (d : MomentData K ω ψ) (a : RealParameters) (U t : ℝ) :
    EngineStep.normalizedPairedEnergy (freezeMomentTime d t) a U 0 =
      EngineStep.normalizedPairedEnergy d a U t := by
  unfold EngineStep.normalizedPairedEnergy
  rw [freezeMomentTime_pairedEnergy]

/-- Replace each actual child by its time-zero frozen profiles, retaining
its slot dictionary, parameters, terminal pieces and exact kernel.
The admissibility callback concerns these literal child data only. -/
def freezeEngineOutput {Ω : Type*} [MeasurableSpace Ω]
    {d : MomentData K ω ψ} {a : RealParameters} {centered : Bool}
    {U t Y₁ Y₂ sigma delta beta C control : ℝ}
    {oldAdmissible newAdmissible : MomentData K ω ψ → RealParameters → Prop}
    (out : EngineStep.PairedEngineConclusion (Ω := Ω) centered
      d a U t Y₁ Y₂ sigma delta beta C control oldAdmissible)
    (hleft : ∀ b ξ,
      newAdmissible (freezeMomentTime (out.leftData b ξ) 0) (out.leftParameters b))
    (hright : ∀ b ξ,
      newAdmissible (freezeMomentTime (out.rightData b ξ) 0) (out.rightParameters b)) :
    EngineStep.PairedEngineConclusion (Ω := Ω) centered
      d a U t Y₁ Y₂ sigma delta beta C control newAdmissible where
  branches := out.branches
  leftData b ξ := freezeMomentTime (out.leftData b ξ) 0
  rightData b ξ := freezeMomentTime (out.rightData b ξ) 0
  leftParameters := out.leftParameters
  rightParameters := out.rightParameters
  leftTwist _ _ := 0
  rightTwist _ _ := 0
  leftTwist_zero _ _ := rfl
  rightTwist_zero _ _ := rfl
  kernel := out.kernel
  finite_kernel := out.finite_kernel
  left_width := out.left_width
  right_width := out.right_width
  left_width_nonneg := out.left_width_nonneg
  right_width_nonneg := out.right_width_nonneg
  left_plain_left_nonneg := out.left_plain_left_nonneg
  left_plain_right_nonneg := out.left_plain_right_nonneg
  right_plain_left_nonneg := out.right_plain_left_nonneg
  right_plain_right_nonneg := out.right_plain_right_nonneg
  left_length := out.left_length
  right_length := out.right_length
  left_kappa := out.left_kappa
  right_kappa := out.right_kappa
  left_slots := out.left_slots
  right_slots := out.right_slots
  left_theta := out.left_theta
  right_theta := out.right_theta
  left_slot_characters := out.left_slot_characters
  right_slot_characters := out.right_slot_characters
  left_admissible := hleft
  right_admissible := hright
  left_capacity := out.left_capacity
  right_capacity := out.right_capacity
  firstZero := out.firstZero
  secondZero := out.secondZero
  exceptional := out.exceptional
  tail := out.tail
  firstZero_nonneg := out.firstZero_nonneg
  secondZero_nonneg := out.secondZero_nonneg
  exceptional_nonneg := out.exceptional_nonneg
  tail_nonneg := out.tail_nonneg
  terminals := out.terminals
  left_integrable b := by
    simpa only [normalizedPairedEnergy_freezeMomentTime, out.leftTwist_zero] using
      out.left_integrable b
  right_integrable b := by
    simpa only [normalizedPairedEnergy_freezeMomentTime, out.rightTwist_zero] using
      out.right_integrable b
  cauchy_integrable b := by
    simpa only [normalizedPairedEnergy_freezeMomentTime,
      out.leftTwist_zero, out.rightTwist_zero] using out.cauchy_integrable b
  parent := by
    simpa only [normalizedPairedEnergy_freezeMomentTime,
      out.leftTwist_zero, out.rightTwist_zero] using out.parent
  mass := out.mass

/-- A raw window quantified over all evaluation times gives a window
for its frozen data using the same original representatives at zero. -/
def freezeRawProfileWindow
    {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {amplitude : ℝ}
    (profiles : EngineStep.RawProfileWindow rowDomain Set.univ window orders d amplitude) :
    EngineStep.RawProfileWindow rowDomain Set.univ window orders
      (freezeMomentTime d 0) amplitude where
  inverseRep u _ := profiles.inverseRep u 0
  leftRep u _ := profiles.leftRep u 0
  rightRep u _ := profiles.rightRep u 0
  primeRep j _ := profiles.primeRep j 0
  inverse_eq u _ y := by
    change d.inverseTest.profile u 0 y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, profiles.inverse_eq]
  left_eq u _ y := by
    change d.plainTest₁.profile u 0 y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, profiles.left_eq]
  right_eq u _ y := by
    change d.plainTest₂.profile u 0 y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, profiles.right_eq]
  prime_eq j _ y := by
    change (d.geometry.slots j).profile 0 y * profilePower 0 y = _
    rw [profilePower_zero, mul_one, profiles.prime_eq]
  inverse_support u hu _ _ := profiles.inverse_support u hu 0 (Set.mem_univ 0)
  left_support u hu _ _ := profiles.left_support u hu 0 (Set.mem_univ 0)
  right_support u hu _ _ := profiles.right_support u hu 0 (Set.mem_univ 0)
  prime_support j _ _ := profiles.prime_support j 0 (Set.mem_univ 0)
  inverse_bound u hu _ _ := profiles.inverse_bound u hu 0 (Set.mem_univ 0)
  left_bound u hu _ _ := profiles.left_bound u hu 0 (Set.mem_univ 0)
  right_bound u hu _ _ := profiles.right_bound u hu 0 (Set.mem_univ 0)
  prime_bound j _ _ := profiles.prime_bound j 0 (Set.mem_univ 0)

section ActualMovingChild

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)}
variable {Q : Type*} {parent d : MomentData K c.family.omega (targetCharacter K c)}
variable {a : RealParameters} {U : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}
variable (child : EngineStep.MovingEngineChildAdmissible
  (axiomChoice K c).A (probeData K c) (momentRowCharacters K c) Q
  parent rowDomain window orders U d a)

/-- The original moving dictionary itself, together with the proved
time independence of actual frozen tests, supplies the full data-only
primitive required by the next reflection or Mellin construction. -/
def frozenMovingChildCompleteSourceData
    (htheta : d.theta = theta) (hslots : ∀ j, d.slotCoefficient j ∈ theta) :
    CompleteSourceData c theta (freezeMomentTime d 0) where
  recipe := child.rowRecipe.frozen (fun _ => 0)
  theta_eq := htheta
  slot_characters := hslots
  timeIndependent := profileTimeIndependent_freezeMomentTime d 0

theorem frozenMovingChild_supportBudget
    (htheta : d.theta = theta) (hslots : ∀ j, d.slotCoefficient j ∈ theta) :
    (frozenMovingChildCompleteSourceData child htheta hslots).recipe.SupportBudget U a.q :=
  child.supportBudget

theorem frozenMovingChild_fullJointBudget
    (htheta : d.theta = theta) (hslots : ∀ j, d.slotCoefficient j ∈ theta) :
    (frozenMovingChildCompleteSourceData child htheta hslots).recipe.FullJointBudget
      U (a.m + a.q) := child.fullJointBudget

include child in
/-- The retained original slots, rather than total length alone, prove
that the same per-slot source mesh holds after freezing. -/
theorem frozenMovingChild_fitsMesh {mesh : ℝ}
    (hparent : parent.geometry.fitsMesh mesh) :
    (freezeMomentTime d 0).geometry.fitsMesh mesh := child.fitsMesh hparent

include child in
/-- The actual raw analytic unit ball transports without changing its
support window. In particular this theorem does not infer a positive
lower support bound when the canonical window includes zero. -/
theorem frozenMovingChild_profileWindow :
    EngineStep.InFixedProfileWindow rowDomain Set.univ window orders
      (freezeMomentTime d 0) := by
  obtain ⟨profiles⟩ := child.engine.1
  exact ⟨freezeRawProfileWindow profiles⟩

end ActualMovingChild

end HeckeSkeleton.Moments.EngineInduction
