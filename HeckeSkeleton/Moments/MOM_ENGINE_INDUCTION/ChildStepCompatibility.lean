import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import HeckeGeneral.Analysis.SelectedMomentSlots

/-!
# Consuming the authoritative paired child step

The authoritative producer is
`HeckeSkeleton.Moments.EngineStep.paired_child_step`, published on
`cloud/mom-engine-step` at commit
`3820604a66b6c3a41d93dec1bf6156a69029be74`.

`ChildStepConclusion` below is its exact conclusion after abbreviating
`parentWidth = m + q` and `allowance = b₂ - p₂ + w + B + ell`.
`remainingParameters` is the identical record update from the producer's
`MomentDataAdapter.lean`.  Thus, after both branches are merged, `change`
converts the producer's conclusion to this interface by definitional equality.
Only the baseline `SelectedMomentSlots` operation is imported here.
At this pin the producer explicitly assumes nonnegative total removal
charge and allows an already zero-slot child in its defect premise.
These changes concern the producer's hypotheses; its conclusion, and
therefore `ChildStepConclusion`, are unchanged.

This file places that actual restricted-slot successor earlier in the
induction order and converts the actual energy inequality into the normalized
inequality used by either form of `Reduction`.  The unrepaired child remains
the left side of this inequality.  Constructing the parent's complete positive reduction,
its exceptional terminal components, and the uniform mass budget for its
proved common-kernel tails remains an analytic assembly obligation, recorded
by `RawParentReduction`. The newer parent and dictionary modules provide
intermediate actual identities and estimates; their calibrated inputs and
uniform recursive combination are not supplied by this child conclusion.

The proof stage is supplied independently by `PolynomialSystem.proofStage`;
`Node.centered` controls only the actual coefficient.  The strict-width
bridge below therefore accepts either child proof stage.  An ordinary root
in the centered range can occupy the later proof stage.  Identifying a
reflected comparison with an admissible shorter ordinary model, and placing
that model in the earlier stage, remain analytic producer obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

universe u

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- The exact successor-parameter operation of the published step. -/
def remainingParameters (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) : RealParameters :=
  { a with z := (d.geometry.restrictSlots keep).totalLength }

@[simp] theorem remainingParameters_width
    (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) :
    (remainingParameters d a keep).m + (remainingParameters d a keep).q = a.m + a.q := rfl

theorem remainingParameters_z_nonneg (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) :
    0 ≤ (remainingParameters d a keep).z := by
  change 0 ≤ (d.geometry.restrictSlots keep).totalLength
  rw [SlotGeometry.totalLength_restrictSlots]
  exact Finset.sum_nonneg fun i _ => (d.geometry.slots i).length_pos.le

theorem remainingParameters_z_le (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) (hz : a.z = d.geometry.totalLength) :
    (remainingParameters d a keep).z ≤ a.z := by
  change (d.geometry.restrictSlots keep).totalLength ≤ a.z
  rw [SlotGeometry.totalLength_restrictSlots, hz]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keep)
    (fun i _ _ => (d.geometry.slots i).length_pos.le)

theorem remainingParameters_z_eq_zero (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) (hz : a.z = d.geometry.totalLength)
    (hzero : a.z = 0) : (remainingParameters d a keep).z = 0 := by
  exact le_antisymm (by simpa only [hzero] using remainingParameters_z_le d a keep hz)
    (remainingParameters_z_nonneg d a keep)

/-- The conclusion of the published `paired_child_step`, retaining the
choice of successor before the scale, rowwise factors, and height. -/
def ChildStepConclusion (d : MomentData K ω ψ) (a : RealParameters)
    (parentWidth σ allowance mesh err : ℝ) : Prop :=
  a.m + a.q ≤ parentWidth - σ / 2 ∧ a.m + a.q < parentWidth ∧
    ∃ removed : Finset (Fin d.geometry.slotCount),
      let keep := Finset.univ \ removed
      let a' := remainingParameters d a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin d.geometry.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows d a Z, ∀ i,
          ‖primePolynomial d i u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * (d.geometry.slots i).length)) →
        pairedEnergy d a Z t ≤
          (∏ i ∈ removed, C i) * Z ^ (allowance + err / 6 + a.κ * mesh) *
            pairedEnergy (d.restrictSlots keep) a' Z t

/-- Slot removal changes neither part of the effective row width. -/
@[simp] theorem restricted_child_width (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) :
    (Node.ordinary (d.restrictSlots keep) (remainingParameters d a keep)).width = a.m + a.q := rfl

/-- The explicit nonnegative weight available to the parent reduction
once the pointwise prime bounds have been supplied. -/
theorem child_repair_weight_nonneg
    (d : MomentData K ω ψ) (a : RealParameters)
    (removed : Finset (Fin d.geometry.slotCount))
    (C : Fin d.geometry.slotCount → ℝ) {Z : ℝ} (hZ : 0 ≤ Z)
    (hC : ∀ i, 0 ≤ C i) (allowance mesh err : ℝ) :
    0 ≤ (∏ i ∈ removed, C i) * Z ^ (allowance + err / 6 + a.κ * mesh) :=
  mul_nonneg (Finset.prod_nonneg fun i _ => hC i) (Real.rpow_nonneg hZ _)

/-- The published inequality is for the actual child energy.  Dividing by
its unchanged width power gives the transfer for either parent reduction. -/
theorem normalized_child_transfer
    (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) (U t factor : ℝ) (hU : 0 ≤ U)
    (henergy : pairedEnergy d a U t ≤
      factor * pairedEnergy (d.restrictSlots keep) (remainingParameters d a keep) U t) :
    (Node.ordinary d a).normalizedEnergy U t ≤
      factor * (Node.ordinary (d.restrictSlots keep)
        (remainingParameters d a keep)).normalizedEnergy U t := by
  unfold Node.normalizedEnergy
  rw [Node.ordinary_energy, Node.ordinary_energy]
  change pairedEnergy d a U t / U ^ (a.m + a.q) ≤
    factor * (pairedEnergy (d.restrictSlots keep) (remainingParameters d a keep) U t /
      U ^ (a.m + a.q))
  calc
    _ ≤ (factor * pairedEnergy (d.restrictSlots keep) (remainingParameters d a keep) U t) /
        U ^ (a.m + a.q) :=
      div_le_div_of_nonneg_right henergy (Real.rpow_nonneg hU _)
    _ = _ := by ring

/-- A strict child may change from positive to zero slots.  A zero-slot
parent must remain zero-slot; that invariant is supplied by the decomposition. -/
theorem PolynomialSystem.earlier_of_width_drop
    {σ W : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W) (child parent : S.Label)
    (hdrop : (S.node child).width + σ / 2 ≤ (S.node parent).width)
    (hzero : (S.node parent).parameters.z = 0 → (S.node child).parameters.z = 0) :
    (S.schedule child).Earlier (S.schedule parent) := by
  by_cases hp : (S.node parent).parameters.z = 0
  · apply S.strict_child_earlier child parent ?_ hdrop
    change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
      (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1)
    simp only [hp, hzero hp, ite_true]
  · by_cases hc : (S.node child).parameters.z = 0
    · apply State.zero_before_positive
      · change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1).val = 0
        simp only [hc, ite_true, Fin.val_zero]
      · change (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1).val = 1
        simp only [hp, ite_false, Fin.val_one]
    · apply S.strict_child_earlier child parent ?_ hdrop
      change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
        (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1)
      simp only [hc, hp, ite_false]

/-- Consume the authoritative child conclusion inside an actual polynomial
system.  The system's successor labels are calibrated to the exact restricted
models.  The result gives an earlier successor and its normalized transfer;
the estimate for the parent still comes from the separate parent assembly. -/
theorem repaired_child_for_recursion
    {σ W : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W) (parent : S.Label)
    (d : MomentData K ω ψ) (a : RealParameters) (parentWidth allowance mesh err : ℝ)
    (hz : a.z = d.geometry.totalLength)
    (hparent : (S.node parent).width = parentWidth)
    (hzero : (S.node parent).parameters.z = 0 → a.z = 0)
    (successor : (keep : Finset (Fin d.geometry.slotCount)) → S.Label)
    (hsuccessor : ∀ keep, S.node (successor keep) =
      Node.ordinary (d.restrictSlots keep) (remainingParameters d a keep))
    (hstep : ChildStepConclusion d a parentWidth σ allowance mesh err) :
    ∃ removed : Finset (Fin d.geometry.slotCount),
      let keep := Finset.univ \ removed
      let a' := remainingParameters d a keep
      (S.schedule (successor keep)).Earlier (S.schedule parent) ∧
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin d.geometry.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows d a Z, ∀ i,
          ‖primePolynomial d i u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * (d.geometry.slots i).length)) →
        (Node.ordinary d a).normalizedEnergy Z t ≤
          (∏ i ∈ removed, C i) * Z ^ (allowance + err / 6 + a.κ * mesh) *
            (S.node (successor keep)).normalizedEnergy Z t := by
  rcases hstep with ⟨hdrop, _, removed, hcapacity, henergy⟩
  let keep := Finset.univ \ removed
  have hwidth : (S.node (successor keep)).width = a.m + a.q := by
    simpa only [hsuccessor keep] using restricted_child_width d a keep
  refine ⟨removed, ?_, hcapacity, ?_⟩
  · apply S.earlier_of_width_drop (successor keep) parent
    · rw [hwidth, hparent]
      linarith
    · intro hp
      rw [hsuccessor keep]
      change (remainingParameters d a keep).z = 0
      exact remainingParameters_z_eq_zero d a keep hz (hzero hp)
  · intro Z hZ C hC t hprime
    rw [hsuccessor keep]
    exact normalized_child_transfer d a keep Z t
      ((∏ i ∈ removed, C i) * Z ^ (allowance + err / 6 + a.κ * mesh))
      (zero_le_one.trans hZ) (henergy Z hZ C hC t hprime)

end HeckeSkeleton.Moments.EngineInduction
