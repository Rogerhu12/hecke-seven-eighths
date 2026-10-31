import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# Reindexing a proved finite engine conclusion

The actual source construction naturally has a dependent finite carrier:
common ideals, pool labels, occurrence allocations and rectangle choices.
This final reindexing uses that entire carrier, including the empty case,
and transports its already proved numerical integrals and mass to Fin n.
It is a packaging lemma, not a replacement for the source-producing
engine theorem or for any of its terminal and mass estimates.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- No finite label is lost, and no measurability of the child-data type
is requested. All numerical hypotheses here are discharged by the
actual source/child construction before this reindexing is used. -/
def PairedEngineConclusion.ofFintype
    (leftData rightData : I → Ω → MomentData K ω ψ)
    (leftParameters rightParameters : I → RealParameters)
    (leftTwist rightTwist : I → Ω → ℝ) (kernel : I → Measure Ω)
    (finite_kernel : ∀ b, IsFiniteMeasure (kernel b))
    (left_width : ∀ b, (leftParameters b).m + (leftParameters b).q ≤ a.m + a.q - σ / 2)
    (right_width : ∀ b, (rightParameters b).m + (rightParameters b).q ≤ a.m + a.q - σ / 2)
    (left_width_nonneg : ∀ b, 0 ≤ (leftParameters b).m + (leftParameters b).q)
    (right_width_nonneg : ∀ b, 0 ≤ (rightParameters b).m + (rightParameters b).q)
    (left_plain_left_nonneg : ∀ b, 0 ≤ (leftParameters b).n₁)
    (left_plain_right_nonneg : ∀ b, 0 ≤ (leftParameters b).n₂)
    (right_plain_left_nonneg : ∀ b, 0 ≤ (rightParameters b).n₁)
    (right_plain_right_nonneg : ∀ b, 0 ≤ (rightParameters b).n₂)
    (left_length : ∀ b ξ, (leftParameters b).z = (leftData b ξ).geometry.totalLength)
    (right_length : ∀ b ξ, (rightParameters b).z = (rightData b ξ).geometry.totalLength)
    (left_kappa : ∀ b, (leftParameters b).κ = a.κ)
    (right_kappa : ∀ b, (rightParameters b).κ = a.κ)
    (left_slots : ∀ b ξ, (leftData b ξ).geometry.slotCount ≤ d.geometry.slotCount)
    (right_slots : ∀ b ξ, (rightData b ξ).geometry.slotCount ≤ d.geometry.slotCount)
    (left_theta : ∀ b ξ, (leftData b ξ).theta = d.theta)
    (right_theta : ∀ b ξ, (rightData b ξ).theta = d.theta)
    (left_slot_characters : ∀ b ξ i, (leftData b ξ).slotCoefficient i ∈ d.theta)
    (right_slot_characters : ∀ b ξ i, (rightData b ξ).slotCoefficient i ∈ d.theta)
    (left_admissible : ∀ b ξ, admissible (leftData b ξ) (leftParameters b))
    (right_admissible : ∀ b ξ, admissible (rightData b ξ) (rightParameters b))
    (left_capacity : ∀ b, (leftParameters b).z = 0 ∨
      (leftParameters b).n₁ + (leftParameters b).n₂ +
        6 * (leftParameters b).κ * (leftParameters b).z ≤
          (leftParameters b).m + (leftParameters b).q)
    (right_capacity : ∀ b, (rightParameters b).z = 0 ∨
      (rightParameters b).n₁ + (rightParameters b).n₂ +
        6 * (rightParameters b).κ * (rightParameters b).z ≤
          (rightParameters b).m + (rightParameters b).q)
    (firstZero secondZero exceptional tail : ℝ)
    (firstZero_nonneg : 0 ≤ firstZero) (secondZero_nonneg : 0 ≤ secondZero)
    (exceptional_nonneg : 0 ≤ exceptional) (tail_nonneg : 0 ≤ tail)
    (terminals : firstZero + secondZero + exceptional + tail ≤
      C * control * Z ^ terminalExponent)
    (left_integrable : ∀ b, Integrable (fun ξ =>
      normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) (kernel b))
    (right_integrable : ∀ b, Integrable (fun ξ =>
      normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ)) (kernel b))
    (cauchy_integrable : ∀ b, Integrable (fun ξ =>
      Real.sqrt (normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) *
        Real.sqrt (normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ)))
          (kernel b))
    (parent : pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      firstZero + secondZero + exceptional + tail +
        ∑ b : I, ∫ ξ,
          Real.sqrt (normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) *
            Real.sqrt (normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ))
              ∂kernel b)
    (mass : (∑ b : I, (kernel b).real Set.univ) ≤ C * control * Z ^ ε) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hs (f : I → ℝ) : (∑ b : Fin (Fintype.card I), f (e b)) = ∑ i : I, f i :=
    Fintype.sum_equiv e (fun b => f (e b)) f (fun b => rfl)
  refine {
    branches := Fintype.card I
    leftData := fun b => leftData (e b)
    rightData := fun b => rightData (e b)
    leftParameters := fun b => leftParameters (e b)
    rightParameters := fun b => rightParameters (e b)
    leftTwist := fun b => leftTwist (e b)
    rightTwist := fun b => rightTwist (e b)
    kernel := fun b => kernel (e b)
    finite_kernel := fun b => finite_kernel (e b)
    left_width := fun b => left_width (e b)
    right_width := fun b => right_width (e b)
    left_width_nonneg := fun b => left_width_nonneg (e b)
    right_width_nonneg := fun b => right_width_nonneg (e b)
    left_plain_left_nonneg := fun b => left_plain_left_nonneg (e b)
    left_plain_right_nonneg := fun b => left_plain_right_nonneg (e b)
    right_plain_left_nonneg := fun b => right_plain_left_nonneg (e b)
    right_plain_right_nonneg := fun b => right_plain_right_nonneg (e b)
    left_length := fun b => left_length (e b)
    right_length := fun b => right_length (e b)
    left_kappa := fun b => left_kappa (e b)
    right_kappa := fun b => right_kappa (e b)
    left_slots := fun b => left_slots (e b)
    right_slots := fun b => right_slots (e b)
    left_theta := fun b => left_theta (e b)
    right_theta := fun b => right_theta (e b)
    left_slot_characters := fun b => left_slot_characters (e b)
    right_slot_characters := fun b => right_slot_characters (e b)
    left_admissible := fun b => left_admissible (e b)
    right_admissible := fun b => right_admissible (e b)
    left_capacity := fun b => left_capacity (e b)
    right_capacity := fun b => right_capacity (e b)
    firstZero := firstZero
    secondZero := secondZero
    exceptional := exceptional
    tail := tail
    firstZero_nonneg := firstZero_nonneg
    secondZero_nonneg := secondZero_nonneg
    exceptional_nonneg := exceptional_nonneg
    tail_nonneg := tail_nonneg
    terminals := terminals
    left_integrable := fun b => left_integrable (e b)
    right_integrable := fun b => right_integrable (e b)
    cauchy_integrable := fun b => cauchy_integrable (e b)
    parent := ?_
    mass := ?_ }
  · exact parent.trans_eq (congrArg (fun x => firstZero + secondZero + exceptional + tail + x)
      (hs (fun i => ∫ ξ,
        Real.sqrt (normalizedPairedEnergy (leftData i ξ) (leftParameters i) Z (leftTwist i ξ)) *
          Real.sqrt (normalizedPairedEnergy (rightData i ξ) (rightParameters i) Z (rightTwist i ξ))
            ∂kernel i)).symm)
  · exact (hs (fun i => (kernel i).real Set.univ)).trans_le mass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofFintype
