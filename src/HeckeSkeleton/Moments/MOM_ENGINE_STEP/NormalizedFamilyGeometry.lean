import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteNormalizedChildren

/-!
# The original parent geometry of the computed normalized family

The raw side calibrations already carry the actual lengths, characters,
capacity ledger and fixed deletion choice. This module records only
their identities with the original parent. All successor inequalities,
the actual retained total length, and zero-slot inheritance are then
proved for the computed children. None of these child conclusions is
an additional input to the eventual producing theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {Z : ℝ}

namespace ActualNormalizedPairFamily

variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
variable (labels : Finset Λ) (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ)

/-- Identities of the original raw side dictionaries, before choosing
either capacity deletion. The gap bound is the original pool ledger. -/
structure ParentGeometry : Prop where
  left_parent : ∀ b ∈ labels,
    (family.leftCapacity b).geometry.parentWidth = a.m + a.q
  right_parent : ∀ b ∈ labels,
    (family.rightCapacity b).geometry.parentWidth = a.m + a.q
  left_gap : ∀ b ∈ labels, step ≤ (family.leftCapacity b).gap
  right_gap : ∀ b ∈ labels, step ≤ (family.rightCapacity b).gap
  left_kappa : ∀ b ∈ labels, (family.leftCalibration b).parameters.κ = a.κ
  right_kappa : ∀ b ∈ labels, (family.rightCalibration b).parameters.κ = a.κ
  left_slots : ∀ b ∈ labels, family.leftSlots b ≤ d.geometry.slotCount
  right_slots : ∀ b ∈ labels, family.rightSlots b ≤ d.geometry.slotCount
  left_theta : ∀ b ∈ labels, ∀ ξ, ((family.leftCalibration b).data ξ).theta = d.theta
  right_theta : ∀ b ∈ labels, ∀ ξ, ((family.rightCalibration b).data ξ).theta = d.theta

namespace ParentGeometry

variable {family labels d a step}
variable (raw : family.ParentGeometry labels d a step)

include raw

theorem left_width (b : family.active labels) :
    (family.leftParameters labels b).m + (family.leftParameters labels b).q ≤
      a.m + a.q - step / 2 := by
  have hb := (Finset.mem_filter.mp b.property).1
  have h := (family.leftChild labels b).parameters_width_drop
  rw [raw.left_parent b.val hb] at h
  exact h.trans (by linarith [raw.left_gap b.val hb])

theorem right_width (b : family.active labels) :
    (family.rightParameters labels b).m + (family.rightParameters labels b).q ≤
      a.m + a.q - step / 2 := by
  have hb := (Finset.mem_filter.mp b.property).1
  have h := (family.rightChild labels b).parameters_width_drop
  rw [raw.right_parent b.val hb] at h
  exact h.trans (by linarith [raw.right_gap b.val hb])

theorem left_kappa_eq (b : family.active labels) :
    (family.leftParameters labels b).κ = a.κ :=
  (family.leftChild labels b).kappa_eq.trans
    (raw.left_kappa b.val (Finset.mem_filter.mp b.property).1)

theorem right_kappa_eq (b : family.active labels) :
    (family.rightParameters labels b).κ = a.κ :=
  (family.rightChild labels b).kappa_eq.trans
    (raw.right_kappa b.val (Finset.mem_filter.mp b.property).1)

theorem left_slot_count (b : family.active labels) (ξ : V) :
    (family.leftData labels b ξ).geometry.slotCount ≤ d.geometry.slotCount :=
  ((family.leftChild labels b).frozen_slot_count ξ).trans
    (raw.left_slots b.val (Finset.mem_filter.mp b.property).1)

theorem right_slot_count (b : family.active labels) (ξ : V) :
    (family.rightData labels b ξ).geometry.slotCount ≤ d.geometry.slotCount :=
  ((family.rightChild labels b).frozen_slot_count ξ).trans
    (raw.right_slots b.val (Finset.mem_filter.mp b.property).1)

theorem left_theta_eq (b : family.active labels) (ξ : V) :
    (family.leftData labels b ξ).theta = d.theta :=
  ((family.leftChild labels b).frozen_theta_eq ξ).trans
    (raw.left_theta b.val (Finset.mem_filter.mp b.property).1 ξ)

theorem right_theta_eq (b : family.active labels) (ξ : V) :
    (family.rightData labels b ξ).theta = d.theta :=
  ((family.rightChild labels b).frozen_theta_eq ξ).trans
    (raw.right_theta b.val (Finset.mem_filter.mp b.property).1 ξ)

theorem left_character (b : family.active labels) (ξ : V)
    (i : Fin (family.leftData labels b ξ).geometry.slotCount) :
    (family.leftData labels b ξ).slotCoefficient i ∈ d.theta := by
  have h := (family.leftChild labels b).frozen_slot_in_theta ξ i
  rwa [raw.left_theta b.val (Finset.mem_filter.mp b.property).1 ξ] at h

theorem right_character (b : family.active labels) (ξ : V)
    (i : Fin (family.rightData labels b ξ).geometry.slotCount) :
    (family.rightData labels b ξ).slotCoefficient i ∈ d.theta := by
  have h := (family.rightChild labels b).frozen_slot_in_theta ξ i
  rwa [raw.right_theta b.val (Finset.mem_filter.mp b.property).1 ξ] at h

/-- The same proof covers all slots. Empty parent geometry forces each
computed retained subset to be empty, without a separate engine case. -/
theorem zero_slots (hzero : d.geometry.slotCount = 0)
    (b : family.active labels) (ξ : V) :
    (family.leftData labels b ξ).geometry.slotCount = 0 ∧
      (family.rightData labels b ξ).geometry.slotCount = 0 := by
  constructor
  · exact Nat.eq_zero_of_le_zero (hzero ▸ raw.left_slot_count b ξ)
  · exact Nat.eq_zero_of_le_zero (hzero ▸ raw.right_slot_count b ξ)

end ParentGeometry

theorem left_parameters_nonneg (b : family.active labels) :
    0 ≤ (family.leftParameters labels b).m + (family.leftParameters labels b).q ∧
      0 ≤ (family.leftParameters labels b).n₁ ∧
      0 ≤ (family.leftParameters labels b).n₂ :=
  ⟨(family.leftChild labels b).parameters_width_nonneg,
    (family.leftChild labels b).plain_left_nonneg,
    (family.leftChild labels b).plain_right_nonneg⟩

theorem right_parameters_nonneg (b : family.active labels) :
    0 ≤ (family.rightParameters labels b).m + (family.rightParameters labels b).q ∧
      0 ≤ (family.rightParameters labels b).n₁ ∧
      0 ≤ (family.rightParameters labels b).n₂ :=
  ⟨(family.rightChild labels b).parameters_width_nonneg,
    (family.rightChild labels b).plain_left_nonneg,
    (family.rightChild labels b).plain_right_nonneg⟩

theorem actual_total_lengths (b : family.active labels) (ξ : V) :
    (family.leftParameters labels b).z = (family.leftData labels b ξ).geometry.totalLength ∧
      (family.rightParameters labels b).z = (family.rightData labels b ξ).geometry.totalLength :=
  ⟨(family.leftChild labels b).frozen_total_length ξ,
    (family.rightChild labels b).frozen_total_length ξ⟩

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.ParentGeometry.zero_slots
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.actual_total_lengths
