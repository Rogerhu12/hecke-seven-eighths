import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ScheduleCompatibility

/-!
# The proof stage determined by the actual geometric lengths

The first stage is the uncentered range `A ≤ 5*M/6`, where
`A = n₁+n₂+z`.  It is not the Boolean telling whether a coefficient has
already been centered.  This module assigns that stage to the unchanged
actual polynomial nodes and derives the earlier-comparison edge from the
paper's real reflected-length inequalities.

The reflected child must already have been constructed and calibrated by
the analytic reflection provider.  The equal-product comparison rectangle
before reflection has the old total length and is not asserted to be an
earlier node by this construction.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

def Node.totalLength (n : Node K ω ψ) : ℝ :=
  n.parameters.n₁ + n.parameters.n₂ + n.parameters.z

/-- The proof range is determined by the actual lengths, independently
of the centering operation on the whole polynomial. -/
def Node.lengthStage (n : Node K ω ψ) : Fin 2 :=
  if n.totalLength ≤ 5 * n.width / 6 then 0 else 1

theorem Node.lengthStage_zero (n : Node K ω ψ)
    (h : n.totalLength ≤ 5 * n.width / 6) : n.lengthStage = 0 := by
  simp only [Node.lengthStage, h, if_true]

theorem Node.lengthStage_one (n : Node K ω ψ)
    (h : 5 * n.width / 6 < n.totalLength) : n.lengthStage = 1 := by
  simp only [Node.lengthStage, not_le.mpr h, if_false]

variable {σ W : ℝ}

/-- Change only the proof schedule.  The original labels, whole
polynomial data, widths and all coefficients remain exactly the same. -/
def PolynomialSystem.withLengthStages (S : PolynomialSystem.{u} K ω ψ σ W) :
    PolynomialSystem.{u} K ω ψ σ W where
  Label := S.Label
  node := S.node
  proofStage x := (S.node x).lengthStage
  sigma_pos := S.sigma_pos
  width_nonneg := S.width_nonneg
  width_le := S.width_le

/-- A reflected comparison in the actual core has the earlier stage in
the same width band and same slot regime. -/
theorem PolynomialSystem.comparison_earlier_of_lengths
    (S : PolynomialSystem.{u} K ω ψ σ W) (child parent : S.Label)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (hchild : (S.node child).totalLength ≤ 5 * (S.node child).width / 6)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength) :
    (S.withLengthStages.schedule child).Earlier (S.withLengthStages.schedule parent) := by
  apply State.comparison
  · change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
      (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1)
    rw [hslots]
  · apply Fin.ext
    change widthBand σ (S.node child).width = widthBand σ (S.node parent).width
    rw [hwidth]
  · change (S.node child).lengthStage.val = 0
    simp only [(S.node child).lengthStage_zero hchild, Fin.val_zero]
  · change (S.node parent).lengthStage.val = 1
    simp only [(S.node parent).lengthStage_one hparent, Fin.val_one]

/-- The zero-slot reflected-length inequality gives the required
earlier edge once its aggregate boundary error fits the actual margin. -/
theorem PolynomialSystem.zero_comparison_earlier
    (S : PolynomialSystem.{u} K ω ψ σ W) (child parent : S.Label) (boundary : ℝ)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hcomparison : (S.node child).totalLength ≤
      3 * (S.node parent).width / 2 - (S.node parent).totalLength + boundary)
    (hboundary : boundary ≤ (S.node parent).width / 6) :
    (S.withLengthStages.schedule child).Earlier (S.withLengthStages.schedule parent) := by
  apply S.comparison_earlier_of_lengths child parent hslots hwidth ?_ hparent
  have hmargin := zero_slot_comparison_margin hparent hcomparison
  rw [hwidth]
  linarith

/-- Positive capacity supplies the stricter `z < M/20` margin, with
no restriction below the endpoint `κ = 1`. -/
theorem PolynomialSystem.positive_comparison_earlier
    (S : PolynomialSystem.{u} K ω ψ σ W) (child parent : S.Label) (boundary : ℝ)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (hz : 0 ≤ (S.node parent).parameters.z)
    (hκ : 3 / 4 ≤ (S.node parent).parameters.κ)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hcapacity : (S.node parent).parameters.n₁ + (S.node parent).parameters.n₂ +
      6 * (S.node parent).parameters.κ * (S.node parent).parameters.z ≤
        (S.node parent).width)
    (hcomparison : (S.node child).totalLength ≤
      3 * (S.node parent).width / 2 - (S.node parent).totalLength +
        2 * (S.node parent).parameters.z + boundary)
    (hboundary : boundary ≤ (S.node parent).width / 15) :
    (S.withLengthStages.schedule child).Earlier (S.withLengthStages.schedule parent) := by
  have hcap : (S.node parent).totalLength +
      (6 * (S.node parent).parameters.κ - 1) * (S.node parent).parameters.z ≤
        (S.node parent).width := by
    unfold Node.totalLength
    nlinarith
  have hsmall := centered_positive_slot_length hz hκ hparent hcap
  have hmargin := positive_slot_comparison_margin hsmall hparent hcomparison
  apply S.comparison_earlier_of_lengths child parent hslots hwidth ?_ hparent
  rw [hwidth]
  linarith

/-- Above the chosen width floor, the actual fixed reserve fits both
comparison margins.  It is the same boundary precision as in the total
loss budget, not a new choice made at the current node. -/
theorem moment_mesh_comparison_margins {ε M : ℝ} (hε : 0 < ε)
    (hfloor : 16 * HeckePort.Schedule.amplification ε ≤ M) :
    sourceReserve ε ≤ M / 6 ∧ sourceReserve ε ≤ M / 15 := by
  obtain ⟨hσ, _, _, _, hboundary⟩ := moment_mesh_engine_bounds hε
  constructor <;> linarith

end HeckeSkeleton.Moments.EngineInduction
