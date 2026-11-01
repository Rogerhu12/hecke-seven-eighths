import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Centering
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.LengthStages

/-!
# The actual geometric branches of the paired core

The geometric length `z` is the sum of the actual positive slot lengths.
Capacity therefore places the positive-slot nodes in `A ≤ M`, uniformly
for every `κ ≥ 3/4`, including `κ = 1`.  A zero-slot node is placed in the
padded core by ordinary reflection before the width-floor bound is used.

In the large-`A` range, the two plain lengths are either short on one side
or both at least `M/4`.  The latter case uses the canonical comparison
rectangle with lengths `M/4` and `n₁+n₂-M/4`.  The construction retains
the actual polynomial data, both profiles, every slot and the common mask.
Its raw comparison has the same total length and the same proof stage;
only a subsequent genuine reflection can make that comparison earlier.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The slot geometry uses strictly positive lengths, even when the
finite set of slots is empty. -/
theorem slotGeometry_totalLength_nonneg (g : SlotGeometry K) :
    0 ≤ g.totalLength := by
  unfold SlotGeometry.totalLength
  exact Finset.sum_nonneg fun i _ => (g.slots i).length_pos.le

namespace Node

theorem slot_nonneg (n : Node K ω ψ)
    (hlength : n.parameters.z = n.data.geometry.totalLength) :
    0 ≤ n.parameters.z := by
  rw [hlength]
  exact slotGeometry_totalLength_nonneg n.data.geometry

/-- Positive-slot capacity is stronger than the total-length core bound.
There is no upper bound on `κ` in this implication. -/
theorem totalLength_le_width_of_capacity (n : Node K ω ψ)
    (hlength : n.parameters.z = n.data.geometry.totalLength)
    (hκ : 3 / 4 ≤ n.parameters.κ)
    (hcapacity : n.parameters.n₁ + n.parameters.n₂ +
      6 * n.parameters.κ * n.parameters.z ≤ n.width) :
    n.totalLength ≤ n.width :=
  positive_capacity_total_length (n.slot_nonneg hlength) hκ hcapacity

/-- The zero-slot padded core gives the actual absolute-counting
condition used by the base branch. -/
theorem base_length_of_zero_padded_core (n : Node K ω ψ)
    {floor padding : ℝ} (hfloor : 0 ≤ floor)
    (hlength : n.parameters.z = n.data.geometry.totalLength)
    (hzero : n.parameters.z = 0)
    (hcore : n.parameters.n₁ + n.parameters.n₂ ≤ n.width + padding)
    (hwidth : n.width ≤ floor) :
    n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤
      floor + padding + floor / 6 := by
  rw [← hlength, hzero]
  linarith

/-- Positive capacity supplies the same base condition at the width
floor, using the actual slot length rather than a weighted surrogate. -/
theorem base_length_of_positive_capacity (n : Node K ω ψ)
    {floor padding : ℝ} (hfloor : 0 ≤ floor) (hpadding : 0 ≤ padding)
    (hlength : n.parameters.z = n.data.geometry.totalLength)
    (hκ : 3 / 4 ≤ n.parameters.κ)
    (hcapacity : n.parameters.n₁ + n.parameters.n₂ +
      6 * n.parameters.κ * n.parameters.z ≤ n.width)
    (hwidth : n.width ≤ floor) :
    n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤
      floor + padding + floor / 6 := by
  have hcore := n.totalLength_le_width_of_capacity hlength hκ hcapacity
  change n.parameters.n₁ + n.parameters.n₂ + n.parameters.z ≤ n.width at hcore
  rw [← hlength]
  linarith

/-- Apply this split after detecting `A > 5*M/6`.  Its first alternative
is the ordinary-reflection branch; the second permits quarter centering. -/
theorem plain_quarter_cases (n : Node K ω ψ) :
    (n.parameters.n₁ < n.width / 4 ∨ n.parameters.n₂ < n.width / 4) ∨
      (n.width / 4 ≤ n.parameters.n₁ ∧ n.width / 4 ≤ n.parameters.n₂) := by
  by_cases h₁ : n.width / 4 ≤ n.parameters.n₁
  · by_cases h₂ : n.width / 4 ≤ n.parameters.n₂
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inl (Or.inr (lt_of_not_ge h₂))
  · exact Or.inl (Or.inl (lt_of_not_ge h₁))

/-- Canonical equal-product centering at the actual quarter width. -/
def quarterCentered (n : Node K ω ψ) : Node K ω ψ where
  data := n.data
  parameters := n.parameters
  centered := true
  comparison₁ := n.width / 4
  comparison₂ := n.parameters.n₁ + n.parameters.n₂ - n.width / 4
  comparison_sum := by ring

@[simp] theorem quarterCentered_data (n : Node K ω ψ) :
    n.quarterCentered.data = n.data := rfl

@[simp] theorem quarterCentered_parameters (n : Node K ω ψ) :
    n.quarterCentered.parameters = n.parameters := rfl

@[simp] theorem quarterCentered_centered (n : Node K ω ψ) :
    n.quarterCentered.centered = true := rfl

@[simp] theorem quarterCentered_width (n : Node K ω ψ) :
    n.quarterCentered.width = n.width := rfl

@[simp] theorem quarterCentered_totalLength (n : Node K ω ψ) :
    n.quarterCentered.totalLength = n.totalLength := rfl

@[simp] theorem quarterCentered_lengthStage (n : Node K ω ψ) :
    n.quarterCentered.lengthStage = n.lengthStage := rfl

/-- Both comparison lengths are at least a quarter width in the centered
branch.  Nonnegativity follows as soon as the width is nonnegative. -/
theorem quarterCentered_comparison_lengths (n : Node K ω ψ)
    (h₁ : n.width / 4 ≤ n.parameters.n₁)
    (h₂ : n.width / 4 ≤ n.parameters.n₂) :
    n.quarterCentered.comparison₁ = n.width / 4 ∧
      n.width / 4 ≤ n.quarterCentered.comparison₂ := by
  refine ⟨rfl, ?_⟩
  change n.width / 4 ≤ n.parameters.n₁ + n.parameters.n₂ - n.width / 4
  linarith

/-- This is an equality of the actual rectangle scale products. -/
theorem quarterCentered_scale_product (n : Node K ω ψ) {U : ℝ} (hU : 0 < U) :
    U ^ (n.width / 4) * U ^ (n.parameters.n₁ + n.parameters.n₂ - n.width / 4) =
      U ^ n.parameters.n₁ * U ^ n.parameters.n₂ :=
  n.quarterCentered.comparison_product hU

/-- The raw comparison retains the original sum of the plain lengths. -/
@[simp] theorem comparison_totalLength (n : Node K ω ψ) :
    n.comparisonOrdinary.totalLength = n.totalLength := by
  change n.comparison₁ + n.comparison₂ + n.parameters.z =
    n.parameters.n₁ + n.parameters.n₂ + n.parameters.z
  rw [n.comparison_sum]

@[simp] theorem comparison_lengthStage (n : Node K ω ψ) :
    n.comparisonOrdinary.lengthStage = n.lengthStage := by
  simp only [lengthStage, comparison_totalLength, comparison_width]

/-- Centering is an actual finite-energy decomposition on the original
rows, before any reflected-comparison estimate is applied. -/
theorem quarterCentered_energy_decomposition (n : Node K ω ψ) (U t : ℝ) :
    pairedEnergy n.data n.parameters U t ≤
      2 * n.quarterCentered.energy U t +
        2 * n.quarterCentered.comparisonOrdinary.energy U t :=
  n.quarterCentered.pairedEnergy_le_centered_add_comparison rfl U t

end Node

namespace PolynomialSystem

variable {σ W : ℝ}

/-- Equal actual slot regime, width and total length give the same
length-based schedule, independently of the centered Boolean. -/
theorem same_length_schedule (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (htotal : (S.node child).totalLength = (S.node parent).totalLength) :
    S.withLengthStages.schedule child = S.withLengthStages.schedule parent := by
  have hslot :
      (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
        (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1) := by
    rw [hslots]
  have hband :
      boundedBand σ (S.node child).width W S.sigma_pos (S.width_le child) =
        boundedBand σ (S.node parent).width W S.sigma_pos (S.width_le parent) := by
    apply Fin.ext
    change widthBand σ (S.node child).width = widthBand σ (S.node parent).width
    rw [hwidth]
  have hstage : (S.node child).lengthStage = (S.node parent).lengthStage := by
    unfold Node.lengthStage
    rw [htotal, hwidth]
  dsimp only [PolynomialSystem.schedule, PolynomialSystem.withLengthStages]
  rw [hslot, hband, hstage]

theorem quarterCentered_same_schedule (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hchild : S.node child = (S.node parent).quarterCentered) :
    S.withLengthStages.schedule child = S.withLengthStages.schedule parent := by
  apply S.same_length_schedule child parent
  · rw [hchild]
    rfl
  · rw [hchild]
    rfl
  · rw [hchild]
    rfl

/-- In particular, the unreflected comparison does not become an earlier
stage merely because its coefficient is ordinary. -/
theorem comparison_same_length_schedule (S : PolynomialSystem.{u} K ω ψ σ W)
    (child parent : S.Label)
    (hchild : S.node child = (S.node parent).comparisonOrdinary) :
    S.withLengthStages.schedule child = S.withLengthStages.schedule parent := by
  apply S.same_length_schedule child parent
  · rw [hchild]
    exact (S.node parent).comparison_slots
  · rw [hchild]
    exact (S.node parent).comparison_width
  · rw [hchild]
    exact (S.node parent).comparison_totalLength

end PolynomialSystem

end HeckeSkeleton.Moments.EngineInduction
