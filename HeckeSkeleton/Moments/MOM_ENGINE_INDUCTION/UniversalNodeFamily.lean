import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreRecursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileOrderSchedule

/-!
# The actual universal node family and its concrete labels

Labels are genuine `Node` values satisfying primitive admissibility and
all geometric invariants used by the induction. An `ULift` only matches
the universe of the fixed continuous kernel parameter. The polynomial
family has no arbitrary energy field and assumes no local reduction.

Primitive admissibility sees the original data and the five numerical
quantities m, q, z, kappa and the sum of the plain lengths. Thus equal-
product quarter centering and its raw comparison preserve admissibility
by equality. The actual profile-order rank factors through precisely
these quantities. Ordinary reflection and the canonical strict output
enter the same subtype once their genuine geometric and primitive
calibrations have been proved; no label-existence assumption remains.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open scoped Classical

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Exactly the numerical data preserved by an equal-product comparison. -/
structure PairedInvariantParameters where
  m : ℝ
  q : ℝ
  z : ℝ
  kappa : ℝ
  plainSum : ℝ

def pairedInvariantParameters (a : RealParameters) : PairedInvariantParameters :=
  ⟨a.m, a.q, a.z, a.κ, a.n₁ + a.n₂⟩

/-- A representative is used only to evaluate the existing numerical
rank, never to replace any actual node or polynomial rectangle. -/
def PairedInvariantParameters.parameters (p : PairedInvariantParameters) : RealParameters :=
  ⟨p.m, 0, p.z, p.q, p.plainSum, 0, p.kappa⟩

theorem pairedInvariantParameters_coreRank (σ W padding : ℝ) (a : RealParameters) :
    parameterCoreRank σ W padding (pairedInvariantParameters a).parameters =
      parameterCoreRank σ W padding a := by
  simp only [parameterCoreRank, PairedInvariantParameters.parameters,
    pairedInvariantParameters, add_zero]

/-- The producer's admissible predicate is a primitive predicate on
actual data and the invariant numerical quantities, not an energy bound. -/
def admissibleOfInvariant
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop :=
  primitive d (pairedInvariantParameters a)

theorem pairedInvariantParameters_comparison (n : Node K ω ψ) :
    pairedInvariantParameters n.comparisonParameters = pairedInvariantParameters n.parameters := by
  change PairedInvariantParameters.mk n.parameters.m n.parameters.q n.parameters.z
      n.parameters.κ (n.comparison₁ + n.comparison₂) =
    PairedInvariantParameters.mk n.parameters.m n.parameters.q n.parameters.z
      n.parameters.κ (n.parameters.n₁ + n.parameters.n₂)
  rw [n.comparison_sum]

/-- Geometry and primitive source facts, with no moment or local-step
conclusion. Centered nodes are the actual legal quarter rectangles. -/
structure UniversalNodeInvariant
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (W padding : ℝ) (cap : ℕ) (n : Node K ω ψ) : Prop where
  length : n.parameters.z = n.data.geometry.totalLength
  plain_left_nonneg : 0 ≤ n.parameters.n₁
  plain_right_nonneg : 0 ≤ n.parameters.n₂
  kappa_lower : 3 / 4 ≤ n.parameters.κ
  kappa_upper : n.parameters.κ ≤ 1
  capacity : n.parameters.z = 0 ∨
    n.parameters.n₁ + n.parameters.n₂ + 6 * n.parameters.κ * n.parameters.z ≤ n.width
  width_nonneg : 0 ≤ n.width
  width_le : n.width ≤ W
  slot_count : n.data.geometry.slotCount ≤ cap
  admissible : admissibleOfInvariant primitive n.data n.parameters
  centered_core : n.centered = true → n.totalLength ≤ n.width + padding
  centered_left : n.centered = true → n.width / 4 ≤ n.parameters.n₁
  centered_right : n.centered = true → n.width / 4 ≤ n.parameters.n₂
  comparison_left : n.centered = true → n.comparison₁ = n.width / 4
  comparison_right : n.centered = true →
    n.comparison₂ = n.parameters.n₁ + n.parameters.n₂ - n.width / 4

/-- The underlying family really is the subtype of actual nodes. -/
def UniversalNode
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (W padding : ℝ) (cap : ℕ) :=
  { n : Node K ω ψ // UniversalNodeInvariant primitive W padding cap n }

namespace UniversalNodeInvariant

variable {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
variable {W padding : ℝ} {cap : ℕ} {n : Node K ω ψ}

/-- Quarter centering retains the actual data and parameters literally. -/
theorem quarterCentered (h : UniversalNodeInvariant primitive W padding cap n)
    (hcore : n.totalLength ≤ n.width + padding)
    (hleft : n.width / 4 ≤ n.parameters.n₁) (hright : n.width / 4 ≤ n.parameters.n₂) :
    UniversalNodeInvariant primitive W padding cap n.quarterCentered where
  length := h.length
  plain_left_nonneg := h.plain_left_nonneg
  plain_right_nonneg := h.plain_right_nonneg
  kappa_lower := h.kappa_lower
  kappa_upper := h.kappa_upper
  capacity := h.capacity
  width_nonneg := h.width_nonneg
  width_le := h.width_le
  slot_count := h.slot_count
  admissible := h.admissible
  centered_core _ := hcore
  centered_left _ := hleft
  centered_right _ := hright
  comparison_left _ := rfl
  comparison_right _ := rfl

/-- The ordinary raw comparison is also in the family. Its two actual
lengths are nonnegative by the quarter lower bounds and true width.
Its admissibility uses only equality of the original plain-length sum. -/
theorem comparisonOrdinary (h : UniversalNodeInvariant primitive W padding cap n)
    (hcentered : n.centered = true) :
    UniversalNodeInvariant primitive W padding cap n.comparisonOrdinary := by
  have hsum := n.comparison_sum
  have hleft := h.centered_left hcentered
  have hright := h.centered_right hcentered
  have hc₁ := h.comparison_left hcentered
  have hc₂ := h.comparison_right hcentered
  refine {
    length := h.length
    plain_left_nonneg := ?_
    plain_right_nonneg := ?_
    kappa_lower := h.kappa_lower
    kappa_upper := h.kappa_upper
    capacity := ?_
    width_nonneg := h.width_nonneg
    width_le := h.width_le
    slot_count := h.slot_count
    admissible := ?_
    centered_core := ?_
    centered_left := ?_
    centered_right := ?_
    comparison_left := ?_
    comparison_right := ?_ }
  · change 0 ≤ n.comparison₁
    linarith [h.width_nonneg]
  · change 0 ≤ n.comparison₂
    linarith [h.width_nonneg]
  · rcases h.capacity with hzero | hcap
    · exact Or.inl hzero
    · right
      change n.comparison₁ + n.comparison₂ + 6 * n.parameters.κ * n.parameters.z ≤ n.width
      rw [hsum]
      exact hcap
  · change primitive n.data (pairedInvariantParameters n.comparisonParameters)
    rw [pairedInvariantParameters_comparison]
    exact h.admissible
  all_goals intro hfalse; cases hfalse

end UniversalNodeInvariant

namespace UniversalNode

variable (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
variable (W padding : ℝ) (cap : ℕ)

/-- A genuine ordinary polynomial enters the subtype from its primitive
source facts and numerical geometry alone. -/
def ordinary (d : MomentData K ω ψ) (a : RealParameters)
    (hlength : a.z = d.geometry.totalLength)
    (hleft : 0 ≤ a.n₁) (hright : 0 ≤ a.n₂)
    (hκlower : 3 / 4 ≤ a.κ) (hκupper : a.κ ≤ 1)
    (hcapacity : a.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q)
    (hwidth : 0 ≤ a.m + a.q) (hW : a.m + a.q ≤ W)
    (hslots : d.geometry.slotCount ≤ cap)
    (hadmissible : admissibleOfInvariant primitive d a) : UniversalNode primitive W padding cap :=
  ⟨Node.ordinary d a, {
    length := hlength
    plain_left_nonneg := hleft
    plain_right_nonneg := hright
    kappa_lower := hκlower
    kappa_upper := hκupper
    capacity := hcapacity
    width_nonneg := hwidth
    width_le := hW
    slot_count := hslots
    admissible := hadmissible
    centered_core := by intro h; cases h
    centered_left := by intro h; cases h
    centered_right := by intro h; cases h
    comparison_left := by intro h; cases h
    comparison_right := by intro h; cases h }⟩

variable {primitive W padding cap}

def quarterCentered (x : UniversalNode primitive W padding cap)
    (hcore : x.val.totalLength ≤ x.val.width + padding)
    (hleft : x.val.width / 4 ≤ x.val.parameters.n₁)
    (hright : x.val.width / 4 ≤ x.val.parameters.n₂) : UniversalNode primitive W padding cap :=
  ⟨x.val.quarterCentered, x.property.quarterCentered hcore hleft hright⟩

def comparisonOrdinary (x : UniversalNode primitive W padding cap)
    (hcentered : x.val.centered = true) : UniversalNode primitive W padding cap :=
  ⟨x.val.comparisonOrdinary, x.property.comparisonOrdinary hcentered⟩

end UniversalNode

/-- The only lift matches the existing continuous recursion universe.
The evaluated polynomial is the unchanged underlying subtype value. -/
def universalPolynomialSystem
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding : ℝ) (cap : ℕ) (hσ : 0 < σ) : PolynomialSystem.{u} K ω ψ σ W where
  Label := ULift.{u} (UniversalNode primitive W padding cap)
  node x := x.down.val
  proofStage x := x.down.val.coreStage padding
  sigma_pos := hσ
  width_nonneg x := x.down.property.width_nonneg
  width_le x := x.down.property.width_le

theorem universalPolynomialSystem_geometry
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding : ℝ) (cap : ℕ) (hσ : 0 < σ) :
    CoreNodeGeometry (universalPolynomialSystem.{u} primitive σ W padding cap hσ) padding where
  length x := x.down.property.length
  plain_left_nonneg x := x.down.property.plain_left_nonneg
  plain_right_nonneg x := x.down.property.plain_right_nonneg
  kappa_lower x := x.down.property.kappa_lower
  kappa_upper x := x.down.property.kappa_upper
  capacity x := x.down.property.capacity
  centered_core x := x.down.property.centered_core
  centered_left x := x.down.property.centered_left
  centered_right x := x.down.property.centered_right
  comparison_left x := x.down.property.comparison_left
  comparison_right x := x.down.property.comparison_right

theorem universalPolynomialSystem_admissible
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding : ℝ) (cap : ℕ) (hσ : 0 < σ)
    (x : (universalPolynomialSystem.{u} primitive σ W padding cap hσ).Label) :
    admissibleOfInvariant primitive x.down.val.data x.down.val.parameters :=
  x.down.property.admissible

/-- The two actual same-product labels are constructed in the legal
centering case, with no separately assumed family-label witness. -/
def universalQuarterLabels
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding : ℝ) (cap : ℕ) (hσ : 0 < σ)
    (x : (universalPolynomialSystem.{u} primitive σ W padding cap hσ).Label)
    (hcore : x.down.val.totalLength ≤ x.down.val.width + padding)
    (hleft : x.down.val.width / 4 ≤ x.down.val.parameters.n₁)
    (hright : x.down.val.width / 4 ≤ x.down.val.parameters.n₂) :
    QuarterLabels (universalPolynomialSystem.{u} primitive σ W padding cap hσ) x where
  center := ⟨x.down.quarterCentered hcore hleft hright⟩
  comparison := ⟨(x.down.quarterCentered hcore hleft hright).comparisonOrdinary rfl⟩
  center_eq := rfl
  comparison_eq := rfl

/-- Canonical outputs acquire actual subtype labels from their proved
geometry. The only profile premises concern the literal frozen child
data; freezing arbitrary profile-dependent admissibility is not assumed
by definitional equality. A producer may supply its genuine freeze
stability theorem to these two primitive premises. -/
def universalEngineBranchAt {Ω : Type u} [MeasurableSpace Ω]
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (σ W padding : ℝ) (cap : ℕ) (hσ : 0 < σ)
    (x : (universalPolynomialSystem.{u} primitive σ W padding cap hσ).Label)
    (U δ β C control : ℝ)
    (out : x.down.val.EngineOutput (Ω := Ω) U σ δ β C control
      (admissibleOfInvariant primitive))
    (hleft : ∀ b ξ, admissibleOfInvariant primitive
      (freezeMomentTime (out.leftData b ξ) (out.leftTwist b ξ)) (out.leftParameters b))
    (hright : ∀ b ξ, admissibleOfInvariant primitive
      (freezeMomentTime (out.rightData b ξ) (out.rightTwist b ξ)) (out.rightParameters b)) :
    EngineBranchAt (Ω := Ω) (universalPolynomialSystem.{u} primitive σ W padding cap hσ)
      x U δ β C control (admissibleOfInvariant primitive) := by
  let left (b : Fin out.branches) (ξ : Ω) :
      UniversalNode primitive W padding cap :=
    UniversalNode.ordinary primitive W padding cap
      (freezeMomentTime (out.leftData b ξ) (out.leftTwist b ξ)) (out.leftParameters b)
      (out.left_length b ξ) (out.left_plain_left_nonneg b) (out.left_plain_right_nonneg b)
      (by rw [out.left_kappa]; exact x.down.property.kappa_lower)
      (by rw [out.left_kappa]; exact x.down.property.kappa_upper)
      (out.left_capacity b) (out.left_width_nonneg b)
      (by
        have hp : x.down.val.parameters.m + x.down.val.parameters.q ≤ W :=
          x.down.property.width_le
        have hc := out.left_width b
        linarith)
      ((out.left_slots b ξ).trans x.down.property.slot_count) (hleft b ξ)
  let right (b : Fin out.branches) (ξ : Ω) :
      UniversalNode primitive W padding cap :=
    UniversalNode.ordinary primitive W padding cap
      (freezeMomentTime (out.rightData b ξ) (out.rightTwist b ξ)) (out.rightParameters b)
      (out.right_length b ξ) (out.right_plain_left_nonneg b) (out.right_plain_right_nonneg b)
      (by rw [out.right_kappa]; exact x.down.property.kappa_lower)
      (by rw [out.right_kappa]; exact x.down.property.kappa_upper)
      (out.right_capacity b) (out.right_width_nonneg b)
      (by
        have hp : x.down.val.parameters.m + x.down.val.parameters.q ≤ W :=
          x.down.property.width_le
        have hc := out.right_width b
        linarith)
      ((out.right_slots b ξ).trans x.down.property.slot_count) (hright b ξ)
  exact {
    output := out
    left := fun b ξ => ⟨left b ξ⟩
    right := fun b ξ => ⟨right b ξ⟩
    left_eq := fun _ _ => rfl
    right_eq := fun _ _ => rfl }

end HeckeSkeleton.Moments.EngineInduction
