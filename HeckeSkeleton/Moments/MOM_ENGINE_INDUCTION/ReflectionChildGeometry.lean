import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCommonReflection
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalNodeFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependent

/-!
# The actual fixed-line reflection children remain in the geometric family

The reflected factor is the longer actual plain factor, with the shorter
one retained literally. A common dyadic cutoff supplies a nonnegative new
plain exponent for every retained frequency and both contour lines.
The numerical bounds retain the full slot length and the actual kappa.

For positive slots the original capacity, the large-total-length branch
and kappa at least 3/4 give z<M/20. Together with boundary<=M/15 these
facts prove the child's full positive capacity, not merely its earlier
length stage. Zero-slot capacity remains the original zero-slot fact.
The constructors at the end therefore need only the child's primitive
arithmetic/profile admissibility; no child moment estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Ties may use the first factor; both choices have the same lengths. -/
def reflectionLongFirst (a : RealParameters) : Bool := decide (a.n₂ ≤ a.n₁)

theorem reflectionLongFirst_long (a : RealParameters) :
    (if reflectionLongFirst a then a.n₁ else a.n₂) = max a.n₁ a.n₂ := by
  by_cases h : a.n₂ ≤ a.n₁
  · simp only [reflectionLongFirst, h, decide_true, if_true, max_eq_left h]
  · have h' : a.n₁ ≤ a.n₂ := (lt_of_not_ge h).le
    simp only [reflectionLongFirst, h, decide_false, Bool.false_eq_true, if_false,
      max_eq_right h']

theorem reflectionLongFirst_short (a : RealParameters) :
    (if reflectionLongFirst a then a.n₂ else a.n₁) = min a.n₁ a.n₂ := by
  by_cases h : a.n₂ ≤ a.n₁
  · simp only [reflectionLongFirst, h, decide_true, if_true, min_eq_right h]
  · have h' : a.n₁ ≤ a.n₂ := (lt_of_not_ge h).le
    simp only [reflectionLongFirst, h, decide_false, Bool.false_eq_true, if_false,
      min_eq_left h']

theorem reflection_short_le_quarter {a b M : ℝ}
    (h : a ≤ M / 4 ∨ b ≤ M / 4) : min a b ≤ M / 4 := by
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

/-- The two actual slot costs fit inside the strict large-length margin.
This proves the full capacity needed to admit the reflected child. -/
theorem positive_reflection_child_capacity
    {A M z κ child boundary : ℝ} (hz : 0 ≤ z) (hκ : 3 / 4 ≤ κ)
    (hlarge : 5 * M / 6 < A) (hcapacity : A + (6 * κ - 1) * z ≤ M)
    (hchild : child ≤ 3 * M / 2 - A + 2 * z + boundary)
    (hboundary : boundary ≤ M / 15) :
    child + (6 * κ - 1) * z ≤ M := by
  have hsmall := centered_positive_slot_length hz hκ hlarge hcapacity
  nlinarith

namespace Node

/-- The actual child keeps all numerical invariants outside the chosen
plain exponent and keeps the exact original slot count and total length. -/
theorem fixedLineReflectionChild_invariants (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    let child := node.fixedLineReflectionChild first U E0 hE0 childOrder x
    child.parameters.m = node.parameters.m ∧ child.parameters.q = node.parameters.q ∧
      child.parameters.z = node.parameters.z ∧ child.parameters.κ = node.parameters.κ ∧
      child.width = node.width ∧ child.data.geometry.slotCount = node.data.geometry.slotCount ∧
      child.data.geometry.totalLength = node.data.geometry.totalLength ∧ child.centered = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fixedLineReflectionChild_plain_nonneg (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder : ℕ)
    (x : (ℕ × Bool) × ℝ)
    (hleft : 0 ≤ node.parameters.n₁) (hright : 0 ≤ node.parameters.n₂) :
    let child := node.fixedLineReflectionChild first U E0 hE0 childOrder x
    0 ≤ child.parameters.n₁ ∧ 0 ≤ child.parameters.n₂ := by
  have hj := reflectionDyadicExponent_nonneg hU x.1.1
  cases first with
  | false => exact ⟨hleft, hj⟩
  | true => exact ⟨hj, hright⟩

theorem fixedLineReflectionChild_plain_sum (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    let child := node.fixedLineReflectionChild first U E0 hE0 childOrder x
    child.parameters.n₁ + child.parameters.n₂ =
      (if first then node.parameters.n₂ else node.parameters.n₁) +
        reflectionDyadicExponent U x.1.1 := by
  cases first with
  | false => rfl
  | true => exact add_comm _ _

theorem fixedLongReflectionChild_totalLength (node : Node K ω ψ)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).totalLength =
        min node.parameters.n₁ node.parameters.n₂ + reflectionDyadicExponent U x.1.1 +
          node.parameters.z := by
  change (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).parameters.n₁ +
    (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).parameters.n₂ + node.parameters.z = _
  rw [fixedLineReflectionChild_plain_sum, reflectionLongFirst_short]

/-- The same primitive arithmetic, full remaining mask and non-norm
condition are available at every fixed-line frequency child. -/
theorem fixedLineReflectionChild_arithmetic (node : Node K ω ψ) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    ReflectionArithmeticPreserved node
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x) U :=
  node.normalizedOrdinaryPowerChildNode_reflectionArithmetic first
    (reflectionFixedLine x.1.2) (-x.2) (reflectionDyadicExponent U x.1.1)
    E0 hE0 childOrder U

theorem fixedLineReflectionChild_timeIndependent (node : Node K ω ψ)
    (h : ProfileTimeIndependent node.data) (first : Bool)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ) :
    ProfileTimeIndependent (node.fixedLineReflectionChild first U E0 hE0 childOrder x).data :=
  h.normalizedOrdinaryPowerChild first (reflectionFixedLine x.1.2) (-x.2) E0 hE0 childOrder

/-- The genuine short-factor branch and the genuine quarter comparison
both satisfy this calculation. The longer factor is selected internally. -/
theorem fixedLongReflectionChild_comparison_length (node : Node K ω ψ)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (padding boundary : ℝ)
    (hlength : node.parameters.z = node.data.geometry.totalLength)
    (hshort : node.parameters.n₁ ≤ node.width / 4 ∨ node.parameters.n₂ ≤ node.width / 4)
    (hcore : node.totalLength ≤ node.width + padding) (hpadding : padding ≤ node.width / 4)
    (hnext : reflectionDyadicExponent U x.1.1 ≤
      max (node.width - max node.parameters.n₁ node.parameters.n₂) 0 + boundary) :
    (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).totalLength ≤
        3 * node.width / 2 - node.totalLength + 2 * node.parameters.z + boundary := by
  have h := reflection_comparison_child_length (node.slot_nonneg hlength)
    (reflection_short_le_quarter hshort)
    (show min node.parameters.n₁ node.parameters.n₂ + max node.parameters.n₁ node.parameters.n₂ +
        node.parameters.z ≤ node.width + padding by
      rw [min_add_max]
      exact hcore) hpadding hnext
  rw [fixedLongReflectionChild_totalLength]
  simpa only [min_add_max] using h

/-- Capacity is proved with the original kappa, including its endpoint.
No absolute-slot estimate silently substitutes kappa*z for z. -/
theorem fixedLongReflectionChild_comparison_capacity (node : Node K ω ψ)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (boundary : ℝ)
    (hlength : node.parameters.z = node.data.geometry.totalLength)
    (hκ : 3 / 4 ≤ node.parameters.κ)
    (hcapacity : node.parameters.z = 0 ∨ node.parameters.n₁ + node.parameters.n₂ +
      6 * node.parameters.κ * node.parameters.z ≤ node.width)
    (hlarge : 5 * node.width / 6 < node.totalLength)
    (hchild : (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).totalLength ≤
        3 * node.width / 2 - node.totalLength + 2 * node.parameters.z + boundary)
    (hboundary : boundary ≤ node.width / 15) :
    let child := node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x
    child.parameters.z = 0 ∨ child.parameters.n₁ + child.parameters.n₂ +
      6 * child.parameters.κ * child.parameters.z ≤ child.width := by
  rcases hcapacity with hzero | hcap
  · exact Or.inl hzero
  · right
    let child := node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x
    have hcap' : node.totalLength + (6 * node.parameters.κ - 1) * node.parameters.z ≤
        node.width := by
      change node.parameters.n₁ + node.parameters.n₂ + node.parameters.z +
        (6 * node.parameters.κ - 1) * node.parameters.z ≤ node.width
      nlinarith
    have h := positive_reflection_child_capacity (node.slot_nonneg hlength) hκ hlarge
      hcap' hchild hboundary
    change child.parameters.n₁ + child.parameters.n₂ +
      6 * node.parameters.κ * node.parameters.z ≤ node.width
    change child.parameters.n₁ + child.parameters.n₂ + node.parameters.z +
      (6 * node.parameters.κ - 1) * node.parameters.z ≤ node.width at h
    nlinarith

/-- An outer zero-slot reflection really returns to the padded core.
The whole-series branch handles lengths beyond the stated threshold. -/
theorem fixedLongReflectionChild_outer_core (node : Node K ω ψ)
    (U E0 : ℝ) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (gap boundary padding : ℝ) (hzero : node.parameters.z = 0) (hgap : 0 ≤ gap)
    (hlong : max node.parameters.n₁ node.parameters.n₂ ≤ node.width + gap)
    (hnext : reflectionDyadicExponent U x.1.1 ≤
      max (node.width - max node.parameters.n₁ node.parameters.n₂) 0 + boundary)
    (hbudget : gap + boundary ≤ padding) :
    (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
      U E0 hE0 childOrder x).totalLength ≤ node.width + padding := by
  have h := reflection_outer_child_core hgap
    ((min_le_left node.parameters.n₁ node.parameters.n₂).trans
      (le_max_left node.parameters.n₁ node.parameters.n₂)) hlong hnext hbudget
  rw [fixedLongReflectionChild_totalLength, hzero, add_zero]
  exact h

private theorem fixedLineReflectionChild_invariant_of_capacity
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} (node : Node K ω ψ)
    (hnode : UniversalNodeInvariant primitive W padding cap node) (first : Bool)
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (hcapacity :
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters.z = 0 ∨
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters.n₁ +
        (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters.n₂ +
        6 * (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters.κ *
          (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters.z ≤ node.width)
    (hadmissible : admissibleOfInvariant primitive
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x).data
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x).parameters) :
    UniversalNodeInvariant primitive W padding cap
      (node.fixedLineReflectionChild first U E0 hE0 childOrder x) := by
  let child := node.fixedLineReflectionChild first U E0 hE0 childOrder x
  have hn := node.fixedLineReflectionChild_plain_nonneg first U E0 hU hE0 childOrder x
    hnode.plain_left_nonneg hnode.plain_right_nonneg
  exact (UniversalNode.ordinary primitive W padding cap child.data child.parameters
    hnode.length hn.1 hn.2 hnode.kappa_lower hnode.kappa_upper hcapacity
    hnode.width_nonneg hnode.width_le hnode.slot_count hadmissible).property

/-- Actual comparison children enter the universal family after only
primitive arithmetic/profile admissibility has been supplied. -/
theorem fixedLongReflectionChild_comparison_invariant
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} (node : Node K ω ψ)
    (hnode : UniversalNodeInvariant primitive W padding cap node)
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (boundary : ℝ)
    (hshort : node.parameters.n₁ ≤ node.width / 4 ∨ node.parameters.n₂ ≤ node.width / 4)
    (hcore : node.totalLength ≤ node.width + padding) (hpadding : padding ≤ node.width / 4)
    (hlarge : 5 * node.width / 6 < node.totalLength) (hboundary : boundary ≤ node.width / 15)
    (hnext : reflectionDyadicExponent U x.1.1 ≤
      max (node.width - max node.parameters.n₁ node.parameters.n₂) 0 + boundary)
    (hadmissible : admissibleOfInvariant primitive
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x).data
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x).parameters) :
    UniversalNodeInvariant primitive W padding cap
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x) := by
  have hl := node.fixedLongReflectionChild_comparison_length U E0 hE0 childOrder x
    padding boundary hnode.length hshort hcore hpadding hnext
  have hc := node.fixedLongReflectionChild_comparison_capacity U E0 hE0 childOrder x
    boundary hnode.length hnode.kappa_lower hnode.capacity hlarge hl hboundary
  exact fixedLineReflectionChild_invariant_of_capacity node hnode
    (reflectionLongFirst node.parameters) U E0 hU hE0 childOrder x hc hadmissible

/-- The zero-slot outer child has the original zero-slot capacity. Its
padded-core bound is the separately proved actual length calculation. -/
theorem fixedLongReflectionChild_outer_invariant
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} (node : Node K ω ψ)
    (hnode : UniversalNodeInvariant primitive W padding cap node)
    (U E0 : ℝ) (hU : 1 < U) (hE0 : 1 ≤ E0) (childOrder : ℕ) (x : (ℕ × Bool) × ℝ)
    (hzero : node.parameters.z = 0)
    (hadmissible : admissibleOfInvariant primitive
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x).data
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x).parameters) :
    UniversalNodeInvariant primitive W padding cap
      (node.fixedLineReflectionChild (reflectionLongFirst node.parameters)
        U E0 hE0 childOrder x) :=
  fixedLineReflectionChild_invariant_of_capacity node hnode
    (reflectionLongFirst node.parameters) U E0 hU hE0 childOrder x (Or.inl hzero) hadmissible

end Node
end HeckeSkeleton.Moments.EngineInduction
