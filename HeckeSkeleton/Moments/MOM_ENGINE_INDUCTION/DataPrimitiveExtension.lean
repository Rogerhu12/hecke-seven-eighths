import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMesh

/-!
# Preserving an additional literal data primitive during reflection

The additional predicate reads only the actual `MomentData`. Applications
use concrete complete-row, fixed remaining-ideal, character and theta
dictionaries. Its only closure obligation below is a statement about the
literal fixed-line child constructor, before any energy inequality or
reflection output is formed.

This interface is not intended for a moment bound or for an existential
completed engine output. Such a replacement would change the producer
obligation rather than construct its arithmetic input. The actual
application must provide the source dictionary and prove this literal
transport from its concrete fields.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Adjoin a predicate on the actual data while retaining every old
parameter-dependent primitive. -/
def withDataPrimitive
    (Q : MomentData K ω ψ → Prop)
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  Q d ∧ primitive d p

/-- A literal constructor-preservation statement. No energy, measure,
opaque local output, admissible label or induction conclusion occurs. -/
def FixedLineDataPreserved (Q : MomentData K ω ψ → Prop) : Prop :=
  ∀ (parent : Node K ω ψ) (first : Bool) (U E : ℝ) (hE : 1 ≤ E)
      (J : ℕ) (x : (ℕ × Bool) × ℝ),
    Q parent.data → Q (parent.fixedLineReflectionChild first U E hE J x).data

/-- Strengthen the actual node before constructing any local output. -/
theorem UniversalNodeInvariant.withDataPrimitive
    {Q : MomentData K ω ψ → Prop}
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} {n : Node K ω ψ}
    (h : UniversalNodeInvariant primitive W padding cap n) (hQ : Q n.data) :
    UniversalNodeInvariant (withDataPrimitive Q primitive) W padding cap n where
  length := h.length
  plain_left_nonneg := h.plain_left_nonneg
  plain_right_nonneg := h.plain_right_nonneg
  kappa_lower := h.kappa_lower
  kappa_upper := h.kappa_upper
  capacity := h.capacity
  width_nonneg := h.width_nonneg
  width_le := h.width_le
  slot_count := h.slot_count
  admissible := ⟨hQ, h.admissible⟩
  centered_core := h.centered_core
  centered_left := h.centered_left
  centered_right := h.centered_right
  comparison_left := h.comparison_left
  comparison_right := h.comparison_right

/-- The actual generic factory now creates its literal child directly
in the stronger subtype. Only the data-constructor law is additional. -/
theorem ReflectionPrimitiveTransfer.withDataPrimitive
    {Q : MomentData K ω ψ → Prop}
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {sigma W padding A lower upper U E : ℝ} {hE : 1 ≤ E}
    {childOrder : ℕ} {parent : Node K ω ψ}
    (hQ : Q parent.data) (hpreserved : FixedLineDataPreserved Q)
    (htransfer : ReflectionPrimitiveTransfer primitive sigma W padding A lower upper
      U E hE childOrder parent) :
    ReflectionPrimitiveTransfer (withDataPrimitive Q primitive) sigma W padding A lower upper
      U E hE childOrder parent := by
  intro x hunit harithmetic hearlier
  exact ⟨hpreserved parent (reflectionLongFirst parent.parameters)
    U E hE childOrder x hQ, htransfer x hunit harithmetic hearlier⟩

end HeckeSkeleton.Moments.EngineInduction
