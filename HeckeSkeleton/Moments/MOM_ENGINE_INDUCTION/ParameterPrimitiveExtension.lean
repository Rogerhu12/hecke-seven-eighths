import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.DataPrimitiveExtension

/-!
# Retaining actual parameter-dependent source data in the recursive family

A moving source recipe's displayed-support and joint row budgets depend
on q and the total width. They must remain attached to the same recipe
witness when the actual node is labelled. A data-only existence predicate
cannot express that attachment.

This extension retains a predicate of the actual MomentData and its
invariant real parameters. Its closure law is proved directly for the
literal fixed-line constructor, before labels, local outputs or energy
bounds are formed. Existing data-only predicates are a specialization.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The predicate may retain one source recipe together with its exact
q and row-width budgets, without assuming an analytic estimate. -/
def withParameterPrimitive
    (Q : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop)
    (primitive : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop)
    (d : MomentData K omegaCharacter psiCharacter) (p : PairedInvariantParameters) : Prop :=
  Q d p ∧ primitive d p

/-- Only the actual fixed-line node is involved. In particular, this law
is independent of any completed reflection output or recursive bound. -/
def FixedLineParameterPreserved
    (Q : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop) : Prop :=
  ∀ (parent : Node K omegaCharacter psiCharacter) (first : Bool)
      (U E : ℝ) (hE : 1 ≤ E) (J : ℕ) (x : (ℕ × Bool) × ℝ),
    Q parent.data (pairedInvariantParameters parent.parameters) →
      Q (parent.fixedLineReflectionChild first U E hE J x).data
        (pairedInvariantParameters
          (parent.fixedLineReflectionChild first U E hE J x).parameters)

/-- Existing data-only constructor laws require no new hypotheses. -/
theorem FixedLineDataPreserved.parameter
    {Q : MomentData K omegaCharacter psiCharacter → Prop}
    (h : FixedLineDataPreserved Q) :
    FixedLineParameterPreserved (fun d _ => Q d) := h

/-- The unchanged node carries its actual source witness and numerical
budgets together before any local reduction is constructed. -/
theorem UniversalNodeInvariant.withParameterPrimitive
    {Q : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop}
    {primitive : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} {n : Node K omegaCharacter psiCharacter}
    (h : UniversalNodeInvariant primitive W padding cap n)
    (hQ : Q n.data (pairedInvariantParameters n.parameters)) :
    UniversalNodeInvariant (withParameterPrimitive Q primitive) W padding cap n where
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

/-- Extend the real factory's child constructor with the same
parameter-dependent source witness. No child energy is a premise. -/
theorem ReflectionPrimitiveTransfer.withParameterPrimitive
    {Q : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop}
    {primitive : MomentData K omegaCharacter psiCharacter → PairedInvariantParameters → Prop}
    {sigma W padding A lower upper U E : ℝ} {hE : 1 ≤ E}
    {childOrder : ℕ} {parent : Node K omegaCharacter psiCharacter}
    (hQ : Q parent.data (pairedInvariantParameters parent.parameters))
    (hpreserved : FixedLineParameterPreserved Q)
    (htransfer : ReflectionPrimitiveTransfer primitive sigma W padding A lower upper
      U E hE childOrder parent) :
    ReflectionPrimitiveTransfer (withParameterPrimitive Q primitive)
      sigma W padding A lower upper U E hE childOrder parent := by
  intro x hunit harithmetic hearlier
  exact ⟨hpreserved parent (reflectionLongFirst parent.parameters)
    U E hE childOrder x hQ, htransfer x hunit harithmetic hearlier⟩

end HeckeSkeleton.Moments.EngineInduction
