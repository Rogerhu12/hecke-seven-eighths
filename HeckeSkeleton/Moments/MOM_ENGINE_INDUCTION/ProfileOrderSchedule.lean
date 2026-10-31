import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreStages
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl

/-!
# Finite backward selection of the actual Euler orders

An analytic reflection or strict engine call may need a higher parent
Euler order than the order imposed on its normalized children.  The
entire sequence is selected from the two actual order functions before
the scale, row or continuous Fourier parameter.  One never asserts that
a fixed finite-order unit ball is invariant under both operations.

The profile order attached to a node is determined by its three-stage
geometric rank, hence by its existing RealParameters.  No extra state
is inserted in the authoritative admissible predicate's signature.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify

/-- Ground-level requirements include the base and genuine terminal
decay orders. Each successor pays both actual analytic order functions. -/
def backwardProfileOrder (ground : ℕ) (engine reflection : ℕ → ℕ) : ℕ → ℕ
  | 0 => ground
  | rank + 1 =>
    let J := backwardProfileOrder ground engine reflection rank
    max J (max (engine J) (reflection J))

theorem backwardProfileOrder_succ (ground : ℕ) (engine reflection : ℕ → ℕ)
    (rank : ℕ) :
    backwardProfileOrder ground engine reflection rank ≤
      backwardProfileOrder ground engine reflection (rank + 1) :=
  le_max_left _ _

theorem backwardProfileOrder_monotone (ground : ℕ) (engine reflection : ℕ → ℕ) :
    Monotone (backwardProfileOrder ground engine reflection) :=
  monotone_nat_of_le_succ (backwardProfileOrder_succ ground engine reflection)

theorem backwardProfileOrder_ground_le (ground : ℕ) (engine reflection : ℕ → ℕ)
    (rank : ℕ) : ground ≤ backwardProfileOrder ground engine reflection rank :=
  backwardProfileOrder_monotone ground engine reflection (Nat.zero_le rank)

/-- No monotonicity assumption on either analytic order function is
needed: all children are first normalized at the predecessor order. -/
theorem backwardProfileOrder_parent_orders (ground : ℕ) (engine reflection : ℕ → ℕ)
    {rank : ℕ} (hrank : 0 < rank) :
    engine (backwardProfileOrder ground engine reflection (rank - 1)) ≤
        backwardProfileOrder ground engine reflection rank ∧
    reflection (backwardProfileOrder ground engine reflection (rank - 1)) ≤
        backwardProfileOrder ground engine reflection rank := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrank)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, backwardProfileOrder]
  exact ⟨(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem backwardProfileOrder_child_le (ground : ℕ) (engine reflection : ℕ → ℕ)
    {child parent : ℕ} (h : child < parent) :
    backwardProfileOrder ground engine reflection child ≤
      backwardProfileOrder ground engine reflection (parent - 1) :=
  backwardProfileOrder_monotone ground engine reflection (by omega)

/-- The exact geometric rank depends only on the actual seven numerical
parameters. The centered/comparison pair has the same total length. -/
def parameterCoreRank (sigma widthLimit padding : ℝ) (a : RealParameters) : ℕ :=
  (if a.z = 0 then 0 else 3 * (widthBand sigma widthLimit + 1)) +
    3 * widthBand sigma (a.m + a.q) +
      if a.m + a.q + padding < a.n₁ + a.n₂ + a.z then 2
      else if a.n₁ + a.n₂ + a.z ≤ 5 * (a.m + a.q) / 6 then 0 else 1

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

theorem PolynomialSystem.core_rank_parameters {sigma widthLimit : ℝ}
    (S : PolynomialSystem K omegaCharacter psiCharacter sigma widthLimit)
    (padding : ℝ) (x : S.Label) :
    ((S.withCoreStages padding).schedule x).rank =
      parameterCoreRank sigma widthLimit padding (S.node x).parameters := by
  unfold PolynomialSystem.schedule PolynomialSystem.withCoreStages State.rank
    parameterCoreRank Node.coreStage Node.lengthStage Node.totalLength Node.width boundedBand
  split_ifs <;> simp_all <;> split_ifs <;> simp_all <;> linarith

/-- The one preselected maximal order covers every actual node, including
strict-step zero-slot children outside the padded core. -/
theorem PolynomialSystem.core_profile_order_le {sigma widthLimit : ℝ}
    (S : PolynomialSystem K omegaCharacter psiCharacter sigma widthLimit)
    (padding : ℝ) (ground : ℕ) (engine reflection : ℕ → ℕ) (x : S.Label) :
    backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding (S.node x).parameters) ≤
      backwardProfileOrder ground engine reflection (6 * (widthBand sigma widthLimit + 1)) := by
  rw [← S.core_rank_parameters padding x]
  exact backwardProfileOrder_monotone ground engine reflection
    ((S.withCoreStages padding).schedule x).rank_lt_bound.le

/-- Weakening the actual finite Euler order preserves every profile,
annulus and common constant, including the prime-window slices. -/
theorem modelProfileControl_mono_order
    {d : MomentData K omegaCharacter psiCharacter}
    {J L : ℕ} {A C H lower upper T : ℝ}
    (h : ModelProfileControl d L A C H lower upper T) (hJL : J ≤ L) :
    ModelProfileControl d J A C H lower upper T := by
  intro q
  obtain ⟨hsmooth, hsupport, hbound⟩ := h q
  exact ⟨hsmooth, hsupport,
    (testSeminorm_mono_order _ A hJL).trans hbound⟩

/-- A child normalized at the parent's predecessor order automatically
lies in its own rank's true unit ball. -/
theorem normalized_child_rank_profile_control
    {d : MomentData K omegaCharacter psiCharacter}
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {child parent : ℕ} (hearlier : child < parent) {A lower upper : ℝ}
    (h : ModelProfileControl d
      (backwardProfileOrder ground engine reflection (parent - 1)) A 1 0 lower upper 0) :
    ModelProfileControl d (backwardProfileOrder ground engine reflection child)
      A 1 0 lower upper 0 :=
  modelProfileControl_mono_order h
    (backwardProfileOrder_child_le ground engine reflection hearlier)

end HeckeSkeleton.Moments.EngineInduction
