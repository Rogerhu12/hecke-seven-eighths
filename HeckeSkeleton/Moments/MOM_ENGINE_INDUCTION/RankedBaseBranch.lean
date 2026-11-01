import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileSupremum

/-!
# Actual base leaves for the finite-order recursive profile family

Every node's actual rank provides the common ground order.  The one
weighted profile budget supplies weight-zero order-one control, with
the explicit factor two.  The existing ideal and prime counting proof
then constructs the literal base certificate.  Both final constants are
selected before the height, the node and its scale.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify

universe u

variable {K : Type} [Field K] [NumberField K]

/-- The ground order and the actual weighted seminorm imply precisely
the primitive profile input required by absolute base counting. -/
theorem rankedProfilePrimitive_base_profiles
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    {σ W padding A C H lower upper T : ℝ}
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
    (hground : 1 ≤ ground) (hA : 0 ≤ A)
    (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (h : admissibleOfInvariant
      (rankedProfilePrimitive ground engine reflection σ W padding A
        (profileFamilyBudget C H T) lower upper) d a) :
    ModelProfileControl d 1 0 (2 * (1 + C)) H lower upper T := by
  have hg := rankedProfilePrimitive_ground ground engine reflection h
  have ho := modelProfileControl_mono_order hg hground
  have hw := modelProfileControl_weight_zero ho hA hlower hinterval
  intro q
  refine ⟨(hw q).1, (hw q).2.1, ?_⟩
  simpa only [profileFamilyBudget, Real.rpow_zero, mul_one, mul_assoc] using (hw q).2.2

/-- Uniform base certificates for the same literal root/child family.
The only local inequality in the hypotheses is the base-domain length
condition. No parent or child energy estimate is an input. -/
theorem uniform_ranked_profile_base_components (cap ground : ℕ)
    (engine reflection : ℕ → ℕ) (σ W padding A C H lower upper floor boundary : ℝ)
    (hground : 1 ≤ ground) (hA : 0 ≤ A) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ D heightDegree : ℝ,
      D = generalBaseConstant K cap upper (2 * (1 + C)) (2 * (1 + C)) (2 * (1 + C)) ∧
      heightDegree = baseHeightDegree cap H H H ∧ 0 ≤ D ∧ 0 ≤ heightDegree ∧
      ∀ T : ℝ, 0 ≤ T → ∀ {ω ψ : HeckeCharacter K} (n : Node K ω ψ) (U : ℝ),
      1 ≤ U → n.data.geometry.slotCount ≤ cap →
      admissibleOfInvariant
        (rankedProfilePrimitive ground engine reflection σ W padding A
          (profileFamilyBudget C H T) lower upper) n.data n.parameters →
      n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤
        floor + padding + floor / 6 →
      Nonempty (TerminalComponents.{u} (n.normalizedEnergy U 0) U T D heightDegree
        floor padding σ boundary) := by
  obtain ⟨D, heightDegree, hD, hdegree, hDn, hdegreen, hbase⟩ :=
    uniform_modelProfileControl_base_components.{u} (K := K) cap
      (2 * (1 + C)) H lower upper floor padding σ boundary
      (by positivity) hH hlower hinterval
  refine ⟨D, heightDegree, hD, hdegree, hDn, hdegreen, ?_⟩
  intro T hT ω ψ n U hU hcount hprofile hlength
  exact hbase T hT n U hU hcount
    (rankedProfilePrimitive_base_profiles ground engine reflection
      hground hA hlower hinterval hprofile) hlength

end HeckeSkeleton.Moments.EngineInduction
