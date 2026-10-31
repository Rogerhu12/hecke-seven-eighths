import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentMoment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The complete public output of a paired engine step

This is the output type to be constructed from the two actual source
transformations. In particular, it is not a hypothesis standing in for
those transformations. The parent and every child are the literal
`MomentData` energies. The two children share one positive kernel on the
entire continuous parameter space, and each branch's parameters are fixed
before that parameter. Both true zero terms, the exceptional term, and
the truncation tail remain separately visible.

An induction consumer may assume the engine's theorem producing this
output. The construction of that theorem belongs to MOM_ENGINE_STEP.
The helper below proves the exact AM--GM conversion needed by a positive
measure recursion, without estimating any child moment.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def normalizedPairedEnergy (d : MomentData K ω ψ) (a : RealParameters) (Z t : ℝ) : ℝ :=
  pairedEnergy d a Z t / Z ^ (a.m + a.q)

theorem normalizedPairedEnergy_nonneg (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) (hZ : 0 < Z) :
    0 ≤ normalizedPairedEnergy d a Z t :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Real.rpow_pos_of_pos hZ _).le

/-- A complete engine conclusion. The constants and original-profile
control are parameters chosen by the provider before the moving data.
The `parent` and `mass` fields are conclusions the provider must prove,
not primitive calibration fields it may request. -/
structure PairedEngineConclusion {Ω : Type*} [MeasurableSpace Ω]
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ) where
  branches : ℕ
  leftData : Fin branches → Ω → MomentData K ω ψ
  rightData : Fin branches → Ω → MomentData K ω ψ
  leftParameters : Fin branches → RealParameters
  rightParameters : Fin branches → RealParameters
  leftTwist : Fin branches → Ω → ℝ
  rightTwist : Fin branches → Ω → ℝ
  kernel : Fin branches → Measure Ω
  finite_kernel : ∀ b, IsFiniteMeasure (kernel b)
  left_width : ∀ b, (leftParameters b).m + (leftParameters b).q ≤ a.m + a.q - σ / 2
  right_width : ∀ b, (rightParameters b).m + (rightParameters b).q ≤ a.m + a.q - σ / 2
  left_capacity : ∀ b, (leftParameters b).z = 0 ∨
    (leftParameters b).n₁ + (leftParameters b).n₂ +
      6 * (leftParameters b).κ * (leftParameters b).z ≤
        (leftParameters b).m + (leftParameters b).q
  right_capacity : ∀ b, (rightParameters b).z = 0 ∨
    (rightParameters b).n₁ + (rightParameters b).n₂ +
      6 * (rightParameters b).κ * (rightParameters b).z ≤
        (rightParameters b).m + (rightParameters b).q
  firstZero : ℝ
  secondZero : ℝ
  exceptional : ℝ
  tail : ℝ
  firstZero_nonneg : 0 ≤ firstZero
  secondZero_nonneg : 0 ≤ secondZero
  exceptional_nonneg : 0 ≤ exceptional
  tail_nonneg : 0 ≤ tail
  terminals : firstZero + secondZero + exceptional + tail ≤
    C * control * Z ^ terminalExponent
  left_integrable : ∀ b, Integrable (fun ξ =>
    normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) (kernel b)
  right_integrable : ∀ b, Integrable (fun ξ =>
    normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ)) (kernel b)
  cauchy_integrable : ∀ b, Integrable (fun ξ =>
    Real.sqrt (normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) *
      Real.sqrt (normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ)))
        (kernel b)
  parent : pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
    firstZero + secondZero + exceptional + tail +
      ∑ b, ∫ ξ,
        Real.sqrt (normalizedPairedEnergy (leftData b ξ) (leftParameters b) Z (leftTwist b ξ)) *
          Real.sqrt (normalizedPairedEnergy (rightData b ξ) (rightParameters b) Z (rightTwist b ξ))
            ∂kernel b
  mass : (∑ b, (kernel b).real Set.univ) ≤ C * control * Z ^ ε

namespace PairedEngineConclusion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}

/-- The complete output gives the positive, normalized recursion directly.
The same kernel is retained for both children and the terminal budget is
paid once. No final estimate for either child is used. -/
theorem linearized
    (out : PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control) (hZ : 0 < Z) :
    pairedStageEnergy centered d a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      C * control * Z ^ terminalExponent +
        ∑ b, ((∫ ξ, normalizedPairedEnergy
          (out.leftData b ξ) (out.leftParameters b) Z (out.leftTwist b ξ) ∂out.kernel b) +
          ∫ ξ, normalizedPairedEnergy
            (out.rightData b ξ) (out.rightParameters b) Z (out.rightTwist b ξ) ∂out.kernel b) / 2 := by
  apply out.parent.trans
  apply add_le_add out.terminals
  apply Finset.sum_le_sum
  intro b _
  have hpoint (ξ : Ω) :
      Real.sqrt (normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) Z
        (out.leftTwist b ξ)) *
      Real.sqrt (normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) Z
        (out.rightTwist b ξ)) ≤
      (normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) Z (out.leftTwist b ξ) +
        normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) Z (out.rightTwist b ξ)) / 2 := by
    have hleft := normalizedPairedEnergy_nonneg (out.leftData b ξ) (out.leftParameters b)
      Z (out.leftTwist b ξ) hZ
    have hright := normalizedPairedEnergy_nonneg (out.rightData b ξ) (out.rightParameters b)
      Z (out.rightTwist b ξ) hZ
    nlinarith [sq_nonneg
      (Real.sqrt (normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) Z
        (out.leftTwist b ξ)) -
       Real.sqrt (normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) Z
        (out.rightTwist b ξ))), Real.sq_sqrt hleft, Real.sq_sqrt hright]
  have hi := integral_mono (out.cauchy_integrable b)
    (((out.left_integrable b).add (out.right_integrable b)).div_const 2) hpoint
  rw [integral_div] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add (out.left_integrable b) (out.right_integrable b)] at hi
  exact hi

theorem strict_width
    (out : PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control) (hσ : 0 < σ) (b : Fin out.branches) :
    (out.leftParameters b).m + (out.leftParameters b).q < a.m + a.q ∧
      (out.rightParameters b).m + (out.rightParameters b).q < a.m + a.q := by
  constructor <;> linarith [out.left_width b, out.right_width b]

end PairedEngineConclusion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.linearized
