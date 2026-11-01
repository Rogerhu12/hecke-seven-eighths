import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinStrictTransfer
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreRecursion

/-!
# A literal Mellin strict step with its genuine labelled children

The normalization envelope and outer kernel constant are selected from
the proved Mellin preprocessing theorem. They do not depend on the
parent profile budget, moving node, scale, or engine output. Only the
actual canonical output at each fixed outer frequency is supplied by
the strict producer. Its ordinary children have genuine labels in the
original induction family.

The pure coefficient budget pays the exact Mellin mass. It is not a
parent or child energy bound. The bound below applies the induction
hypothesis only to the strict output's smaller children, then invokes
the proved scalar Mellin transfer. No joint kernel or measurable bind
of frequency-dependent engine kernels is constructed or assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type u} [MeasurableSpace Ω]

private def mellin_strict_exists (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :=
  exists_centeredMellin_strict_transfer
    (K := K) (omegaCharacter := ω) (psiCharacter := ψ) (Ω := Ω)
    cap J A a b hA ha hab

/-- The actual envelope selected by the existing preprocessing proof. -/
def mellinStrictEnvelope (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) : ℝ :=
  (mellin_strict_exists (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
    cap J A a b hA ha hab).choose

theorem mellinStrictEnvelope_one_le (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    1 ≤ mellinStrictEnvelope (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
      cap J A a b hA ha hab :=
  (mellin_strict_exists (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
    cap J A a b hA ha hab).choose_spec.choose

/-- This fixed constant is selected before the moving profile budget. -/
def mellinStrictMassConstant (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) : ℝ :=
  (mellin_strict_exists (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
    cap J A a b hA ha hab).choose_spec.choose_spec.choose

theorem mellinStrictMassConstant_nonneg (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
      cap J A a b hA ha hab :=
  (mellin_strict_exists (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
    cap J A a b hA ha hab).choose_spec.choose_spec.choose_spec.1

/-- A fixed actual intermediate model. Its parameters and width are
the parent's; it is not itself an earlier recursive call. -/
def Node.mellinStrictModel (n : Node K ω ψ) (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) : Node K ω ψ :=
  (n.freezeTime 0).normalizedMellinPlain
    (annularPlateau a b ha hab) (annularPlateau a b ha hab)
    (2 * P) (by linarith)
    (mellinStrictEnvelope (K := K) (ω := ω) (ψ := ψ) (Ω := Ω) cap J A a b hA ha hab)
    (mellinStrictEnvelope_one_le (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
      cap J A a b hA ha hab) J frequency

/-- The selected constants carry the exact theorem which constructed
them; there is no additional analytic premise on the parent energy. -/
theorem mellinStrictTransfer_chosen (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P) (n : Node K ω ψ) (U : ℝ) (hU : 0 < U)
    (hcap : n.data.geometry.slotCount ≤ cap)
    (hprofile : ModelProfileControl n.data (J + 2) A P 0 a b 0) :
    (∀ frequency : ℝ × ℝ,
      ProfileTimeIndependent
        (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).data ∧
      ModelProfileControl
        (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).data
        J A 1 0 (a / 2) (2 * b) 0) ∧
    ∀ sigma delta beta C control D : ℝ, 0 ≤ D →
    ∀ admissible : (ℝ × ℝ) → MomentData K ω ψ → RealParameters → Prop,
    ∀ outputs : ∀ frequency : ℝ × ℝ,
      (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).EngineOutput
        (Ω := Ω) U sigma delta beta C control (admissible frequency),
    (∀ frequency branch parameter,
      (Node.ordinary ((outputs frequency).leftData branch parameter)
        ((outputs frequency).leftParameters branch)).normalizedEnergy U 0 ≤ D) →
    (∀ frequency branch parameter,
      (Node.ordinary ((outputs frequency).rightData branch parameter)
        ((outputs frequency).rightParameters branch)).normalizedEnergy U 0 ≤ D) →
    n.normalizedEnergy U 0 ≤
      mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
        cap J A a b hA ha hab * P ^ (2 * (cap + 2)) *
          (C * control * (U ^ beta + U ^ delta * D)) := by
  exact (mellin_strict_exists (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
    cap J A a b hA ha hab).choose_spec.choose_spec.choose_spec.2
      P hP n U hU hcap hprofile

variable {sigma widthLimit : ℝ}

/-- The public strict output for a literal intermediate node, with
labels only for its actual ordinary children. The intermediate need
not have a label or belong to the recursive admissible subtype. -/
structure LabeledEngineOutput
    (S : PolynomialSystem.{u} K ω ψ sigma widthLimit) (n : Node K ω ψ)
    (U delta beta C control : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop) where
  output : n.EngineOutput (Ω := Ω) U sigma delta beta C control admissible
  left : Fin output.branches → Ω → S.Label
  right : Fin output.branches → Ω → S.Label
  left_eq : ∀ branch parameter, S.node (left branch parameter) =
    Node.ordinary (output.leftData branch parameter) (output.leftParameters branch)
  right_eq : ∀ branch parameter, S.node (right branch parameter) =
    Node.ordinary (output.rightData branch parameter) (output.rightParameters branch)

/-- Only the canonical width and zero-slot conclusions are used to
prove these genuine child labels earlier than the original parent. -/
theorem LabeledEngineOutput.children_earlier
    {S : PolynomialSystem.{u} K ω ψ sigma widthLimit} {n : Node K ω ψ}
    {U delta beta C control : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (branch : LabeledEngineOutput (Ω := Ω) S n U delta beta C control admissible)
    (padding : ℝ) (x : S.Label)
    (hparameters : n.parameters = (S.node x).parameters)
    (hlength : n.parameters.z = n.data.geometry.totalLength)
    (b : Fin branch.output.branches) (parameter : Ω) :
    ((S.withCoreStages padding).schedule (branch.left b parameter)).Earlier
        ((S.withCoreStages padding).schedule x) ∧
      ((S.withCoreStages padding).schedule (branch.right b parameter)).Earlier
        ((S.withCoreStages padding).schedule x) := by
  have hwidth : n.parameters.m + n.parameters.q =
      (S.node x).parameters.m + (S.node x).parameters.q :=
    congrArg (fun a : RealParameters => a.m + a.q) hparameters
  constructor
  · apply (S.withCoreStages padding).earlier_of_width_drop (branch.left b parameter) x
    · change (S.node (branch.left b parameter)).width + sigma / 2 ≤ (S.node x).width
      rw [branch.left_eq]
      have hdrop := branch.output.left_width b
      change (branch.output.leftParameters b).m + (branch.output.leftParameters b).q +
        sigma / 2 ≤ (S.node x).parameters.m + (S.node x).parameters.q
      linarith
    · change (S.node x).parameters.z = 0 → (S.node (branch.left b parameter)).parameters.z = 0
      intro hzero
      rw [branch.left_eq]
      exact (engineOutput_zero_parameters branch.output hlength
        (by rw [hparameters]; exact hzero) b parameter).1
  · apply (S.withCoreStages padding).earlier_of_width_drop (branch.right b parameter) x
    · change (S.node (branch.right b parameter)).width + sigma / 2 ≤ (S.node x).width
      rw [branch.right_eq]
      have hdrop := branch.output.right_width b
      change (branch.output.rightParameters b).m + (branch.output.rightParameters b).q +
        sigma / 2 ≤ (S.node x).parameters.m + (S.node x).parameters.q
      linarith
    · change (S.node x).parameters.z = 0 → (S.node (branch.right b parameter)).parameters.z = 0
      intro hzero
      rw [branch.right_eq]
      exact (engineOutput_zero_parameters branch.output hlength
        (by rw [hparameters]; exact hzero) b parameter).2

/-- Primitive input to one legal strict call. The only estimate field
is a scalar coefficient/profile budget. Actual parent profiles and
canonical outputs, rather than their desired energy consequence, are
the remaining inputs. -/
structure MellinStrictBranchAt
    (S : PolynomialSystem.{u} K ω ψ sigma widthLimit) (x : S.Label)
    (U T C H beta delta : ℝ)
    (admissible : MomentData K ω ψ → RealParameters → Prop) where
  cap : ℕ
  order : ℕ
  weight : ℝ
  lower : ℝ
  upper : ℝ
  weight_nonneg : 0 ≤ weight
  lower_pos : 0 < lower
  interval : lower ≤ upper
  profileBudget : ℝ
  profileBudget_one_le : 1 ≤ profileBudget
  slot_cap : (S.node x).data.geometry.slotCount ≤ cap
  profiles : ModelProfileControl (S.node x).data (order + 2) weight profileBudget 0 lower upper 0
  engineCoefficient : ℝ
  engineControl : ℝ
  outputs : ∀ frequency : ℝ × ℝ,
    LabeledEngineOutput (Ω := Ω) S
      ((S.node x).mellinStrictModel (Ω := Ω) cap order weight lower upper
        weight_nonneg lower_pos interval profileBudget profileBudget_one_le frequency)
      U delta beta engineCoefficient engineControl admissible
  budget : mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
      cap order weight lower upper weight_nonneg lower_pos interval *
        profileBudget ^ (2 * (cap + 2)) * (engineCoefficient * engineControl) ≤
      C * (1 + T) ^ H

/-- Consume each strict output at fixed outer frequency before the
outer Mellin integral. The same-rank intermediate is never an IH call. -/
theorem MellinStrictBranchAt.bound
    {S : PolynomialSystem.{u} K ω ψ sigma widthLimit} {x : S.Label}
    {U T C H beta delta padding : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (branch : MellinStrictBranchAt (Ω := Ω) S x U T C H beta delta admissible)
    (hU : 0 < U) (hlength : (S.node x).parameters.z = (S.node x).data.geometry.totalLength)
    (D : ℝ) (hD : 0 ≤ D)
    (hchildren : ∀ y, ((S.withCoreStages padding).schedule y).Earlier
      ((S.withCoreStages padding).schedule x) → (S.node y).normalizedEnergy U 0 ≤ D) :
    (S.node x).normalizedEnergy U 0 ≤
      C * (1 + T) ^ H * U ^ beta + C * (1 + T) ^ H * U ^ delta * D := by
  have hearlier (frequency : ℝ × ℝ) (b : Fin (branch.outputs frequency).output.branches)
      (parameter : Ω) :=
    (branch.outputs frequency).children_earlier padding x rfl
      (show ((S.node x).mellinStrictModel (Ω := Ω) branch.cap branch.order branch.weight
        branch.lower branch.upper branch.weight_nonneg branch.lower_pos branch.interval
        branch.profileBudget branch.profileBudget_one_le frequency).parameters.z =
        ((S.node x).mellinStrictModel (Ω := Ω) branch.cap branch.order branch.weight
          branch.lower branch.upper branch.weight_nonneg branch.lower_pos branch.interval
          branch.profileBudget branch.profileBudget_one_le frequency).data.geometry.totalLength
        from hlength) b parameter
  have hleft (frequency : ℝ × ℝ) (b : Fin (branch.outputs frequency).output.branches)
      (parameter : Ω) :
      (Node.ordinary ((branch.outputs frequency).output.leftData b parameter)
        ((branch.outputs frequency).output.leftParameters b)).normalizedEnergy U 0 ≤ D := by
    have h := hchildren ((branch.outputs frequency).left b parameter)
      (hearlier frequency b parameter).1
    simpa only [(branch.outputs frequency).left_eq] using h
  have hright (frequency : ℝ × ℝ) (b : Fin (branch.outputs frequency).output.branches)
      (parameter : Ω) :
      (Node.ordinary ((branch.outputs frequency).output.rightData b parameter)
        ((branch.outputs frequency).output.rightParameters b)).normalizedEnergy U 0 ≤ D := by
    have h := hchildren ((branch.outputs frequency).right b parameter)
      (hearlier frequency b parameter).2
    simpa only [(branch.outputs frequency).right_eq] using h
  have hscalar := (mellinStrictTransfer_chosen (Ω := Ω)
    branch.cap branch.order branch.weight branch.lower branch.upper
    branch.weight_nonneg branch.lower_pos branch.interval
    branch.profileBudget branch.profileBudget_one_le (S.node x) U hU branch.slot_cap
    branch.profiles).2 sigma delta beta branch.engineCoefficient branch.engineControl D hD
      (fun _ => admissible) (fun frequency => (branch.outputs frequency).output) hleft hright
  have hfactor : 0 ≤ U ^ beta + U ^ delta * D :=
    add_nonneg (Real.rpow_nonneg hU.le beta) (mul_nonneg (Real.rpow_nonneg hU.le delta) hD)
  calc
    (S.node x).normalizedEnergy U 0 ≤
        mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
          branch.cap branch.order branch.weight branch.lower branch.upper
          branch.weight_nonneg branch.lower_pos branch.interval *
          branch.profileBudget ^ (2 * (branch.cap + 2)) *
            (branch.engineCoefficient * branch.engineControl * (U ^ beta + U ^ delta * D)) := hscalar
    _ = (mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
          branch.cap branch.order branch.weight branch.lower branch.upper
          branch.weight_nonneg branch.lower_pos branch.interval *
          branch.profileBudget ^ (2 * (branch.cap + 2)) *
            (branch.engineCoefficient * branch.engineControl)) * (U ^ beta + U ^ delta * D) := by ring
    _ ≤ (C * (1 + T) ^ H) * (U ^ beta + U ^ delta * D) :=
      mul_le_mul_of_nonneg_right branch.budget hfactor
    _ = C * (1 + T) ^ H * U ^ beta + C * (1 + T) ^ H * U ^ delta * D := by ring

end HeckeSkeleton.Moments.EngineInduction
