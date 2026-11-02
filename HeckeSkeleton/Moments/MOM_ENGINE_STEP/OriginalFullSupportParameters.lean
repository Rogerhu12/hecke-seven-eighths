import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalJointFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

set_option linter.unusedSectionVars false

/-!
# Repartition the original width using the actual full support length

Only the two coordinates `m` and `q` are repartitioned. Their sum, the
two plain lengths, the slot length, the inverse length and kappa are
unchanged. Consequently the actual paired rows, whole centered moment
and strict engine domain are exactly the original ones.

The original moving recipe supplies its actual effective full support.
Its literal logarithmic norm is nonnegative and pays the entire displayed
support. The complete joint budget retains the original total width.
The existing full-support first radius has inverse exponent precisely
the new `m`; no old scale window is relabelled without proof.

The final transport changes only the parent parameter label of a proved
engine conclusion. Both chosen children, every kernel, all four terminal
values and their proved estimates are retained without alteration.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open MeasureTheory

/-- The original total width is preserved exactly. -/
def withSupportLength (a : RealParameters) (supportLength : ℝ) : RealParameters :=
  { a with m := a.m + a.q - supportLength, q := supportLength }

@[simp] theorem withSupportLength_m (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).m = a.m + a.q - supportLength := rfl

@[simp] theorem withSupportLength_q (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).q = supportLength := rfl

@[simp] theorem withSupportLength_r (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).r = a.r := rfl

@[simp] theorem withSupportLength_z (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).z = a.z := rfl

@[simp] theorem withSupportLength_n₁ (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).n₁ = a.n₁ := rfl

@[simp] theorem withSupportLength_n₂ (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).n₂ = a.n₂ := rfl

@[simp] theorem withSupportLength_kappa (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).κ = a.κ := rfl

@[simp] theorem withSupportLength_width (a : RealParameters) (supportLength : ℝ) :
    (withSupportLength a supportLength).m + (withSupportLength a supportLength).q =
      a.m + a.q := by
  sorry

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

@[simp] theorem pairedRows_withSupportLength
    (d : MomentData K ω ψ) (a : RealParameters) (supportLength Z : ℝ) :
    pairedRows d (withSupportLength a supportLength) Z = pairedRows d a Z := by
  sorry

@[simp] theorem pairedEnergy_withSupportLength
    (d : MomentData K ω ψ) (a : RealParameters) (supportLength Z t : ℝ) :
    pairedEnergy d (withSupportLength a supportLength) Z t = pairedEnergy d a Z t := by
  sorry

@[simp] theorem pairedStageEnergy_withSupportLength
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (supportLength Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered d (withSupportLength a supportLength) Z t Y₁ Y₂ =
      pairedStageEnergy centered d a Z t Y₁ Y₂ := by
  sorry

@[simp] theorem normalizedPairedEnergy_withSupportLength
    (d : MomentData K ω ψ) (a : RealParameters) (supportLength Z t : ℝ) :
    normalizedPairedEnergy d (withSupportLength a supportLength) Z t =
      normalizedPairedEnergy d a Z t := by
  sorry

namespace PairedEngineDomain

variable {centered : Bool} {d : MomentData K ω ψ} {a b : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}

/-- The paired domain uses exactly these unchanged parent coordinates.
In particular its full kappa interval remains `3/4 ≤ κ ≤ 1`. -/
theorem of_parent_parameters
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hwidth : b.m + b.q = a.m + a.q)
    (hleft : b.n₁ = a.n₁) (hright : b.n₂ = a.n₂)
    (hlength : b.z = a.z) (hkappa : b.κ = a.κ) :
    PairedEngineDomain centered d b Z Y₁ Y₂ floor padding := by
  sorry

theorem withSupportLength
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) (supportLength : ℝ) :
    PairedEngineDomain centered d
      (HeckeSkeleton.Moments.EngineStep.withSupportLength a supportLength)
      Z Y₁ Y₂ floor padding := by
  sorry

theorem withSupportLength_iff (supportLength : ℝ) :
    PairedEngineDomain centered d
      (HeckeSkeleton.Moments.EngineStep.withSupportLength a supportLength)
      Z Y₁ Y₂ floor padding ↔
        PairedEngineDomain centered d a Z Y₁ Y₂ floor padding := by
  sorry

end PairedEngineDomain

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The literal norm length of every effective additional deletion,
including the normalized original remaining support. -/
def fullSupportLength (Z : ℝ) : ℝ :=
  idealLogLength Z (Q.moving.effectiveFullSupport Q.remaining).val

def fullSupportParameters (a : RealParameters) (Z : ℝ) : RealParameters :=
  withSupportLength a (Q.fullSupportLength Z)

theorem fullSupportLength_nonneg (Z : ℝ) (hZ : 1 < Z) : 0 ≤ Q.fullSupportLength Z := by
  sorry

theorem rpow_fullSupportLength (Z : ℝ) (hZ : 1 < Z) :
    Z ^ Q.fullSupportLength Z = A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) := by
  sorry

@[simp] theorem fullSupportParameters_m (a : RealParameters) (Z : ℝ) :
    (Q.fullSupportParameters a Z).m = a.m + a.q - Q.fullSupportLength Z := rfl

@[simp] theorem fullSupportParameters_q (a : RealParameters) (Z : ℝ) :
    (Q.fullSupportParameters a Z).q = Q.fullSupportLength Z := rfl

@[simp] theorem fullSupportParameters_width (a : RealParameters) (Z : ℝ) :
    (Q.fullSupportParameters a Z).m + (Q.fullSupportParameters a Z).q = a.m + a.q := by
  sorry

theorem fullSupportParameters_q_nonneg (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ (Q.fullSupportParameters a Z).q := by
  sorry

/-- The entire actual full support is paid exactly by the new `q`. -/
theorem fullSupportParameters_support_norm (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) =
      Z ^ (Q.fullSupportParameters a Z).q := by
  sorry

/-- The original displayed support is a genuine divisor of the full
support; no former displayed-support window is enlarged by assertion. -/
theorem supportBudget_fullSupportParameters (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    Q.SupportBudget Z (Q.fullSupportParameters a Z).q := by
  sorry

/-- The full joint condition uses exactly the same original total
width. This equivalence does not reverse the one-way radical reduction
of the original remaining ideal. -/
theorem fullJointBudget_fullSupportParameters_iff (a : RealParameters) (Z : ℝ) :
    Q.FullJointBudget Z
      ((Q.fullSupportParameters a Z).m + (Q.fullSupportParameters a Z).q) ↔
        Q.FullJointBudget Z (a.m + a.q) := by
  sorry

theorem exteriorRemaining_fullJointBudget_fullSupportParameters
    (a : RealParameters) (Z : ℝ) (hbudget : Q.FullJointBudget Z (a.m + a.q)) :
    Q.exteriorRemaining.FullJointBudget Z
      ((Q.fullSupportParameters a Z).m + (Q.fullSupportParameters a Z).q) := by
  sorry

/-- A real admitted original row bounds the new support length by the
original width. No nonempty-source condition is required elsewhere. -/
theorem fullSupportLength_le_width_of_allowed
    (Z width : ℝ) (hZ : 1 < Z) (hbudget : Q.FullJointBudget Z width)
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u) :
    Q.fullSupportLength Z ≤ width := by
  sorry

theorem fullSupportParameters_m_nonneg_of_pairedRow
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hbudget : Q.FullJointBudget Z (a.m + a.q)) (ξ : X)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z) :
    0 ≤ (Q.fullSupportParameters a Z).m := by
  sorry

theorem pairedRows_empty_of_fullSupportParameters_m_neg
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hbudget : Q.FullJointBudget Z (a.m + a.q))
    (hnegative : (Q.fullSupportParameters a Z).m < 0) (ξ : X) :
    pairedRows (data ξ) a Z = ∅ := by
  sorry

/-- The actual tighter first radius has exactly the repartitioned
inverse exponent. The original source chart is not reconstructed. -/
theorem fullSupportRadius_inverse_eq_parameters_m
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    (Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans hZ)).val⁻¹ =
      Z ^ (Q.fullSupportParameters a Z).m := by
  sorry

end CompleteMovingRowRecipe

namespace PairedEngineConclusion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters} {supportLength : ℝ}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Return a proved internal conclusion to the original parent
parameters. Every actual child, continuous measure and terminal value
is copied literally; only identities of the parent label are used. -/
def ofWithSupportLength
    (out : PairedEngineConclusion (Ω := Ω) centered d (withSupportLength a supportLength)
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible where
  branches := out.branches
  leftData := out.leftData
  rightData := out.rightData
  leftParameters := out.leftParameters
  rightParameters := out.rightParameters
  leftTwist := out.leftTwist
  rightTwist := out.rightTwist
  leftTwist_zero := out.leftTwist_zero
  rightTwist_zero := out.rightTwist_zero
  kernel := out.kernel
  finite_kernel := out.finite_kernel
  left_width b := by simpa only [withSupportLength_width] using out.left_width b
  right_width b := by simpa only [withSupportLength_width] using out.right_width b
  left_width_nonneg := out.left_width_nonneg
  right_width_nonneg := out.right_width_nonneg
  left_plain_left_nonneg := out.left_plain_left_nonneg
  left_plain_right_nonneg := out.left_plain_right_nonneg
  right_plain_left_nonneg := out.right_plain_left_nonneg
  right_plain_right_nonneg := out.right_plain_right_nonneg
  left_length := out.left_length
  right_length := out.right_length
  left_kappa := out.left_kappa
  right_kappa := out.right_kappa
  left_slots := out.left_slots
  right_slots := out.right_slots
  left_theta := out.left_theta
  right_theta := out.right_theta
  left_slot_characters := out.left_slot_characters
  right_slot_characters := out.right_slot_characters
  left_admissible := out.left_admissible
  right_admissible := out.right_admissible
  left_capacity := out.left_capacity
  right_capacity := out.right_capacity
  firstZero := out.firstZero
  secondZero := out.secondZero
  exceptional := out.exceptional
  tail := out.tail
  firstZero_nonneg := out.firstZero_nonneg
  secondZero_nonneg := out.secondZero_nonneg
  exceptional_nonneg := out.exceptional_nonneg
  tail_nonneg := out.tail_nonneg
  terminals := out.terminals
  left_integrable := out.left_integrable
  right_integrable := out.right_integrable
  cauchy_integrable := out.cauchy_integrable
  parent := by simpa only [pairedStageEnergy_withSupportLength, withSupportLength_width] using out.parent
  mass := out.mass

variable (out : PairedEngineConclusion (Ω := Ω) centered d (withSupportLength a supportLength)
  Z t Y₁ Y₂ σ ε terminalExponent C control admissible)

@[simp] theorem ofWithSupportLength_leftData : out.ofWithSupportLength.leftData = out.leftData := rfl

@[simp] theorem ofWithSupportLength_rightData : out.ofWithSupportLength.rightData = out.rightData := rfl

@[simp] theorem ofWithSupportLength_kernel : out.ofWithSupportLength.kernel = out.kernel := rfl

end PairedEngineConclusion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedRows_withSupportLength
#print axioms HeckeSkeleton.Moments.EngineStep.pairedStageEnergy_withSupportLength
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.withSupportLength_iff
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.supportBudget_fullSupportParameters
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullSupportParameters_m_nonneg_of_pairedRow
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullSupportRadius_inverse_eq_parameters_m
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofWithSupportLength
