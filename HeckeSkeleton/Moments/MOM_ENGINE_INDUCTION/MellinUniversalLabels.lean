import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinScalarStep
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalNodeFamily

/-!
# Genuine strict children of an unlabelled Mellin intermediate

The same-rank Mellin intermediate is only an input to the actual strict
producer. It need not be a member of the recursive node subtype. Its
published ordinary children acquire labels from their own geometry and
primitive admissibility, and only those labels are used by induction.

The optional admissibility conversion below retains every numerical
field, both actual child data, all four terminal pieces and the original
positive kernels. Its premises concern only those actual children's
primitive calibration, never their moment estimates.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeSkeleton.Moments.UniformAmplify

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Replace only the proved primitive predicates on the very same
children. In particular, this operation does not construct an engine
output from a parent estimate or change any of its kernels. -/
def recalibrateEngineOutput {n : Node K ω ψ} {U sigma delta beta C control : ℝ}
    {oldAdmissible newAdmissible : MomentData K ω ψ → RealParameters → Prop}
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta C control oldAdmissible)
    (hleft : ∀ b frequency, newAdmissible (out.leftData b frequency) (out.leftParameters b))
    (hright : ∀ b frequency, newAdmissible (out.rightData b frequency) (out.rightParameters b)) :
    n.EngineOutput (Ω := Ω) U sigma delta beta C control newAdmissible where
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
  left_width := out.left_width
  right_width := out.right_width
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
  left_admissible := hleft
  right_admissible := hright
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
  parent := out.parent
  mass := out.mass

/-- Only the intermediate's numerical geometry is needed. In
particular, it has no recursive family-membership premise. -/
def universalLabeledEngineOutput
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (sigma W padding : ℝ) (cap : ℕ) (hsigma : 0 < sigma)
    (n : Node K ω ψ) (U delta beta C control : ℝ)
    (hkappaLower : 3 / 4 ≤ n.parameters.κ) (hkappaUpper : n.parameters.κ ≤ 1)
    (hwidth : n.width ≤ W) (hslots : n.data.geometry.slotCount ≤ cap)
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta C control
      (admissibleOfInvariant primitive)) :
    LabeledEngineOutput (Ω := Ω)
      (universalPolynomialSystem.{u} primitive sigma W padding cap hsigma)
      n U delta beta C control (admissibleOfInvariant primitive) := by
  let left (b : Fin out.branches) (frequency : Ω) :
      UniversalNode primitive W padding cap :=
    UniversalNode.ordinary primitive W padding cap
      (out.leftData b frequency) (out.leftParameters b)
      (out.left_length b frequency) (out.left_plain_left_nonneg b) (out.left_plain_right_nonneg b)
      (by rw [out.left_kappa]; exact hkappaLower)
      (by rw [out.left_kappa]; exact hkappaUpper)
      (out.left_capacity b) (out.left_width_nonneg b)
      (by have hdrop := out.left_width b; change n.parameters.m + n.parameters.q ≤ W at hwidth; linarith)
      ((out.left_slots b frequency).trans hslots) (out.left_admissible b frequency)
  let right (b : Fin out.branches) (frequency : Ω) :
      UniversalNode primitive W padding cap :=
    UniversalNode.ordinary primitive W padding cap
      (out.rightData b frequency) (out.rightParameters b)
      (out.right_length b frequency) (out.right_plain_left_nonneg b) (out.right_plain_right_nonneg b)
      (by rw [out.right_kappa]; exact hkappaLower)
      (by rw [out.right_kappa]; exact hkappaUpper)
      (out.right_capacity b) (out.right_width_nonneg b)
      (by have hdrop := out.right_width b; change n.parameters.m + n.parameters.q ≤ W at hwidth; linarith)
      ((out.right_slots b frequency).trans hslots) (out.right_admissible b frequency)
  exact {
    output := out
    left := fun b frequency => ⟨left b frequency⟩
    right := fun b frequency => ⟨right b frequency⟩
    left_eq := fun _ _ => rfl
    right_eq := fun _ _ => rfl }

/-- Supply the actual canonical outputs at the literal selected Mellin
models. Their genuine child labels are constructed, not assumed. The
only estimate premise is the explicit scalar coefficient budget which
pays the already proved outer Mellin mass. -/
def universalMellinStrictBranch
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (sigma W padding : ℝ) (cap : ℕ) (hsigma : 0 < sigma)
    (x : (universalPolynomialSystem.{u} primitive sigma W padding cap hsigma).Label)
    (U T C H beta delta : ℝ)
    (J : ℕ) (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P)
    (hprofile : ModelProfileControl x.down.val.data (J + 2) A P 0 a b 0)
    (engineCoefficient engineControl : ℝ)
    (outputs : ∀ frequency : ℝ × ℝ,
      (x.down.val.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).EngineOutput
        (Ω := Ω) U sigma delta beta engineCoefficient engineControl
          (admissibleOfInvariant primitive))
    (hbudget : mellinStrictMassConstant (K := K) (ω := ω) (ψ := ψ) (Ω := Ω)
        cap J A a b hA ha hab * P ^ (2 * (cap + 2)) *
          (engineCoefficient * engineControl) ≤ C * (1 + T) ^ H) :
    MellinStrictBranchAt (Ω := Ω)
      (universalPolynomialSystem.{u} primitive sigma W padding cap hsigma) x
      U T C H beta delta (admissibleOfInvariant primitive) where
  cap := cap
  order := J
  weight := A
  lower := a
  upper := b
  weight_nonneg := hA
  lower_pos := ha
  interval := hab
  profileBudget := P
  profileBudget_one_le := hP
  slot_cap := x.down.property.slot_count
  profiles := hprofile
  engineCoefficient := engineCoefficient
  engineControl := engineControl
  outputs frequency := universalLabeledEngineOutput primitive sigma W padding cap hsigma
    (x.down.val.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency)
    U delta beta engineCoefficient engineControl
    x.down.property.kappa_lower x.down.property.kappa_upper
    x.down.property.width_le x.down.property.slot_count (outputs frequency)
  budget := hbudget

end HeckeSkeleton.Moments.EngineInduction
