import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualCompleteSourceFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceReflection

/-!
# Literal strict children return to the actual recursive primitive

The canonical moving-child output supplies its own complete recipe,
two norm budgets and embedding of the retained slots. Freezing the same
child at its evaluation time preserves its energy and proves the time
independence needed for the next Mellin transform.

The only analytic premise below is the actual child's scheduled profile
control. The arithmetic calibration, canonical theta, fixed cancellation
exponent and original slot mesh are then constructed for the same child.
No recursive estimate or replacement child is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]
variable {Q : Type*} {parent d : MomentData K c.family.omega (targetCharacter K c)}
variable {a : RealParameters} {U : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- Primitive membership is reconstructed from this actual child before
the universal-node constructor assigns a recursive label. -/
theorem frozenMovingChild_recipePrimitive
    (child : EngineStep.MovingEngineChildAdmissible
      (axiomChoice K c).A (probeData K c) (momentRowCharacters K c) Q
      parent rowDomain window orders U d a)
    (htheta : d.theta = canonicalDetectorTheta K (targetCharacter K c))
    (hslots : ∀ j, d.slotCoefficient j ∈ canonicalDetectorTheta K (targetCharacter K c))
    (hprime : PrimeProfileSupport d)
    (hkappa : a.κ = 2 * c.family.B - 1)
    (hmesh : parent.geometry.fitsMesh (momentMesh K c.family).val)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma padding A Cp Hp lower upper T : ℝ)
    (hprofile : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma 2 padding A
        (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime d 0) a) :
    admissibleOfInvariant
      (recipeDataReflectionPrimitive c (canonicalDetectorTheta K (targetCharacter K c))
        (actualCompleteSourceBudgetPrimitive c) ground engine reflection sigma padding
        A Cp Hp lower upper U T)
      (freezeMomentTime d 0) a := by
  let D := frozenMovingChildCompleteSourceBudgetData child htheta hslots hprime
  exact ⟨hkappa, ⟨D⟩, child.fitsMesh hmesh, D.canonicalReflectionArithmetic, hprofile⟩

/-- The canonical conclusion retains its actual children, kernels and
terminal terms. Only the literal time-zero freeze and the now-proved
primitive membership are applied before the universal labels are built.
The source parent may be the energy-preserving finite-row localization. -/
def frozenCompleteRecipeEngineOutput {Ω : Type*} [MeasurableSpace Ω]
    (n : Node K c.family.omega (targetCharacter K c))
    (sourceParent : MomentData K c.family.omega (targetCharacter K c))
    (sigma delta beta coefficient control padding A Cp Hp lower upper T : ℝ)
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta coefficient control
      (EngineStep.MovingEngineChildAdmissible
        (axiomChoice K c).A (probeData K c) (momentRowCharacters K c) Q
        sourceParent rowDomain window orders U))
    (htheta : n.data.theta = canonicalDetectorTheta K (targetCharacter K c))
    (hkappa : n.parameters.κ = 2 * c.family.B - 1)
    (hmesh : sourceParent.geometry.fitsMesh (momentMesh K c.family).val)
    (hleftPrime : ∀ b xi, PrimeProfileSupport (out.leftData b xi))
    (hrightPrime : ∀ b xi, PrimeProfileSupport (out.rightData b xi))
    (hleftProfile : ∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma 2 padding A
        (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.leftData b xi) 0) (out.leftParameters b))
    (hrightProfile : ∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma 2 padding A
        (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.rightData b xi) 0) (out.rightParameters b)) :
    n.EngineOutput (Ω := Ω) U sigma delta beta coefficient control
      (admissibleOfInvariant
        (recipeDataReflectionPrimitive c (canonicalDetectorTheta K (targetCharacter K c))
          (actualCompleteSourceBudgetPrimitive c) ground engine reflection sigma padding
          A Cp Hp lower upper U T)) := by
  apply freezeEngineOutput out
  · intro b xi
    exact frozenMovingChild_recipePrimitive (out.left_admissible b xi)
      ((out.left_theta b xi).trans htheta)
      (fun j => htheta ▸ out.left_slot_characters b xi j)
      (hleftPrime b xi) ((out.left_kappa b).trans hkappa) hmesh
      ground engine reflection sigma padding A Cp Hp lower upper T (hleftProfile b xi)
  · intro b xi
    exact frozenMovingChild_recipePrimitive (out.right_admissible b xi)
      ((out.right_theta b xi).trans htheta)
      (fun j => htheta ▸ out.right_slot_characters b xi j)
      (hrightPrime b xi) ((out.right_kappa b).trans hkappa) hmesh
      ground engine reflection sigma padding A Cp Hp lower upper T (hrightProfile b xi)

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.frozenMovingChild_recipePrimitive
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.frozenCompleteRecipeEngineOutput
