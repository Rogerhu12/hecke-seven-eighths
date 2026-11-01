import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedSchwartzProfileBridge
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StrictChildRank
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FrozenEngineOutput

/-!
# The actual canonical children satisfy their scheduled profile primitive

One finite Schwartz-to-Euler coefficient is selected before the original
height budget. The same actual raw child windows, their genuine width
decrease, and zero-slot preservation then prove profile admissibility
before recursive labels are formed. There is no recursive energy input.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField Set HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open MeasureTheory EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The minimum coefficient passed into the actual source preparation. -/
def strictChildProfileMinimum
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 < upper) : ℝ :=
  (exists_rankedAnnulusSchwartz_profileBudget (K := K) (ω := ω) (ψ := ψ)
    ground engine reflection sigma widthLimit padding A lower upper hlower hupper).choose

theorem strictChildProfileMinimum_one_le
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 < upper) :
    1 ≤ strictChildProfileMinimum (K := K) (ω := ω) (ψ := ψ)
      ground engine reflection sigma widthLimit padding A lower upper hlower hupper :=
  (exists_rankedAnnulusSchwartz_profileBudget (K := K) (ω := ω) (ψ := ψ)
    ground engine reflection sigma widthLimit padding A lower upper hlower hupper).choose_spec.1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Both actual children are calibrated before either is assigned a
recursive label. The input windows are the proved positive windows of
these same children, not an asserted closure for arbitrary descendants. -/
theorem engineOutput_frozen_rankedProfiles
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (Cp Hp T : ℝ)
    (hminimum : strictChildProfileMinimum (K := K) (ω := ω) (ψ := ψ)
      ground engine reflection sigma widthLimit padding A lower upper hlower hupper ≤ Cp)
    (hHp : 0 ≤ Hp) (hT : 0 ≤ T)
    {n : Node K ω ψ} {U delta beta C control : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (out : n.EngineOutput (Ω := Ω) U sigma delta beta C control admissible)
    (hsigma : 0 < sigma) (hwidth : n.width ≤ widthLimit)
    (hlength : n.parameters.z = n.data.geometry.totalLength)
    (orders : Finset (ℕ × ℕ))
    (horders : eulerSchwartzOrders (K := K) (ω := ω) (ψ := ψ)
      (lower / clippedAnnulusStep upper (6 * (widthBand sigma widthLimit + 1)) ^
        (6 * (widthBand sigma widthLimit + 1)))
      (upper * (2 : ℝ) ^ (6 * (widthBand sigma widthLimit + 1)))
      (div_pos hlower (pow_pos (clippedAnnulusStep_pos upper _) _))
      (backwardProfileOrder ground engine reflection
        (parameterCoreRank sigma widthLimit padding n.parameters - 1)) A ⊆ orders)
    (hleft : ∀ b xi, InFixedProfileWindow Set.univ Set.univ
      (Icc ((clippedAnnulusLower lower upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters) / 2) /
        (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters)))
        (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters)))
      orders (out.leftData b xi))
    (hright : ∀ b xi, InFixedProfileWindow Set.univ Set.univ
      (Icc ((clippedAnnulusLower lower upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters) / 2) /
        (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters)))
        (2 * rankedAnnulusUpper upper (6 * (widthBand sigma widthLimit + 1))
          (parameterCoreRank sigma widthLimit padding n.parameters)))
      orders (out.rightData b xi)) :
    (∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma widthLimit padding A
        (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.leftData b xi) 0) (out.leftParameters b)) ∧
    (∀ b xi, admissibleOfInvariant
      (rankedAnnulusProfilePrimitive ground engine reflection sigma widthLimit padding A
        (profileFamilyBudget Cp Hp T) lower upper)
      (freezeMomentTime (out.rightData b xi) 0) (out.rightParameters b)) := by
  have controls :=
    (exists_rankedAnnulusSchwartz_profileBudget (K := K) (ω := ω) (ψ := ψ)
      ground engine reflection sigma widthLimit padding A lower upper hlower hupper).choose_spec.2
  have hparent := (parameterCoreRank_lt_bound n.parameters hsigma hwidth).le
  constructor
  · intro b xi
    have hrank := (engineOutput_children_rank
      (widthLimit := widthLimit) (padding := padding) out hsigma hlength b xi).1
    obtain ⟨profiles⟩ := hleft b xi
    exact controls Cp Hp T hminimum hHp hT n.parameters (out.leftParameters b)
      (freezeMomentTime (out.leftData b xi) 0) hparent hrank orders horders
      ⟨freezeRawProfileWindow profiles⟩
  · intro b xi
    have hrank := (engineOutput_children_rank
      (widthLimit := widthLimit) (padding := padding) out hsigma hlength b xi).2
    obtain ⟨profiles⟩ := hright b xi
    exact controls Cp Hp T hminimum hHp hT n.parameters (out.rightParameters b)
      (freezeMomentTime (out.rightData b xi) 0) hparent hrank orders horders
      ⟨freezeRawProfileWindow profiles⟩

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.strictChildProfileMinimum_one_le
#print axioms HeckeSkeleton.Moments.EngineInduction.engineOutput_frozen_rankedProfiles
