import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MomentDataAdapter

/-!
# Principal exceptions from the original fixed background family

Only the original fixed characters enter the hypothesis. If the fixed
background has finite order, its two orientations belong to the chosen
fixed finite family; otherwise a finite row character cannot cancel it.
The conclusion therefore applies to the constructed children without a
new principal-exception oracle for their moving row characters.
-/

noncomputable section
open scoped NumberField

namespace HeckeSkeleton.Moments.EngineStep.OriginalFixedThetaClosure

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Fixed original background membership supplies the principal-row
condition for every finite complete row character. -/
theorem principal_in_theta (d : MomentData K ω ψ)
    (hone : (1 : HeckeCharacter K) ∈ d.theta)
    (hbackground : FiniteOrder ψ → ψ ∈ d.theta ∧ ψ⁻¹ ∈ d.theta)
    (u : NonzeroIdeal K) (hprincipal : d.plainBackground * d.rowCharacter u = 1) :
    d.rowCharacter u ∈ d.theta := by
  have hrow : d.rowCharacter u = d.plainBackground⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hprincipal)
  rcases d.plain_background_spec with hb | hb | hb
  · have he : d.rowCharacter u = 1 := by simpa only [hb, inv_one] using hrow
    simpa only [he] using hone
  · have he : d.rowCharacter u = ψ⁻¹ := by simpa only [hb] using hrow
    have hf : FiniteOrder ψ := isOfFinOrder_inv_iff.mp (he ▸ d.rowCharacter_finite u)
    simpa only [he] using (hbackground hf).2
  · have he : d.rowCharacter u = ψ := by simpa only [hb, inv_inv] using hrow
    have hf : FiniteOrder ψ := he ▸ d.rowCharacter_finite u
    simpa only [he] using (hbackground hf).1

/-- If the original fixed background has infinite order, only the
principal fixed character needs to be in the finite family. -/
theorem principal_in_theta_of_infinite_order (d : MomentData K ω ψ)
    (hone : (1 : HeckeCharacter K) ∈ d.theta) (hbackground : ¬FiniteOrder ψ)
    (u : NonzeroIdeal K) (hprincipal : d.plainBackground * d.rowCharacter u = 1) :
    d.rowCharacter u ∈ d.theta :=
  principal_in_theta d hone (fun h => (hbackground h).elim) u hprincipal

end HeckeSkeleton.Moments.EngineStep.OriginalFixedThetaClosure

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFixedThetaClosure.principal_in_theta
