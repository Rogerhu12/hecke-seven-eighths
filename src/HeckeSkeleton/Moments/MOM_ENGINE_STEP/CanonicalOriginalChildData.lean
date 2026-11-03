import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe

/-!
# Raw child data from original arithmetic and actual profile factors

This constructor starts with the original fixed background and theta,
the actual moving S-integer factors, one original finite correction,
the residual complete-row sectors, and the actual plain/slot profiles.
It constructs the row character, complete common mask, exhaustive row
enumeration, and finite-order proofs internally.  The retained slot
characters are the original parent's selected characters.

The joint row/support bound is imposed on the actual allowed predicate.
An original physical row enters that predicate by its genuine frequency
norm factorization; no completed transformed MomentData, arithmetic
dictionary, allowed-row certificate, or admissibility is an input.
This file does not assert that arbitrary profile factors already have
the analytic windows required by the final producer.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K}

private theorem original_correction_finite (parent : MomentData K ω ψ)
    (correction : HeckeCharacter K)
    (hcorr : correction = 1 ∨ correction ∈ parent.theta) : FiniteOrder correction := by
  rcases hcorr with h | h
  · rw [h]
    exact IsOfFinOrder.one
  · exact parent.theta_finite _ h

/-- The raw data use full residual ideals, including sixth-power
descendants.  Fixed moving phases are genuine arithmetic coefficients. -/
def data (parent : MomentData K ω ψ)
    (moving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K)
    (hcorr : correction = 1 ∨ correction ∈ parent.theta)
    (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
    (inverse left right : IdealTest K) (geometry : SlotGeometry K)
    (index : Fin geometry.slotCount → Fin parent.geometry.slotCount) :
    MomentData K ω ψ where
  theta := parent.theta
  theta_finite := parent.theta_finite
  inverseBackground := parent.inverseBackground
  direction := parent.direction
  direction_spec := parent.direction_spec
  directed_background := parent.directed_background
  plainBackground := parent.plainBackground
  plain_background_spec := parent.plain_background_spec
  rowCharacter u := correction * moving.character *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (sector u) u
  rowCharacter_finite u :=
    ((original_correction_finite parent correction hcorr).mul moving.character_finite).mul
      (completeIdealRowCharacter_finite K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (sector u) u)
  allowedRow u := completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u ∧
    idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ budget
  rows U := (completeExteriorIdealRows K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) U).filter
    (fun u => idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ budget)
  rows_spec U u := by
    rw [Finset.mem_filter, mem_completeExteriorIdealRows]
    tauto
  commonMask u I :=
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I moving.support.val)) && decide (IsCoprime I remaining.val))
  inverseTest := inverse
  plainTest₁ := left
  plainTest₂ := right
  geometry := geometry
  slotCoefficient i := parent.slotCoefficient (index i)

variable (parent : MomentData K ω ψ)
variable (moving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (hcorr : correction = 1 ∨ correction ∈ parent.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K → SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (budget : ℝ)
variable {X : Type*}
variable (inverse left right : X → IdealTest K) (geometry : X → SlotGeometry K)
variable (index : ∀ ξ, Fin (geometry ξ).slotCount → Fin parent.geometry.slotCount)

/-- The original full moving recipe is a conclusion of the raw
constructor, on every allowed ideal and at every Fourier parameter. -/
def recipe : CompleteMovingRowRecipe A P R (fun ξ =>
    data parent moving correction hcorr sector remaining budget
      (inverse ξ) (left ξ) (right ξ) (geometry ξ) (index ξ)) where
  moving := moving
  correction := correction
  correction_mem _ := hcorr
  sector := sector
  exterior _ _ hu := hu.1
  character _ _ _ := rfl
  remaining := remaining
  mask _ _ _ := rfl

theorem recipe_fullJointBudget (Z width : ℝ) :
    (recipe parent moving correction hcorr sector remaining (Z ^ width)
      inverse left right geometry index).FullJointBudget Z width := by
  intro ξ u hu
  exact hu.2

theorem recipe_jointBudget (Z width : ℝ) :
    (recipe parent moving correction hcorr sector remaining (Z ^ width)
      inverse left right geometry index).JointBudget Z width :=
  CompleteMovingRowRecipe.jointBudget_of_full _ Z width
    (recipe_fullJointBudget parent moving correction hcorr sector remaining
      inverse left right geometry index Z width)

/-- Original finite slot characters survive literally; no correction
outside the original theta family is introduced as a slot character. -/
theorem slot_in_theta (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
    (ξ : X) (i : Fin (geometry ξ).slotCount) :
    (data parent moving correction hcorr sector remaining budget
      (inverse ξ) (left ξ) (right ξ) (geometry ξ) (index ξ)).slotCoefficient i ∈
      (data parent moving correction hcorr sector remaining budget
        (inverse ξ) (left ξ) (right ξ) (geometry ξ) (index ξ)).theta :=
  hslot (index ξ i)

/-- The actual residual ideal is exterior; its original norm identity
then proves the new allowed predicate without an allowed-row premise. -/
theorem source_allowed {Ih : A.Exterior} {h g : A.R} {factor : ℝ}
    (row : ActualChildRow Ih h g factor)
    (hsource : A.exteriorNorm Ih * idealNorm K (moving.fullMaskSupport remaining) ≤
      factor * budget)
    (ξ : X) :
    (data parent moving correction hcorr sector remaining budget
      (inverse ξ) (left ξ) (right ξ) (geometry ξ) (index ξ)).allowedRow row.momentIdeal := by
  refine ⟨(HeckeAxiom.exteriorEquiv A row.ideal).property, ?_⟩
  apply le_of_mul_le_mul_left _ row.factor_pos
  change factor * (A.exteriorNorm row.ideal *
    idealNorm K (moving.fullMaskSupport remaining)) ≤ factor * budget
  rw [← mul_assoc, ← row.norm_factor]
  exact hsource

/-- The complete source mask is visible at every individual ideal,
including every ramification zero of the full residual row. -/
theorem maskValue_eq (ξ : X) (u I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    maskValue (data parent moving correction hcorr sector remaining budget
      (inverse ξ) (left ξ) (right ξ) (geometry ξ) (index ξ)) u I.val =
      (if completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I.val
        then (1 : ℂ) else 0) *
      (if IsCoprime I.val moving.support.val then (1 : ℂ) else 0) *
      (if IsCoprime I.val remaining.val then (1 : ℂ) else 0) := by
  unfold maskValue data
  by_cases hrow : completeIdealCommonMask K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I.val <;>
    by_cases hmove : IsCoprime I.val moving.support.val <;>
    by_cases hremain : IsCoprime I.val remaining.val <;>
    simp [hrow, hmove, hremain]

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.recipe
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.recipe_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.recipe_jointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.source_allowed
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalChildData.maskValue_eq
