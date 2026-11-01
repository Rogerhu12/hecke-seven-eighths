import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourceBudgets
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionPrimitiveFamily
import Expansion.CanonicalDetectorCharacters

/-!
# Recovering actual reflection arithmetic from the same complete recipe

Every original or strict child source retains one complete moving recipe
and both of its arithmetic budgets. These data reconstruct the ordinary
reflection calibration with the recipe's actual full mask support.
Neither the varying row nor any redundant fixed factor is discarded.

The original canonical theta family absorbs every permitted finite plain
background. Together with the target's original radial normalization,
this proves the non-norm condition on the child's own paired-row filter.
It does not assume that the child's filter is the parent's old filter.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global Expansion.Project
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)}
variable {U : ℝ} {d : MomentData K c.family.omega (targetCharacter K c)}
variable {p : PairedInvariantParameters}

/-- The actual factors and the two bounds, rather than an unrelated
mask witness, supply the full calibration of this literal node. -/
theorem CompleteSourceBudgetData.reflectionArithmetic
    (D : CompleteSourceBudgetData c theta U d p)
    (w : InfinitePlace K)
    (hpsi : heckeRadialParameter K w (targetCharacter K c) = 0)
    (hfinite : FiniteOrder d.plainBackground → d.plainBackground⁻¹ ∈ d.theta) :
    reflectionArithmeticPrimitive (places K c) (probeData K c)
      (momentRowCharacters K c) theta U d p := by
  refine ⟨fun _ => D.source.remaining, ?_, D.source.mask, ?_⟩
  · exact movingReflectionCalibration_of_recipe (Node.ordinary d p.parameters)
      D.source.recipe theta (by intro eta heta; simpa only [D.source.theta_eq] using heta) U
      D.supportBudget D.pairedJointBudget
  · exact pairedRows_actualPlain_nonNorm_of_target d w hpsi hfinite p.parameters U

/-- The canonical fixed theta handles all three backgrounds permitted
by MomentData, including backgrounds created by strict conjugation. -/
theorem canonicalTheta_finite_plainBackground
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (d : MomentData K omegaCharacter psiCharacter)
    (htheta : d.theta = canonicalDetectorTheta K psiCharacter)
    (hfinite : FiniteOrder d.plainBackground) :
    d.plainBackground⁻¹ ∈ d.theta := by
  rw [htheta]
  rcases d.plain_background_spec with hbackground | hbackground | hbackground
  · simpa only [hbackground, inv_one] using
      one_mem_canonicalDetectorTheta K psiCharacter
  · have hpsi : FiniteOrder psiCharacter := hbackground ▸ hfinite
    simp [hbackground, canonicalDetectorTheta, hpsi]
  · have hpsi : FiniteOrder psiCharacter := by
      simpa only [hbackground, inv_inv] using hfinite.inv
    simp [hbackground, canonicalDetectorTheta, hpsi]

/-- Inversion does not enlarge the original canonical exceptional set.
This supplies the strict producer's inverse slot-character premise. -/
theorem canonicalTheta_inv_mem {psiCharacter eta : HeckeCharacter K}
    (heta : eta ∈ canonicalDetectorTheta K psiCharacter) :
    eta⁻¹ ∈ canonicalDetectorTheta K psiCharacter := by
  by_cases hpsi : FiniteOrder psiCharacter
  · simp only [canonicalDetectorTheta, if_pos hpsi, Finset.mem_insert,
      Finset.mem_singleton] at heta ⊢
    rcases heta with rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (inv_inv _))
  · have h : eta = 1 := by simpa [canonicalDetectorTheta, hpsi] using heta
    simpa only [h, inv_one] using one_mem_canonicalDetectorTheta K psiCharacter

/-- The strict source's slot hypotheses follow from the one original
theta and its actual retained slot dictionary. -/
theorem CompleteSourceBudgetData.canonicalInverseSlots
    (D : CompleteSourceBudgetData c
      (canonicalDetectorTheta K (targetCharacter K c)) U d p) :
    ∀ j, (d.slotCoefficient j)⁻¹ ∈ d.theta := by
  intro j
  rw [D.source.theta_eq]
  exact canonicalTheta_inv_mem (D.source.slot_characters j)

/-- At the actual fixed-theta source all non-norm inputs are proved
from the original target, even after the last slot has disappeared. -/
theorem CompleteSourceBudgetData.canonicalReflectionArithmetic
    (D : CompleteSourceBudgetData c
      (canonicalDetectorTheta K (targetCharacter K c)) U d p) :
    reflectionArithmeticPrimitive (places K c) (probeData K c)
      (momentRowCharacters K c)
      (canonicalDetectorTheta K (targetCharacter K c)) U d p :=
  D.reflectionArithmetic (normNormalizationPlace K) (targetCharacter_radial_zero K c)
    (canonicalTheta_finite_plainBackground d D.source.theta_eq)

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.CompleteSourceBudgetData.reflectionArithmetic
#print axioms HeckeSkeleton.Moments.EngineInduction.canonicalTheta_finite_plainBackground
#print axioms HeckeSkeleton.Moments.EngineInduction.CompleteSourceBudgetData.canonicalReflectionArithmetic
