import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCarrierRestoration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePairing

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original residual bound on both sides

The actual carrier restoration is followed by finite weighted Minkowski.
The original common scalar is paid by its exact norm, including when it
vanishes. Multiplication of the two independent expansions retains all
four original rectangles and the original leaf weight and denominator.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

private theorem eq_of_unit_normalizer (x y : ℝ) (z : ℂ)
    (he : x = ‖z‖ ^ 2 * y) (hz : z = 1) : x = y := by
  simpa only [hz, norm_one, one_pow, one_mul] using he

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem rectangleEnergy_eq_source (side rectangle : Bool) (ξ : EngineParameter) :
    seed.ordinary.rectangleEnergy side rectangle ξ =
      (seed.ordinary.originalSource side rectangle).energy
        (σ := Arithmetic.embedding c) ξ := by
  cases side
  · change (seed.ordinary.leftFrame rectangle).energy ξ =
      (seed.ordinary.leftFrame rectangle).source.energy (σ := Arithmetic.embedding c) ξ
    have hg : (seed.ordinary.leftFrame rectangle).normalizer = 1 :=
      seed.atoms.gaussNormalizer false rectangle
    exact eq_of_unit_normalizer _ _ _
      ((seed.ordinary.leftFrame rectangle).energy_eq_source ξ) hg
  · change (seed.ordinary.rightFrame rectangle).energy ξ =
      (seed.ordinary.rightFrame rectangle).source.energy (σ := Arithmetic.embedding c) ξ
    have hg : (seed.ordinary.rightFrame rectangle).normalizer = 1 :=
      seed.atoms.gaussNormalizer true rectangle
    exact eq_of_unit_normalizer _ _ _
      ((seed.ordinary.rightFrame rectangle).energy_eq_source ξ) hg

theorem rectangleRoot_eq_unscaled (side rectangle : Bool) (ξ : EngineParameter) :
    Real.sqrt (seed.ordinary.rectangleEnergy side rectangle ξ) =
      ‖seed.occurrences.normalizer seed.phases side‖ *
        Real.sqrt ((seed.unscaledOriginal side rectangle).energy
          (σ := Arithmetic.embedding c) ξ) := by
  rw [seed.rectangleEnergy_eq_source, seed.original_energy,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem unscaledRoot_le_labels (hpacket : packet.Realizes)
    (side rectangle : Bool) (ξ : EngineParameter) :
    Real.sqrt ((seed.unscaledOriginal side rectangle).energy
      (σ := Arithmetic.embedding c) ξ) ≤
      ∑ a : (seed.canonicalSupport input).labels side,
        ‖PassiveAllocation.sign a.val‖ *
          Real.sqrt ((seed.canonicalSource input (seed.canonicalSupport input)
            side a rectangle).energy (σ := Arithmetic.embedding c) ξ) := by
  rw [seed.unscaledOriginal_energy_restored input hpacket side rectangle ξ]
  have hbound := PassiveAllocation.sqrt_residual_energy_le
    ((seed.canonicalSupport input).carrier side) seed.ordinary.passiveMask
    (seed.ordinary.passiveMask_ne_zero seed.phases.deletion_nonzero)
    (seed.ordinary.originalSource side false).rows
    (seed.canonicalWeight side) (seed.canonicalCoefficient input true side rectangle)
    (fun _ => seed.canonicalLocation side) ξ
  refine hbound.trans_eq ?_
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun e : ℝ => ‖PassiveAllocation.sign a.val‖ * Real.sqrt e)
    (seed.canonicalSource_energy input (seed.canonicalSupport input) side a rectangle ξ).symm

theorem rectangleRoot_le_sideSum (hpacket : packet.Realizes)
    (side rectangle : Bool) (ξ : EngineParameter) :
    Real.sqrt (seed.ordinary.rectangleEnergy side rectangle ξ) ≤
      (seed.refinement input (seed.canonicalSupport input)).sideSum side rectangle ξ := by
  rw [seed.rectangleRoot_eq_unscaled]
  calc
    _ ≤ ‖seed.occurrences.normalizer seed.phases side‖ *
        ∑ a : (seed.canonicalSupport input).labels side,
          ‖PassiveAllocation.sign a.val‖ *
            Real.sqrt ((seed.canonicalSource input (seed.canonicalSupport input)
              side a rectangle).energy (σ := Arithmetic.embedding c) ξ) :=
      mul_le_mul_of_nonneg_left
        (seed.unscaledRoot_le_labels input hpacket side rectangle ξ) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change ‖seed.occurrences.normalizer seed.phases side‖ *
          (‖PassiveAllocation.sign a.val‖ * Real.sqrt
            ((seed.canonicalSource input (seed.canonicalSupport input)
              side a rectangle).energy (σ := Arithmetic.embedding c) ξ)) =
        ‖PassiveAllocation.sign a.val‖ * Real.sqrt
          (‖seed.occurrences.normalizer seed.phases side‖ ^ 2 *
            (seed.canonicalSource input (seed.canonicalSupport input)
              side a rectangle).energy (σ := Arithmetic.embedding c) ξ)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      ring

theorem canonicalRefinement_bound (hpacket : packet.Realizes) :
    seed.RefinementBound input (seed.canonicalSupport input) := by
  intro z
  exact (seed.refinement input (seed.canonicalSupport input)).ordinary_pointwise_of_sideBounds
    (seed.rectangleRoot_le_sideSum input hpacket) z

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalRefinement_bound
