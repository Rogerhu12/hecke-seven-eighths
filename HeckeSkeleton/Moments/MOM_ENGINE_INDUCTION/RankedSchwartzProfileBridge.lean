import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteSchwartzProfileBridge
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedAnnulusPrimitive

/-!
# The actual normalized window enters the finite-rank primitive

The common maximal annulus selects all Schwartz-to-Euler controls.
Their finite maximum is paid by the source coefficient before the
source height, model or Fourier values are chosen. At a strict child,
the proved active clipping support fits its earlier rank's annulus.
No change to the child's profiles or normalization is necessary.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField Set
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The minimum source coefficient is fixed after the backward order
schedule and before any source data. Every actual normalized strict
child then has the complete ranked profile primitive. -/
theorem exists_rankedAnnulusSchwartz_profileBudget
    (ground : ℕ) (engine reflection : ℕ → ℕ)
    (sigma widthLimit padding A lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 < upper) :
    let N := 6 * (widthBand sigma widthLimit + 1)
    let lowerMax := lower / clippedAnnulusStep upper N ^ N
    let upperMax := upper * (2 : ℝ) ^ N
    let hlowerMax : 0 < lowerMax :=
      div_pos hlower (pow_pos (clippedAnnulusStep_pos upper N) N)
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (Cp Hp T : ℝ), D ≤ Cp → 0 ≤ Hp → 0 ≤ T →
      ∀ (parentParameters childParameters : RealParameters) (child : MomentData K ω ψ),
      parameterCoreRank sigma widthLimit padding parentParameters ≤ N →
      parameterCoreRank sigma widthLimit padding childParameters <
        parameterCoreRank sigma widthLimit padding parentParameters →
      ∀ orders : Finset (ℕ × ℕ),
      eulerSchwartzOrders (K := K) (ω := ω) (ψ := ψ) lowerMax upperMax hlowerMax
        (backwardProfileOrder ground engine reflection
          (parameterCoreRank sigma widthLimit padding parentParameters - 1)) A ⊆ orders →
      InFixedProfileWindow Set.univ Set.univ
        (Icc ((clippedAnnulusLower lower upper N
            (parameterCoreRank sigma widthLimit padding parentParameters) / 2) /
          (2 * rankedAnnulusUpper upper N
            (parameterCoreRank sigma widthLimit padding parentParameters)))
          (2 * rankedAnnulusUpper upper N
            (parameterCoreRank sigma widthLimit padding parentParameters)))
        orders child →
      admissibleOfInvariant
        (rankedAnnulusProfilePrimitive ground engine reflection
          sigma widthLimit padding A (profileFamilyBudget Cp Hp T) lower upper)
        child childParameters := by
  let N := 6 * (widthBand sigma widthLimit + 1)
  let lowerMax := lower / clippedAnnulusStep upper N ^ N
  let upperMax := upper * (2 : ℝ) ^ N
  have hlowerMax : 0 < lowerMax :=
    div_pos hlower (pow_pos (clippedAnnulusStep_pos upper N) N)
  obtain ⟨D, hD, controls⟩ := exists_finiteRank_rawWindow_controls
    (K := K) (ω := ω) (ψ := ψ) lowerMax upperMax hlowerMax N
    (fun rank => backwardProfileOrder ground engine reflection (rank - 1)) A
  refine ⟨D, hD, ?_⟩
  intro Cp Hp T hminimum hHp hT parentParameters childParameters child
    hparent hearlier orders horders hwindow
  have hCp : 0 ≤ Cp := (zero_le_one.trans hD).trans hminimum
  have hbudget : D ≤ profileFamilyBudget Cp Hp T :=
    coefficient_le_profileFamilyBudget hCp hminimum hHp hT
  have hinterval := (clippedAnnulus_child_enlargement_subset hlower.le hupper hparent hearlier).trans
    (clippedAnnulus_maximal_subset hlower.le hupper.le N
      (parameterCoreRank sigma widthLimit padding childParameters))
  have hprofile := controls (parameterCoreRank sigma widthLimit padding parentParameters)
    hparent _ _ orders horders hinterval child hwindow
  exact rankedAnnulusProfilePrimitive_strictChild ground engine reflection
    hlower.le hupper hbudget hparent hearlier hprofile

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.exists_rankedAnnulusSchwartz_profileBudget
