import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceScaleSupRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderReflectionFamily
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderTail
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerRecipe

/-!
# The fixed arithmetic inventory of the actual source

The original recipe has exactly its two detector presentations.  Its
finite theta filter, calibration twist and target are fixed before any
source scale, row, sector or profile parameters.  The same finite subgroup
contains every coefficient cycle, and each reflected period has its own
genuinely constructed Mellin source.

The general reflected input is proved from the original quadratic and
cubic sieves.  No new reflected-energy premise is added to the skeleton.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualArithmetic

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open SourceScaleSupRows TerminalBackgrounds
open scoped Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

def twists : Subgroup (HeckeCharacter K) :=
  generatedTwists K (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    (probeData K c).G

instance twists_finite : Finite (twists K c) :=
  generatedTwists_finite K _ _
    (Expansion.Project.canonicalDetectorTheta_finiteOrder K (targetCharacter K c))
    (calibration_G_finite_order K c)

theorem calibration_mem : (probeData K c).G ∈ twists K c :=
  calibration_mem_generatedTwists K _ _

theorem original_theta (i : Parameters K c) :
    (originalData K c i).theta =
      Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) := rfl

theorem original_direction (i : Parameters K c) :
    (originalData K c i).direction = 1 := rfl

theorem pulled_direction (i : Parameters K c) :
    (pulledData K c i).direction = 1 := rfl

/-- Every complete ideal remains a row after the sixth-power profile
pullback.  Neither the character nor its original zero mask is altered. -/
theorem pulled_arithmetic (i : Parameters K c) :
    (pulledData K c i).allowedRow = completeIdealIsExterior K (places K c) ∧
      (pulledData K c i).rowCharacter = completeIdealRowCharacter K (places K c)
        (probeData K c) (momentRowCharacters K c) i.sector ∧
      (pulledData K c i).commonMask = completeIdealCommonMask K (places K c) :=
  recipe_unmarked_arithmetic (expansionRecipeRaw K c) i.rowScale i.polynomialScale
    i.sector i.heights i.realShifts i.imagShifts

theorem pulled_rows (i : Parameters K c) (H : ℝ) :
    (pulledData K c i).rows H = (originalData K c i).rows H := rfl

/-- The background is conjugated at the same time as the whole inverse
polynomial, producing precisely the allowed inverse-oriented class. -/
theorem pulled_background (i : Parameters K c) :
    BackgroundCycle.Admissible K (twists K c) (targetCharacter K c)
      (pulledData K c i).inverseBackground⁻¹ := by
  have h := directed_background_admissible K c.family.omega (targetCharacter K c)
    (originalData K c i) (probeData K c).G
  rw [original_direction, zpow_neg_one, original_theta] at h
  exact h

theorem filter_unramified (θ : HeckeCharacter K)
    (hθ : θ ∈ Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) : UnramifiedAt K θ p := by
  by_cases hf : FiniteOrder (targetCharacter K c)
  · simp only [Expansion.Project.canonicalDetectorTheta, if_pos hf,
      Finset.mem_insert, Finset.mem_singleton] at hθ
    rcases hθ with rfl | rfl | rfl
    · exact unramifiedAt_one K p
    · exact target_unramified_outside K c p hp
    · exact (target_unramified_outside K c p hp).inv K
  · have heq : θ = 1 := by
      simpa only [Expansion.Project.canonicalDetectorTheta, if_neg hf,
        Finset.mem_singleton] using hθ
    subst θ
    exact unramifiedAt_one K p

theorem twists_unramified (θ : HeckeCharacter K) (hθ : θ ∈ twists K c)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) : UnramifiedAt K θ p :=
  generatedTwists_unramified K (places K c)
    (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
    (probeData K c).G (filter_unramified K c)
    (calibration_G_unramified K c) θ hθ p hp

theorem admissible_unramified (ν : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K (twists K c) (targetCharacter K c) ν)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) : UnramifiedAt K ν p := by
  rcases hν with hν | ⟨θ, hθ, rfl⟩
  · exact twists_unramified K c ν hν p hp
  · exact (target_unramified_outside K c p hp).mul K (twists_unramified K c θ hθ p hp)

def periods : Finset (HeckeCharacter K) :=
  periodInventory K (twists K c) (targetCharacter K c) (probeData K c).Lambda

theorem periods_unramified (θ : HeckeCharacter K) (hθ : θ ∈ periods K c)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) : UnramifiedAt K θ p :=
  inventory_unramified K (places K c) (twists K c) (targetCharacter K c)
    (probeData K c).Lambda (twists_unramified K c)
    (target_unramified_outside K c) (calibration_lambda_unramified K c) θ hθ p hp

theorem periods_angular (θ : HeckeCharacter K) (hθ : θ ∈ periods K c) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex), heckeComplexWeight K v hv θ ≠ 0 :=
  inventory_nonzero_angular K c (twists K c) θ hθ

def reflectionFamily : GeneralReflectedEnergy.ReflectionFamily K (places K c)
    (probeData K c).arithmetic (periods K c) :=
  TerminalReflectionFamily.actualFamily K c (periods K c)
    (periods_unramified K c) (periods_angular K c)

/-- The finite inventory and every member of its Mellin family are
fixed before the analytic constants are selected. -/
theorem reflected_input
    (hquadratic : HeckeSkeleton.LowEnergy.ActualSieveDictionary.ExteriorQuadraticBound
      K (places K c) (probeData K c).arithmetic)
    (hcubic : HeckeSkeleton.LowEnergy.ActualSieveDictionary.ExteriorCubicBound
      K (places K c) (probeData K c).arithmetic) :
    GeneralReflectedEnergy.Input K (places K c) (probeData K c).arithmetic
      (reflectionFamily K c).data (periods K c) :=
  TerminalTail.reflected_energy_input K (places K c) (probeData K c).arithmetic
    (periods K c) (reflectionFamily K c) hquadratic hcubic

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualArithmetic

end
