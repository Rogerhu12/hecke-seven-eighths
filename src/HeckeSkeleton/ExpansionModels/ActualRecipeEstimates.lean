import HeckeSkeleton.Base
import Expansion.ActualRecipeIdentity
import Expansion.ActualRecipeTailBounds
import HeckeSkeleton.ExpansionModels.ActualPresentationBoundary

/-!
# Bounds and detector sources for the original raw recipe

These are specializations of the proved actual arithmetic statements to
the one Axiom choice already made by Base.  No theorem in this file takes
an expansion estimate, an integral identity or a detector conclusion as
an input.  The common retained constants precede every scale and height.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project
open scoped BigOperators

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar
  expansionNormOneSpace expansionNormOneBorel

theorem expansionPhysicalParameters_e_lamB (c : TargetContext K) :
    (expansionPhysicalParameters K c).e ≤ c.lamB / 1000 := by
  have h := (expansionPhysicalParameters K c).e_cap
  dsimp only [expansionInternalCap] at h
  linarith [min_le_right c.family.lamA c.lamB]

theorem highExpansion_principal_eq_actual (c : TargetContext K) (Z H : ℝ) :
    (highExpansion K c Z H).principal =
      actualPrincipalRetained K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
        (targetCharacter K c) c.geometry Z H c.family.B (expansionPhysicalParameters K c).e := rfl

theorem highExpansion_small_eq_actual (c : TargetContext K) (Z H : ℝ) :
    (highExpansion K c Z H).small =
      actualSmallRetained K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
        (targetCharacter K c) c.geometry Z H c.family.B (expansionPhysicalParameters K c).e := rfl

theorem highExpansion_large_eq_actual (c : TargetContext K) (Z H : ℝ) :
    (highExpansion K c Z H).large =
      actualLargeRetained K (excludedPlaces K c)
        (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
        (targetCharacter K c) c.geometry Z H (expansionShellAllowance K c) := rfl

/-- The three original powers with one common retained constant and degree. -/
def ActualRetainedEstimates (c : TargetContext K) (C Z0 A : ℝ) : Prop :=
  0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
    (‖(highExpansion K c Z H).principal‖ ≤
      C * (Z ^ (c.family.B - 11 / 16 - 23 / 960 + c.lamB) +
        Z ^ (c.family.B - 11 / 16 - 13 / 9600 + c.lamB) +
        Z ^ (c.family.B - 11 / 16 - principalSlotSaving c.geometry + c.lamB)) *
        (1 + H) ^ A) ∧
    (‖(highExpansion K c Z H).small‖ ≤
      C * Z ^ (c.family.B - 11 / 16 - 1 / 50 + c.lamB) * (1 + H) ^ A) ∧
    (‖(highExpansion K c Z H).large‖ ≤
      C * Z ^ (c.family.B - 11 / 16 - 63 / 800 + c.lamB) * (1 + H) ^ A)

theorem exists_actualRetainedEstimates (c : TargetContext K) :
    ∃ b : ℝ × ℝ × ℝ, ActualRetainedEstimates K c b.1 b.2.1 b.2.2 := by
  have hAllowed : AllowedGeneratorInput K (places K c) (probeData K c).arithmetic :=
    Expansion.ActualProbeContext.allowedGenerators K (axiomChoice K c)
  have hcal : ThetaCalibrationInput K (places K c) (probeData K c).arithmetic
      (probeData K c).Lambda (probeData K c).G :=
    Expansion.ActualProbeContext.arithmeticCalibration K (axiomChoice K c)
  have hunram : ∀ p : ExteriorPrime K (places K c),
      UnramifiedAt K (targetCharacter K c) p.val :=
    fun p => target_unramified_outside K c p.val p.property
  obtain ⟨C, Z0, A, hC, hZ0, hA, hb⟩ :=
    exists_actual_retained_components_bound K (excludedPlaces K c)
      (Expansion.ActualProbeContext.allLocalMeasures K)
      (Expansion.ActualProbeContext.finiteAdeleMeasure K) (isComplex_of_family K c)
      (probeData K c) c.family.omega (targetCharacter K c) (representative K c).val.property
      hAllowed hcal hunram c.geometry c.family.B_lower c.family.B_upper
      (expansionPhysicalParameters K c).e_pos (expansionPhysicalParameters K c).e_small
      c.lamB_pos (expansionPhysicalParameters_e_lamB K c)
      (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).1 c.family.boundary
  exact ⟨(C, Z0, A), hC, hZ0, hA, hb⟩

/-- This numerical choice is made from the proved estimates, before tau. -/
def expansionRetainedData (c : TargetContext K) : ℝ × ℝ × ℝ :=
  Classical.choose (exists_actualRetainedEstimates K c)

theorem expansionRetainedData_spec (c : TargetContext K) :
    ActualRetainedEstimates K c (expansionRetainedData K c).1
      (expansionRetainedData K c).2.1 (expansionRetainedData K c).2.2 :=
  Classical.choose_spec (exists_actualRetainedEstimates K c)

/-- The original raw item's own block family carries the proved detector
source above one threshold for every permitted positive height exponent. -/
theorem expansionRecipeRaw_source (c : TargetContext K) (tau : ℝ)
    (htau : 0 < tau) (hceiling : tau ≤ (expansionPhysicalParameters K c).ceiling) :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ b : Fin (highExpansion K c Z (Z ^ tau)).blockCount,
        BlockSource c.geometry ((highExpansion K c Z (Z ^ tau)).block b)
          c.family.B c.family.lamA (expansionPhysicalParameters K c).k Z :=
  actualPhysicalRecipe_source_at_power_height K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry (representative K c).val.property
    (expansionBoundary_lower K c) c.family.B_upper c.family.boundary c.family.lamA
    (expansionShellAllowance K c) (expansionInternalCap K c)
    (expansionPhysicalParameters K c) tau htau hceiling

/-- The global integral identity specialized to the original probe,
measure family and raw recipe. Both numerical guards are the existing
active schedule guards, not new assumptions on the target context. -/
theorem expansionRecipeRaw_identity (c : TargetContext K) (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (targetData K c).probeFunction (targetCharacter K c) Z -
      (targetData K c).signal (targetCharacter K c) Z =
      (highExpansion K c Z H).principal + (highExpansion K c Z H).small +
      (highExpansion K c Z H).large +
      (∑ b, ((highExpansion K c Z H).block b).value) +
      (highExpansion K c Z H).tail := by
  exact actualPhysicalRecipe_identity K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K)
    (Expansion.ActualProbeContext.finiteAdeleMeasure K)
    (Expansion.ActualProbeContext.adeleMeasure K)
    (probeData K c) c.family.omega (targetCharacter K c) c.geometry
    (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
    c.family.boundary c.family.lamA (expansionShellAllowance K c)
    (expansionInternalCap K c) (expansionPhysicalParameters K c)
    (isComplex_of_family K c)
    (Expansion.ActualProbeContext.fourier_zero K (axiomChoice K c))
    (Expansion.ActualProbeContext.allowedGenerators K (axiomChoice K c))
    (Expansion.ActualProbeContext.arithmeticCalibration K (axiomChoice K c))
    (fun p => target_unramified_outside K c p.val p.property)
    (Expansion.ActualProbeContext.normalizer_ne_zero K (axiomChoice K c))
    c.family.B_lower (expansionPhysicalParameters_e_sweep K c)
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).1 Z H hZ hH

/-- Each literal tail summand has its actual arithmetic decay estimate;
the fixed-bin difference uses exactly the boundary hypothesis already
present in the original expansion interface. -/
theorem expansionRecipeRaw_tail (c : TargetContext K)
    (hmove : HighBoundaryControl K c (actualHighPresentation K c)) :
    PowerHeightTailBound (fun Z H => (highExpansion K c Z H).tail) := by
  exact actualPhysicalExpansionTail_bound K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K)
    (Expansion.ActualProbeContext.finiteAdeleMeasure K)
    (isComplex_of_family K c) (probeData K c) c.family.omega (targetCharacter K c)
    (representative K c).val.property
    (Expansion.ActualProbeContext.allowedGenerators K (axiomChoice K c))
    (Expansion.ActualProbeContext.arithmeticCalibration K (axiomChoice K c))
    (fun p => target_unramified_outside K c p.val p.property) c.geometry
    (expansionBoundary_lower K c) c.family.B_lower c.family.B_upper
    (expansionPhysicalParameters K c).e_pos (expansionPhysicalParameters_e_sweep K c)
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).1 c.family.boundary
    (physicalScheduledWholeBoundary_tail_of_highBoundaryControl K c hmove)

end HeckeSkeleton

#print axioms HeckeSkeleton.exists_actualRetainedEstimates
#print axioms HeckeSkeleton.expansionRetainedData_spec
#print axioms HeckeSkeleton.expansionRecipeRaw_source
#print axioms HeckeSkeleton.expansionRecipeRaw_identity
#print axioms HeckeSkeleton.expansionRecipeRaw_tail
