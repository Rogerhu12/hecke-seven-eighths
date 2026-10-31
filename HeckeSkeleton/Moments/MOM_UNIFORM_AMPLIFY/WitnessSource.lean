import HeckeSkeleton.ExpansionModels.SourceData
import HeckeGeneral.Analysis.WitnessRowCount
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.WitnessCalibration
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceWitnessGeometry

/-!
# Independent-scale amplification at the original source witnesses

This module performs the final substitution in the actual finite sector
energy.  All source indices belong to one fixed recipe.  The height degree
and height ceiling are chosen before tau, and the fixed bounded length
range is chosen before either preliminary amplification loss.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {E : MomentSourceData K c}

/-- Only the high-bin witnesses are quantified by the final uniform
energy statement.  Empty or inactive low-bin labels impose no length
condition. -/
abbrev HighMomentIndexFor (K : Type) [Field K] [NumberField K]
    (c : TargetContext K) (E : MomentSourceData K c) (Z T : ℝ) :=
  {i : SourceMomentIndexFor K c E Z T // 51 / 100 < (momentBlockFor i).bin}

/-- Evaluate the independently amplified family at its own source
parameters.  The hypotheses on the source are only geometric: a common
positive lower shell, a bounded inverse length, and the original parameter
box.  They contain no energy estimate. -/
theorem source_inverse_amplified_witness_models
    (M : SourceMomentModelsFor K c E)
    (hamp : AmplifiedIndependentMomentBoundFor M)
    (hp : SourceMomentParameterControlFor M)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hgeometry : ∀ Z T (i : SourceMomentIndexFor K c E Z T),
      51 / 100 < (momentBlockFor i).bin → d ≤ (momentBlockFor i).shell ∧
        0 ≤ (momentWitnessFor i).inverseLength ∧
          (momentWitnessFor i).inverseLength ≤ L) :
    UniformMomentBoundFor
      (fun _ _ i => amplifiedModelEnergyFor M i)
      (fun _ _ i => amplifiedInverseExponent (momentWitnessFor i).inverseLength)
      (fun _ _ _ => True) := by
  have hcal := uniform_witness_calibration
    (fun Z T (i : HighMomentIndexFor K c E Z T) => amplifiedModelEnergyFor M i.val)
    (fun _ _ i => momentBaseFor i.val)
    (fun _ _ i => (momentWitnessFor i.val).inverseLength)
    (fun Z T i => ‖M.heights Z T i.val‖)
    (d := d) (R := L) (loss := c.family.lamA) (Cht := 1) (B := 1)
    hd hL c.family.lamA_pos (by norm_num) (by norm_num)
    (by
      intro Z T hZ hT i
      obtain ⟨hshell, hr, hrL⟩ := hgeometry Z T i.val i.property
      refine ⟨?_, hr, hrL, norm_nonneg _, ?_⟩
      · exact Real.rpow_le_rpow_of_exponent_le hZ hshell
      · simpa only [Real.rpow_one, one_mul] using
          (hp Z T i.val).1.trans (show T ≤ 1 + T by linarith))
    (by
      intro a ε ha hε
      obtain ⟨C, A, h, hC, hA, hh, hbound⟩ := hamp a ε ha hε
      refine ⟨C, A, h, hC, hA, hh, ?_⟩
      intro Z T i hU hD hheight
      exact hbound (momentBaseFor i.val)
        (momentBaseFor i.val ^ (momentWitnessFor i.val).inverseLength) hU hD
        (M.heights Z T i.val) (M.realShifts Z T i.val) (M.imagShifts Z T i.val)
        hheight (hp Z T i.val).2.1 (hp Z T i.val).2.2)
  obtain ⟨A, ceiling, hA, hc, hbound⟩ := hcal
  refine ⟨A, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hbound τ hτ hτc
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ i hbin _heligible
  exact hbound Z hZ ⟨i, hbin⟩

/-- The dyadic recipe supplies the lower shell `1/16` itself.  Its
geometric witness certificate supplies the parameter box; the only length
input here is the bounded interval for the actual inverse witnesses. -/
theorem recipe_inverse_amplified_witness_models
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (hamp : AmplifiedIndependentMomentBoundFor (recipeMomentModels K c R))
    {L N : ℝ} (hL : 0 ≤ L) (hgeometry : R.MomentGeometry N)
    (hlength : ∀ Z T
      (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T),
        51 / 100 < (momentBlockFor i).bin →
        (momentWitnessFor i).inverseLength ≤ L) :
    UniformMomentBoundFor
      (fun _ _ i => amplifiedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => amplifiedInverseExponent (momentWitnessFor i).inverseLength)
      (fun _ _ _ => True) := by
  have hgeom := recipeMomentModels_geometry K c R hgeometry
  apply source_inverse_amplified_witness_models
    (recipeMomentModels K c R) hamp hgeom.2 (d := 1 / 16) (by norm_num) hL
  intro Z T i hbin
  exact ⟨recipeMoment_shell_lower i, (hgeom.1 Z T i).1, hlength Z T i hbin⟩

/-- MI-I-AMPLIFIED-WITNESS-CALIBRATION for the actual source.  All scale,
length and parameter facts are proved for its concrete physical recipe.
The sole analytic input is the independent-scale estimate that this step
is tasked with evaluating. -/
theorem actual_inverse_amplified_witness_models
    (hamp : AmplifiedIndependentMomentBoundFor
      (recipeMomentModels K c (expansionRecipeRaw K c))) :
    UniformMomentBoundFor
      (fun _ _ i => amplifiedModelEnergyFor
        (recipeMomentModels K c (expansionRecipeRaw K c)) i)
      (fun _ _ i => amplifiedInverseExponent (momentWitnessFor i).inverseLength)
      (fun _ _ _ => True) := by
  apply recipe_inverse_amplified_witness_models (expansionRecipeRaw K c) hamp
    (L := 3 / 2 + c.family.lamA)
    (by linarith [c.family.lamA_pos]) (expansionRecipeRaw_geometry K c)
  intro Z T i hbin
  exact (actual_source_witness_inverseLength_range K c i hbin).2

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.source_inverse_amplified_witness_models
#print axioms HeckeSkeleton.Moments.UniformAmplify.recipe_inverse_amplified_witness_models
#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_inverse_amplified_witness_models
