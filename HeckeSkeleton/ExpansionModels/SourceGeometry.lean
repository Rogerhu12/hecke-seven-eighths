import HeckeSkeleton.ExpansionModels.Core

/-!
# Geometry of the actual source parameters

These predicates describe the source's length and parameter ranges without
importing the moment induction or selecting the unfinished named expansion.
The plain-length bound is fixed for the entire recipe before the moment
height exponent or the final small height parameter is chosen.

`MomentGeometry` is a property of the data, not a field of the raw recipe.
The physical detector proves it for its concrete canonical amplitudes.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
variable {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
variable {ψ : HeckeCharacter K} {g : PrimeWindowGeometry}
variable {F : RecipeFamily K ψ g}

/-- The exact parameter region quantified by the source moment profiles. -/
def RecipeWitnessData.ParameterBox (w : RecipeWitnessData K ψ g F)
    (p : Fin 3 → ℝ) (t T : ℝ) : Prop :=
  ‖w.heights p t T‖ ≤ T ∧
    (∀ I : NonzeroIdeal K, ‖w.realShifts I‖ ≤ 8) ∧
    (∀ I : NonzeroIdeal K, ‖w.imagShifts I‖ ≤ 1 + ‖w.heights p t T‖)

/-- Uniform length and parameter ranges for every finite subdivision,
including labels whose selected row fiber is empty. -/
def RecipeAmplitudeData.MomentGeometry (A : RecipeAmplitudeData K S ψ g F)
    (T L : ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 → ∀ j : Fin (A.witnessCount t),
    0 ≤ (A.witness t j).inverseLength ∧
    0 ≤ (A.witness t j).plainLength ∧
    (A.witness t j).plainLength ≤ L ∧
    (A.witness t j).ParameterBox A.physical t T

/-- One common range for every actual block and amplitude of a fixed
all-scale recipe.  The recipe and `L` precede all later moment budgets. -/
def RecipeExpansion.MomentGeometry {ζ : ℝ}
    (R : RecipeExpansion K S ψ g ζ) (L : ℝ) : Prop :=
  ∀ Z T : ℝ, ∀ b : Fin (R.activeCount Z T), ∀ l : Fin R.labelCount,
    ((R.blocks Z T (R.rawBlockIndex Z T b)).amplitude l).MomentGeometry T L

theorem RecipeAmplitudeData.MomentGeometry.mono
    {A : RecipeAmplitudeData K S ψ g F} {T L L' : ℝ}
    (h : A.MomentGeometry T L) (hL : L ≤ L') : A.MomentGeometry T L' := by
  intro t ht ht' j
  obtain ⟨hr, hm, hupper, hbox⟩ := h t ht ht' j
  exact ⟨hr, hm, hupper.trans hL, hbox⟩

theorem RecipeExpansion.MomentGeometry.mono {ζ : ℝ}
    {R : RecipeExpansion K S ψ g ζ} {L L' : ℝ}
    (h : R.MomentGeometry L) (hL : L ≤ L') : R.MomentGeometry L' := by
  intro Z T b l
  exact (h Z T b l).mono hL

end HeckeGeneral.Analysis.ExpansionRecipe

#print axioms HeckeGeneral.Analysis.ExpansionRecipe.RecipeAmplitudeData.MomentGeometry.mono
#print axioms HeckeGeneral.Analysis.ExpansionRecipe.RecipeExpansion.MomentGeometry.mono
