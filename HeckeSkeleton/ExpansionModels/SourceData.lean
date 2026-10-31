import HeckeSkeleton.SourceData
import HeckeSkeleton.ExpansionModels.SourceGeometry

/-!
# The same explicit recipe supplies source data and moment models

An arbitrary fixed `RecipeExpansion R` is used throughout this module.  Its
scale-indexed expansion, source witnesses, row enumeration, actual polynomial
families, and calibration identities are generated together.  The actual
choice `expansionRecipeRaw` occurs only in the compatibility aliases in
`HeckeSkeleton.Moments`.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- Fix the full expansion and dyadic row envelope before uniform constants. -/
def recipeMomentSourceData
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) : MomentSourceData K c where
  expansion := R.toHigh (P := probeData K c) (R := momentRowCharacters K c)
    (ω := c.family.omega)
  rowExponent := momentRowExponent

variable {K c}
variable {R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c)} {Z T : ℝ}

abbrev recipeSourceBlock
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :=
  R.blocks Z T (R.rawBlockIndex Z T i.block)

abbrev recipeSourceAmplitude
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :=
  (recipeSourceBlock i).amplitude i.label

abbrev recipeSourceWitness
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :=
  (recipeSourceAmplitude i).witness i.t i.subdivision

theorem recipeMoment_scale_of_index
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
    (2 : ℝ) ^ (16 : ℕ) ≤ Z ∧ 1 ≤ T :=
  R.active_of_index Z T i.block

theorem recipeMoment_shell_lower
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
    1 / 16 ≤ (momentBlockFor i).shell :=
  (R.shell_range Z T i.block).1

theorem recipeMoment_shell_pos
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
    0 < (momentBlockFor i).shell :=
  (by norm_num : (0 : ℝ) < 1 / 16).trans_le (recipeMoment_shell_lower i)

theorem recipeMomentBase_ge_two
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
    2 ≤ momentBaseFor i :=
  _root_.ExpansionRecipe.shell_base_ge_two
    (recipeMoment_scale_of_index i).1 (recipeMoment_shell_lower i)

theorem recipeMoment_rowWidth_spec
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T) :
    1 < rowWidthFor i ∧ rowWidthFor i ≤ 2 ∧
      momentBaseFor i ^ rowWidthFor i = 2 * momentBaseFor i := by
  have hU2 := recipeMomentBase_ge_two i
  have hU : 1 < momentBaseFor i := by linarith
  change 1 < momentRowExponent (momentBaseFor i) ∧
    momentRowExponent (momentBaseFor i) ≤ 2 ∧
      momentBaseFor i ^ momentRowExponent (momentBaseFor i) = 2 * momentBaseFor i
  rw [momentRowExponent, if_pos hU]
  exact ⟨_root_.ExpansionRecipe.dyadicMassExponent_gt_one hU,
    _root_.ExpansionRecipe.dyadicMassExponent_le_two hU2,
    _root_.ExpansionRecipe.rpow_dyadicMassExponent hU⟩

def recipeSourceSelectedMomentModel
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c))
    (ξ : ExpansionRecipe.RecipeVector)
    (σ τ : NonzeroIdeal K → ExpansionRecipe.RecipeVector) :
    MomentData K c.family.omega (targetCharacter K c) :=
  ((R.family.fullModel K (places K c) (probeData K c)
    (momentRowCharacters K c) c.family.omega (targetCharacter K c) c.geometry
    (momentBaseFor i) (momentBaseFor i ^ (momentWitnessFor i).inverseLength) s ξ σ τ).changeSlotBase
      (momentBlockFor i).shell (recipeMoment_shell_pos i)).restrictSlots i.selected

variable (K c R)

def recipeMomentModels : SourceMomentModelsFor K c (recipeMomentSourceData K c R) where
  dimension := 6
  inverse _Z _T i := recipeSourceSelectedMomentModel i
  paired _Z _T i := recipeSourceSelectedMomentModel i
  unmarked := R.family.inverseFamily K (places K c)
    (probeData K c) (momentRowCharacters K c) c.family.omega
    (targetCharacter K c) c.geometry
  heights _Z T i := (recipeSourceWitness i).heights (recipeSourceAmplitude i).physical i.t T
  realShifts _Z _T i := (recipeSourceWitness i).realShifts
  imagShifts _Z _T i := (recipeSourceWitness i).imagShifts

variable {K c R}

theorem recipeSourceSelectedMomentModel_slots
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (u : FrequencyRow K (places K c)) :
    (∏ j ∈ i.selected, (momentAmplitudeFor i).slotValue j u) =
      slotProduct (inverseModelFor (recipeMomentModels K c R) i u.sector)
        u.ideal.val (momentBaseFor i) 0 := by
  have hZ : 0 < Z := (by norm_num : (0 : ℝ) < 2 ^ (16 : ℕ)).trans_le
    (recipeMoment_scale_of_index i).1
  exact ((recipeSourceWitness i).selectedSlotProduct
    (P := probeData K c) (R := momentRowCharacters K c) (ω := c.family.omega)
    (recipeSourceAmplitude i).physical i.t T u.sector
    (momentBlockFor i).shell (recipeMoment_shell_pos i)
    i.selected u.ideal.val hZ).symm

variable (K c R)

/-- The fixed source and all three model families have literal calibration. -/
theorem recipeMoment_polynomial_calibration :
    SourcePolynomialCalibrationFor (momentRowCharacters K c) (recipeMomentModels K c R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z T i u _hu
    constructor <;>
      exact ExpansionRecipe.completeIdealRowCharacter_of_frequencyRow
        (P := probeData K c) (R := momentRowCharacters K c) u
  · intro Z T i s u I
    change completeIdealCommonMask K (places K c) u I = originalMomentMask (c := c) u I ∧
      completeIdealCommonMask K (places K c) u I = originalMomentMask (c := c) u I
    by_cases h : (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
      p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧ IsCoprime I u.val
    <;> simp [completeIdealCommonMask, originalMomentMask, h]
  · intro Z T i u _hu
    rfl
  · intro Z T i u _hu
    rfl
  · intro Z T i u _hu
    rfl
  · intro Z T i u _hu
    exact recipeSourceSelectedMomentModel_slots i u
  · intro Z T i u _hu
    exact recipeSourceSelectedMomentModel_slots i u
  · intro Z T i u _hu
    rfl

/-- Geometry of the same raw witnesses supplies both length and parameter
admissibility, with the original physical height and no reparameterization. -/
theorem recipeMomentModels_geometry {L : ℝ} (h : R.MomentGeometry L) :
    SourceWitnessLengthBoundFor (recipeMomentSourceData K c R) L ∧
      SourceMomentParameterControlFor (recipeMomentModels K c R) := by
  constructor
  · intro Z T i
    have hi := h Z T i.block i.label i.t i.t_lower i.t_upper i.subdivision
    exact ⟨hi.1, hi.2.1, hi.2.2.1⟩
  · intro Z T i
    exact (h Z T i.block i.label i.t i.t_lower i.t_upper i.subdivision).2.2.2

end HeckeSkeleton

#print axioms HeckeSkeleton.recipeMomentSourceData
#print axioms HeckeSkeleton.recipeMomentModels
#print axioms HeckeSkeleton.recipeMoment_polynomial_calibration
#print axioms HeckeSkeleton.recipeMoment_rowWidth_spec
#print axioms HeckeSkeleton.recipeMomentModels_geometry
