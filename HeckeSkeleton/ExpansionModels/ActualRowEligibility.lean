import HeckeSkeleton.ExpansionModels.SourceData
import Expansion.PhysicalRecipeOrigins
import Expansion.CanonicalModelExclusion
import ArithmeticFrequencyRowRamification

/-!
# Row eligibility of the same actual all-scale recipe

The all-label provenance of the raw physical recipe places every amplitude
row in its original strict dyadic shell.  The existing active-scale guard
gives U ≥ 2, so the sixth-power-free base ideal is never the unit ideal.
The actual ramification theorem then excludes the entire canonical theta
family, whose members are unramified outside the target's original S.

This is an all-scale statement about the original source, including copied
padding labels and default witnesses.  No eventual cutoff, alternative
model, calibration hypothesis or row-eligibility hypothesis is introduced.
The final theorem fills the unchanged SourceRowEligibilityFor predicate.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  expansionNormOneSpace expansionNormOneBorel expansionLocalHaar

local instance actualEligibility_sectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

local notation "Raw" => expansionRecipeRaw K c
local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)
local notation "q" => expansionPhysicalParameters K c
local notation "Eactual" => HighBinActualEuler.arithmeticHighEulerData K (places K c)
  (probeData K c) (targetCharacter K c)

variable {Z T : ℝ}

/-- The same actual source has the already proved uniform length bound
and exactly the original height/shift quantification region. -/
theorem actualRecipeSourceGeometry :
    SourceWitnessLengthBoundFor Source 22 ∧ SourceMomentParameterControlFor Models :=
  recipeMomentModels_geometry K c (Raw) (expansionRecipeRaw_geometry K c)

/-- Every label of the same actual source has the strict lower shell
bound.  The origin theorem includes the copied padding labels. -/
theorem actualRecipeAmplitude_norm_range (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentAmplitudeFor i).rows) :
    momentBaseFor i < frequencyRowNorm K (places K c) u ∧
      frequencyRowNorm K (places K c) u ≤ 2 * momentBaseFor i := by
  let b := (Raw).rawBlockIndex Z T i.block
  let j := physicalRecipeShellIndex K (places K c) c.family.B (q).e
    (expansionShellAllowance K c) Z b
  let a := physicalRecipeChoice K (places K c) c.family.B (q).e
    (expansionShellAllowance K c) Z b
  have hscale := recipeMoment_scale_of_index i
  have hZ : 1 < Z := (by norm_num : (1 : ℝ) < 2 ^ (16 : ℕ)).trans_le hscale.1
  have hT : 0 ≤ T := zero_le_one.trans hscale.2
  have hfixed := physicalRecipeScheduledBlock_rows_subset K (places K c) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry Eactual
    (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
    (q).e_pos c.family.boundary (probeMeasures K c).haar ∅ c.family.lamA
    (expansionShellAllowance K c) (q).width (q).k (q).width_pos Z T hZ hT j a i.label
  have hr := physicalRecipeRows_spec K (places K c) (probeData K c) Eactual
    c.family.omega (targetCharacter K c) (representative K c).val.property
    (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
    (expansionShellAllowance K c) Z T hZ j a u (hfixed hu)
  exact ⟨hr.1, hr.2.1⟩

/-- A witness subdivision retains the actual amplitude row set. -/
theorem actualRecipeWitness_mem_amplitude (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    u ∈ (momentAmplitudeFor i).rows := by
  change u ∈ (((recipeSourceAmplitude i).toAmplitude (P := probeData K c)
    (R := momentRowCharacters K c) (ω := c.family.omega) Z T (momentBaseFor i)).subdivision
      i.t i.subdivision).rows at hu
  have hmem : u ∈ (recipeSourceAmplitude i).rows (momentBaseFor i) ∧
      (recipeSourceAmplitude i).witnessChoice i.t u = i.subdivision := by
    simpa only [RecipeAmplitudeData.toAmplitude, RecipeWitnessData.toWitness, Finset.mem_filter]
      using hu
  exact hmem.1

theorem actualRecipeWitness_norm_range (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    momentBaseFor i < frequencyRowNorm K (places K c) u ∧
      frequencyRowNorm K (places K c) u ≤ 2 * momentBaseFor i :=
  actualRecipeAmplitude_norm_range K c i u (actualRecipeWitness_mem_amplitude K c i u hu)

/-- The cutoff applies to the sixth-free base itself, at every active
scale.  No conclusion is inferred only from a sixth-power descendant. -/
theorem actualRecipeWitness_ideal_ne_one (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    u.ideal.val ≠ 1 := by
  intro hunit
  have hnorm : frequencyRowNorm K (places K c) u = 1 := by
    change idealNorm K u.ideal.val = 1
    rw [hunit]
    simp [idealNorm]
  have hlower := (actualRecipeWitness_norm_range K c i u hu).1
  have hbase := recipeMomentBase_ge_two i
  linarith

/-- Every member of the exact new canonical theta set is unramified
outside the original target S, including psi and its inverse. -/
theorem actualCanonicalTheta_unramified (theta : HeckeCharacter K)
    (htheta : theta ∈ canonicalDetectorTheta K (targetCharacter K c))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K theta p := by
  by_cases hfinite : FiniteOrder (targetCharacter K c)
  · simp only [canonicalDetectorTheta, if_pos hfinite, Finset.mem_insert,
      Finset.mem_singleton] at htheta
    rcases htheta with rfl | rfl | rfl
    · exact unramifiedAt_one K p
    · exact target_unramified_outside K c p hp
    · exact UnramifiedAt.inv K (target_unramified_outside K c p hp)
  · have hone : theta = 1 := by
      simpa only [canonicalDetectorTheta, if_neg hfinite, Finset.mem_singleton] using htheta
    subst theta
    exact unramifiedAt_one K p

/-- Literal arithmetic exclusion, before considering either paired-row
branch.  It applies to every original subdivision and every source label. -/
theorem actualRecipeWitness_character_not_theta (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    (momentRowCharacters K c).character u ∉ canonicalDetectorTheta K (targetCharacter K c) :=
  arithmeticRowCharacterInput_not_mem_unramified_family_of_ideal_ne_one K (places K c)
    (probeData K c) u (actualRecipeWitness_ideal_ne_one K c i u hu)
    (canonicalDetectorTheta K (targetCharacter K c)) (actualCanonicalTheta_unramified K c)

/-- Restricting slots and changing their base preserve the actual theta
family; it is independent of the finite presentation code. -/
theorem actualRecipeMoment_theta (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c)) :
    (pairedModelFor Models i s).theta = canonicalDetectorTheta K (targetCharacter K c) := rfl

/-- The original zero-slot branch excludes the principal plain character,
using the same finite-background filter and the same actual row character. -/
theorem actualRecipeMoment_plain_ne_one (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    (pairedModelFor Models i u.sector).plainBackground *
      (pairedModelFor Models i u.sector).rowCharacter u.ideal.val ≠ 1 := by
  let xi := (Models).heights Z T i
  let j : Fin 2 := _root_.ExpansionRecipe.decodePresentation 2 (by norm_num) (xi 4)
  change (canonicalDetectorPresentation K (targetCharacter K c) j).plainBackground *
    completeIdealRowCharacter K (places K c) (probeData K c) (momentRowCharacters K c)
      u.sector u.ideal.val ≠ 1
  rw [completeIdealRowCharacter_of_frequencyRow (P := probeData K c)
    (R := momentRowCharacters K c) u]
  exact canonicalDetector_plain_ne_one K (targetCharacter K c) j
    ((momentRowCharacters K c).character u) ((momentRowCharacters K c).finite_order u)
    (actualRecipeWitness_character_not_theta K c i u hu)

/-- The original complete-ideal ball contains the actual dyadic shell.
Only the existing row-enumeration exponent absorbs its factor of two. -/
theorem actualRecipeMoment_inverse_rows (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    u.ideal.val ∈ (inverseModelFor Models i u.sector).rows
      (momentBaseFor i ^ (inverseParametersFor i).m) := by
  apply ((inverseModelFor Models i u.sector).rows_spec _ u.ideal.val).mpr
  refine ⟨u.ideal.property, ?_⟩
  change idealNorm K u.ideal.val ≤ momentBaseFor i ^ rowWidthFor i
  rw [(recipeMoment_rowWidth_spec i).2.2]
  exact (actualRecipeWitness_norm_range K c i u hu).2

/-- Both original paired-row branches hold for all actual labels. -/
theorem actualRecipeMoment_paired_rows (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    u.ideal.val ∈ pairedRows (pairedModelFor Models i u.sector)
      (pairedParametersFor i) (momentBaseFor i) := by
  unfold pairedRows
  apply Finset.mem_filter.mpr
  constructor
  · simpa only [pairedParametersFor, inverseParametersFor, add_zero] using
      actualRecipeMoment_inverse_rows K c i u hu
  · by_cases hz : (pairedParametersFor i).z = 0
    · simp only [hz, if_pos]
      exact actualRecipeMoment_plain_ne_one K c i u hu
    · simp only [hz, if_neg]
      rw [actualRecipeMoment_theta]
      have hchar := (recipeMoment_polynomial_calibration K c (Raw)).character Z T i u hu
      rw [hchar.2]
      exact actualRecipeWitness_character_not_theta K c i u hu

theorem actualRecipeMoment_unmarked_rows (i : SourceMomentIndexFor K c Source Z T)
    (u : FrequencyRow K (places K c)) (hu : u ∈ (momentWitnessFor i).rows) :
    u.ideal.val ∈ (unmarkedModelFor Models i u.sector).rows (2 * momentBaseFor i) ∧
      SixthPowerFreeIdeal (K := K) u.ideal.val := by
  constructor
  · apply ((unmarkedModelFor Models i u.sector).rows_spec _ u.ideal.val).mpr
    exact ⟨u.ideal.property, (actualRecipeWitness_norm_range K c i u hu).2⟩
  · simpa only [sixthPowerFreePart_of_frequencyRow u] using
      (sixthPowerFreePart_isSixthPowerFree u.ideal.val)

theorem actualRecipeMoment_selectedLength_nonneg (i : SourceMomentIndexFor K c Source Z T) :
    0 ≤ selectedLengthFor i := by
  have hd := (recipeMoment_shell_pos i).le
  have hJ : (0 : ℝ) ≤ c.geometry.slots := Nat.cast_nonneg _
  change 0 ≤ ∑ _j ∈ i.selected, (1 / 6 : ℝ) /
    ((c.geometry.slots : ℝ) * (momentBlockFor i).shell)
  apply Finset.sum_nonneg
  intro j _hj
  exact div_nonneg (by norm_num) (mul_nonneg hJ hd)

theorem actualRecipeMoment_inverse_region (i : SourceMomentIndexFor K c Source Z T)
    (hcap : inverseCapacityFor i) : MIRegion (inverseParametersFor i) := by
  have hw := (recipeMoment_rowWidth_spec i).1
  have hlength := (actualRecipeSourceGeometry K c).1 Z T i
  have hz := actualRecipeMoment_selectedLength_nonneg K c i
  rcases hcap with ⟨hcap1, hcap2⟩
  change 0 ≤ rowWidthFor i ∧ 0 ≤ (momentWitnessFor i).inverseLength ∧
    0 ≤ selectedLengthFor i ∧
    (momentWitnessFor i).inverseLength + 2 * selectedLengthFor i < rowWidthFor i ∧
    2 * (momentWitnessFor i).inverseLength + 8 * selectedLengthFor i < 3 * rowWidthFor i
  exact ⟨by linarith, hlength.1, hz, by linarith [c.family.lamA_pos],
    by linarith [c.family.lamA_pos]⟩

theorem actualRecipeMoment_paired_region (i : SourceMomentIndexFor K c Source Z T)
    (hcap : pairedCapacityFor i) : ExtendedPRegionFor (pairedParametersFor i) := by
  have hw := (recipeMoment_rowWidth_spec i).1
  have hz := actualRecipeMoment_selectedLength_nonneg K c i
  have hcap' := hcap.2
  change 3 / 4 ≤ 2 * c.family.B - 1 ∧ 2 * c.family.B - 1 ≤ 1 ∧
    (selectedLengthFor i = 0 ∨
      (0 < selectedLengthFor i ∧
        (momentWitnessFor i).plainLength + (momentWitnessFor i).plainLength +
          6 * (2 * c.family.B - 1) * selectedLengthFor i ≤ rowWidthFor i + 0))
  refine ⟨by linarith [c.family.B_lower], by linarith [c.family.B_upper], ?_⟩
  rcases eq_or_lt_of_le hz with hz | hz
  · exact Or.inl hz.symm
  · exact Or.inr ⟨hz, by linarith⟩

/-- The selected slot lengths are exactly the original physical lengths
after the already defined change from Z to its shell base U. -/
theorem actualRecipeMoment_geometry (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c)) :
    (inverseModelFor Models i s).geometry.totalLength = selectedLengthFor i ∧
      (pairedModelFor Models i s).geometry.totalLength = selectedLengthFor i := by
  have hlength : (inverseModelFor Models i s).geometry.totalLength = selectedLengthFor i := by
    change (∑ _j : Fin i.selected.card,
      ((1 / 6 : ℝ) / c.geometry.slots) / (momentBlockFor i).shell) =
        ∑ _j ∈ i.selected, (1 / 6 : ℝ) /
          ((c.geometry.slots : ℝ) * (momentBlockFor i).shell)
    rw [selectedSlots_sum i.selected
      (fun _ : Fin c.geometry.slots => ((1 / 6 : ℝ) / c.geometry.slots) / (momentBlockFor i).shell)]
    apply Finset.sum_congr rfl
    intro j _hj
    exact div_div (1 / 6 : ℝ) (c.geometry.slots : ℝ) (momentBlockFor i).shell
  exact ⟨hlength, hlength⟩

theorem actualRecipeMoment_paired_finite_slots (i : SourceMomentIndexFor K c Source Z T)
    (s : SixthUnitClasses K (places K c))
    (j : Fin (pairedModelFor Models i s).geometry.slotCount) :
    FiniteOrder ((pairedModelFor Models i s).slotCoefficient j) := by
  change FiniteOrder (1 : HeckeCharacter K)
  exact IsOfFinOrder.one

/-- Full eligibility for the original raw data.  All scale, label and
subdivision quantifiers are the original SourceRowEligibilityFor ones. -/
theorem actualRecipeRowEligibility : SourceRowEligibilityFor Models := by
  refine
    { inverse_region := fun _ _ i => actualRecipeMoment_inverse_region K c i
      paired_region := fun _ _ i => actualRecipeMoment_paired_region K c i
      inverse_rows := fun _ _ i => actualRecipeMoment_inverse_rows K c i
      paired_rows := fun _ _ i => actualRecipeMoment_paired_rows K c i
      unmarked_rows := fun _ _ i => actualRecipeMoment_unmarked_rows K c i
      fiber := (frequencyRowIdealSectorEmbedding (K := K) (S := places K c)).injective
      geometry := fun _ _ i => actualRecipeMoment_geometry K c i
      paired_finite_slots := fun _ _ i => actualRecipeMoment_paired_finite_slots K c i }

end HeckeSkeleton

#print axioms HeckeSkeleton.actualRecipeAmplitude_norm_range
#print axioms HeckeSkeleton.actualRecipeSourceGeometry
#print axioms HeckeSkeleton.actualRecipeWitness_character_not_theta
#print axioms HeckeSkeleton.actualRecipeMoment_paired_rows
#print axioms HeckeSkeleton.actualRecipeRowEligibility
