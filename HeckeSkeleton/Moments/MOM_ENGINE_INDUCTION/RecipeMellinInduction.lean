import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeInduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinCoreRecursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceConsumers

/-!
# The original recipe projections from scalar Mellin induction

The source recipe, original mesh and all selected-slot models stay fixed.
A certificate contains the literal source root and the actual primitive
inputs of `MellinCoreRecursionInput`. Its strict branch supplies canonical
outputs at each real Mellin frequency; the scalar strong induction has
already proved the resulting bound without a measurable kernel bind.

This module consumes that proved scalar bound directly. It neither
manufactures a `ClosedParentReduction` nor assumes a completed parent
estimate. The height degree and ceiling precede tau; one scalar and
threshold precede all original indices and sectors. The exact identity
`U ^ rowWidth = 2 * U` returns the result to the physical source exponent.

The actual ranked-annulus and canonical producer theorems must construct
the local certificates at the eventual source call site. No certificate
assumption is added to the main theorem, and this consumer does not claim
that those actual producer constructions have already been supplied.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.TIP
open scoped BigOperators Classical

universe u

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- The same literal recipe root with actual geometric, base, reflection,
Mellin and canonical strict inputs. No moment estimate is a field. -/
structure RecipeScalarLocalCertificate
    (indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (C H : ℝ) {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) where
  system : PolynomialSystem.{u} K c.family.omega (targetCharacter K c)
    (recipeInductionSigma c) 2
  root : system.Label
  root_eq : system.node root = recipeRoot R (indexMap Z T i) s
  parameterSpace : Type u
  parameterMeasurable : MeasurableSpace parameterSpace
  originalControl : ℝ
  admissible : MomentData K c.family.omega (targetCharacter K c) → RealParameters → Prop
  localInputs : @MellinCoreRecursionInput K _ _ c.family.omega (targetCharacter K c)
    parameterSpace parameterMeasurable (recipeInductionSigma c) 2 system
    (momentBaseFor i) T C H (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
    (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
    (sourceReserve c.family.lamA) originalControl admissible

variable {R}

/-- Undo normalization at the actual source root and spend the already
chosen mesh budget. The raw fourth moment is proved by scalar induction. -/
theorem RecipeScalarLocalCertificate.energy_bound
    {indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {C H Z T : ℝ}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (cert : RecipeScalarLocalCertificate.{u} R indexMap C H i s)
    (hH : 0 ≤ H) (hbase : momentBaseFor (indexMap Z T i) = momentBaseFor i) :
    pairedEnergy (pairedModelFor (recipeMomentModels K c R) (indexMap Z T i) s)
      (pairedParametersFor (indexMap Z T i)) (momentBaseFor (indexMap Z T i)) 0 ≤
      ((4 * C) * (1 + 4 * C) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1))) *
        momentBaseFor i ^ (rowWidthFor i + c.family.lamA) *
        (1 + T) ^ (H * ((6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) + 1)) := by
  letI := cert.parameterMeasurable
  have hU : 0 < momentBaseFor i := zero_lt_one.trans cert.localInputs.scale
  have hC : 0 ≤ 4 * C := mul_nonneg (by norm_num) cert.localInputs.coefficient_nonneg
  have hconstant : 0 ≤ (4 * C) *
      (1 + 4 * C) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1)) :=
    mul_nonneg hC (pow_nonneg (by linarith) _)
  have hnorm := cert.localInputs.energy_bound hH
    (recipeInduction_budget (c := c)).2.1 cert.root
  change (cert.system.node cert.root).energy (momentBaseFor i) 0 /
    momentBaseFor i ^ (cert.system.node cert.root).width ≤ _ at hnorm
  have hraw := (div_le_iff₀
    (Real.rpow_pos_of_pos hU (cert.system.node cert.root).width)).mp hnorm
  have hraw' : (cert.system.node cert.root).energy (momentBaseFor i) 0 ≤
      ((4 * C) * (1 + 4 * C) ^ (6 * (widthBand (recipeInductionSigma c) 2 + 1))) *
        momentBaseFor i ^ ((cert.system.node cert.root).width +
          recipeInductionTerminalLoss c +
          (6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) * recipeInductionEdgeLoss c) *
        (1 + T) ^ (H * ((6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) + 1)) := by
    apply hraw.trans_eq
    rw [show (cert.system.node cert.root).width + recipeInductionTerminalLoss c +
        (6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) * recipeInductionEdgeLoss c =
        (cert.system.node cert.root).width + (recipeInductionTerminalLoss c +
          (6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) * recipeInductionEdgeLoss c) by ring,
      Real.rpow_add hU (cert.system.node cert.root).width
        (recipeInductionTerminalLoss c +
          (6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) * recipeInductionEdgeLoss c)]
    ring
  have hw : (cert.system.node cert.root).width = rowWidthFor i := by
    rw [cert.root_eq, recipeRoot_width]
    unfold rowWidthFor
    rw [hbase]
  rw [hw, cert.root_eq, recipeRoot, Node.ordinary_energy] at hraw'
  rw [hbase]
  apply hraw'.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le cert.localInputs.scale.le
      have hbudget := (recipeInduction_budget (c := c)).2.2
      linarith
    · exact hconstant
  · exact Real.rpow_nonneg (by linarith [cert.localInputs.height_nonneg]) _

variable (R)

/-- Uniform local producers in the original source quantifier order.
The height degree and ceiling are chosen before tau, and the certificates
contain primitive local outputs rather than their final scalar estimate. -/
structure RecipeScalarLocalInput
    (indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (eligible : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → Prop) where
  heightDegree : ℝ
  ceiling : ℝ
  heightDegree_nonneg : 0 ≤ heightDegree
  ceiling_pos : 0 < ceiling
  families : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
    ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z (Z ^ τ),
          51 / 100 < (momentBlockFor i).bin → eligible Z (Z ^ τ) i →
            ∀ s : SixthUnitClasses K (places K c),
              Nonempty (RecipeScalarLocalCertificate.{u} R indexMap C heightDegree i s)

variable {R}

/-- The scalar finite-rank theorem gives the actual sector estimate
directly. No common measurable bind for frequency-dependent kernels is
constructed or required. -/
theorem RecipeScalarLocalInput.sectorBound
    {indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {eligible : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → Prop}
    (input : RecipeScalarLocalInput.{u} R indexMap eligible)
    (hbase : ∀ Z T (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T),
      momentBaseFor (indexMap Z T i) = momentBaseFor i) :
    (sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)).SectorBound
      indexMap eligible := by
  let N : ℕ := 6 * (widthBand (recipeInductionSigma c) 2 + 1)
  refine ⟨input.heightDegree * ((N : ℝ) + 1), input.ceiling,
    mul_nonneg input.heightDegree_nonneg (by positivity), input.ceiling_pos, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hcert⟩ := input.families τ hτ hτc
  have hC₄ : 0 ≤ 4 * C := mul_nonneg (by norm_num) hC
  refine ⟨Z₀, (4 * C) * (1 + 4 * C) ^ N, hZ₀,
    mul_nonneg hC₄ (pow_nonneg (by linarith) _), ?_⟩
  intro Z hZ i hbin helig s
  obtain ⟨cert⟩ := hcert Z hZ i hbin helig s
  exact cert.energy_bound input.heightDegree_nonneg (hbase Z (Z ^ τ) i)

variable (R)

local instance : Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The unrestricted zero-slot projection for the same recipe and the
same no-slot model. It has no plain-length capacity premise. -/
theorem paired_zero_slot_recipe_mellin
    (input : RecipeScalarLocalInput.{u} R (fun _ _ i => i.noSlots) (fun _ _ _ => True)) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i.noSlots)
      (fun _ _ i => rowWidthFor i) (fun _ _ _ => True) := by
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.zeroSlotBound_of_sectorBound (input.sectorBound (fun _ _ _ => rfl))

/-- The below-one producer receives the original prime-product premise;
all original finite sectors are summed only after the scalar induction. -/
theorem paired_positive_recipe_mellin_below_one
    (hB : c.family.B < 1)
    (hprime : PairedPrimeProductBoundFor (recipeMomentModels K c R) (2 * c.family.B - 1))
    (producers : c.family.B < 1 →
      PairedPrimeProductBoundFor (recipeMomentModels K c R) (2 * c.family.B - 1) →
        Nonempty (RecipeScalarLocalInput.{u} R (fun _ _ i => i)
          (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  obtain ⟨input⟩ := producers hB hprime
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.positiveSlotBound_of_sectorBound (input.sectorBound (fun _ _ _ => rfl))

/-- The endpoint uses kappa one and the existing absolute prime-product
premise, without a below-one or zero-free condition. -/
theorem paired_positive_recipe_mellin_endpoint
    (hB : c.family.B = 1)
    (hprime : PairedPrimeProductBoundFor (recipeMomentModels K c R) 1)
    (producers : c.family.B = 1 → PairedPrimeProductBoundFor (recipeMomentModels K c R) 1 →
      Nonempty (RecipeScalarLocalInput.{u} R (fun _ _ i => i)
        (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  obtain ⟨input⟩ := producers hB hprime
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.positiveSlotBound_of_sectorBound (input.sectorBound (fun _ _ _ => rfl))

/-- The literal recipe row cutoff equals twice the physical base. This
only multiplies the scalar by two and retains the height degree, ceiling,
threshold, model, no-slot projection and index quantifiers. -/
theorem uniformMomentBound_recipe_physical
    (E : ∀ Z T, SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → Prop)
    (h : UniformMomentBoundFor E (fun _ _ i => rowWidthFor i) eligible) :
    UniformMomentBoundFor E (fun _ _ _ => 1) eligible := by
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  apply F.uniformBound_of_rowWidth_le E eligible (D := 2) (by norm_num) ?_ h
  intro Z T i _hZ
  exact ⟨(by norm_num : (0 : ℝ) < 2).trans_le (recipeMomentBase_ge_two i),
    (recipeMoment_rowWidth_spec i).2.2.le⟩

/-- Return the two actual scalar-induction projections to the physical
source for the same expansion. Polynomial calibration is the recipe's
proved literal calibration; only primitive witness-row eligibility is
supplied. This is a consumer, not a new assumption on the main theorem. -/
theorem plainSource_recipe_mellin
    (positive : RecipeScalarLocalInput.{u} R (fun _ _ i => i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))
    (zero : RecipeScalarLocalInput.{u} R (fun _ _ i => i.noSlots) (fun _ _ _ => True))
    (D : TargetData K c.geometry)
    (hplaces : D.S = excludedPlaces K c)
    (hexpansion : expansionAtPlaces D hplaces = (recipeMomentSourceData K c R).expansion)
    (hrows : SourceRowEligibilityFor (recipeMomentModels K c R)) :
    PSource c.geometry D c.family.B c.family.lamA (momentMesh K c.family).val := by
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  have hpositive : UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) :=
    F.positiveSlotBound_of_sectorBound (positive.sectorBound (fun _ _ _ => rfl))
  exact plainSource_of_model_bounds (recipeMomentModels K c R) D hplaces hexpansion
    (uniformMomentBound_recipe_physical R _ _ hpositive)
    (uniformMomentBound_recipe_physical R _ _ (paired_zero_slot_recipe_mellin R zero))
    (recipeMoment_polynomial_calibration K c R) hrows

end HeckeSkeleton.Moments.EngineInduction.Source
