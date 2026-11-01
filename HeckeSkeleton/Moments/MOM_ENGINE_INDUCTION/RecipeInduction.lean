import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreRecursion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Induction

/-!
# The three source projections from actual local engine and reflection calls

The source recipe is fixed once. The mesh, step, width limit and complete
loss budget are the already chosen source parameters. The external input
supplies the genuine local analytic producers on their actual domains,
with the original profile control and uniform order of constants.

The construction here performs the geometric case split, closes its base
components, constructs the finite-rank root certificate, applies induction,
and sums all original sectors. A completed `ParentReductionInput`, child
moment estimate or final source bound is not an input.

The actual named recipe and actual producing/reflection theorems must still
be supplied by their owners when the original skeleton caller is migrated.
No admitted actual specialization is introduced here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical

universe u

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

def recipeInductionSigma (c : TargetContext K) : ℝ :=
  HeckePort.Schedule.amplification c.family.lamA

def recipeInductionEdgeLoss (c : TargetContext K) : ℝ :=
  sourceReserve c.family.lamA + (momentMesh K c.family).val + sourceReserve c.family.lamA

def recipeInductionTerminalLoss (c : TargetContext K) : ℝ :=
  terminalBudget (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
    (recipeInductionSigma c) (sourceReserve c.family.lamA)

/-- The original preselected mesh pays for all three proof stages and
both slot regimes, without changing any source geometry. -/
theorem recipeInduction_budget :
    0 < recipeInductionSigma c ∧ 0 ≤ recipeInductionEdgeLoss c ∧
      recipeInductionTerminalLoss c +
        (6 * (widthBand (recipeInductionSigma c) 2 + 1) : ℕ) *
          recipeInductionEdgeLoss c ≤ c.family.lamA := by
  obtain ⟨hσ, hr, hmesh, _, _⟩ := moment_mesh_engine_bounds c.family.lamA_pos
  refine ⟨hσ, ?_, ?_⟩
  · unfold recipeInductionEdgeLoss momentMesh
    change 0 ≤ sourceReserve c.family.lamA +
      HeckePort.Schedule.momentMeshValue c.family.lamA + sourceReserve c.family.lamA
    linarith
  · exact (moment_mesh_total_loss_budget c.family.lamA_pos).le

variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- One actual source root and its local analytic producers. The complete
recursion and its uniform bound are constructed from these inputs below. -/
structure RecipeLocalCertificate
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
  localInputs : @CoreRecursionInput K _ _ c.family.omega (targetCharacter K c)
    parameterSpace parameterMeasurable (recipeInductionSigma c) 2 system
    (momentBaseFor i) T C H (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
    (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
    (sourceReserve c.family.lamA) originalControl admissible

variable {R}

/-- The root's whole polynomial identity is retained while the local
case construction supplies the closed reduction and its factor four. -/
def RecipeLocalCertificate.toRootCertificate
    {indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {C H Z T : ℝ}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (cert : RecipeLocalCertificate.{u} R indexMap C H i s) :
    RootCertificate.{u}
      (sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R))
      indexMap (recipeInductionSigma c) 2 (4 * C) H
      (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c) i s where
  system := cert.system.withCoreStages (recipeInductionSigma c / 16)
  root := cert.root
  root_eq := cert.root_eq
  base_one_le := (by norm_num : (1 : ℝ) ≤ 2).trans (recipeMomentBase_ge_two i)
  step := by
    letI := cert.parameterMeasurable
    exact cert.localInputs.toClosedParentReduction

variable (R)

/-- The analytic producers choose one height degree and ceiling before
tau, then one scalar and threshold before every original index and sector.
The remaining fields contain local canonical outputs, actual reflection
integrals and primitive family calibration, rather than a final moment
bound or an all-node reduction. -/
structure RecipeLocalInput
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
              Nonempty (RecipeLocalCertificate.{u} R indexMap C heightDegree i s)

variable {R}

/-- Uniform local producers are assembled into the parent input here,
including the fixed loss schedule and the actual root identification. -/
def RecipeLocalInput.toParentReductionInput
    {indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {eligible : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → Prop}
    (input : RecipeLocalInput.{u} R indexMap eligible)
    (hbase : ∀ Z T (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T),
      momentBaseFor (indexMap Z T i) = momentBaseFor i) :
    ParentReductionInput.{u}
      (sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R))
      indexMap eligible where
  sigma := recipeInductionSigma c
  widthLimit := 2
  heightDegree := input.heightDegree
  terminalLoss := recipeInductionTerminalLoss c
  edgeLoss := recipeInductionEdgeLoss c
  ceiling := input.ceiling
  sigma_pos := (recipeInduction_budget (c := c)).1
  heightDegree_nonneg := input.heightDegree_nonneg
  edgeLoss_nonneg := (recipeInduction_budget (c := c)).2.1
  ceiling_pos := input.ceiling_pos
  loss_budget := (recipeInduction_budget (c := c)).2.2
  base_at := hbase
  certificates := by
    intro τ hτ hc
    obtain ⟨Z₀, C, hZ₀, hC, hf⟩ := input.families τ hτ hc
    refine ⟨Z₀, 4 * C, hZ₀, by positivity, ?_⟩
    intro Z hZ i hbin helig s
    obtain ⟨cert⟩ := hf Z hZ i hbin helig s
    exact ⟨cert.toRootCertificate⟩

variable (R)

local instance recipeInductionSectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The unrestricted zero-slot conclusion for the same explicit recipe.
Ordinary reflection is performed by the actual local case construction;
no bound on the sum of the root's plain lengths is imposed. -/
theorem paired_zero_slot_recipe
    (input : RecipeLocalInput.{u} R (fun _ _ i => i.noSlots) (fun _ _ _ => True)) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i.noSlots)
      (fun _ _ i => rowWidthFor i) (fun _ _ _ => True) := by
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.zeroSlotBound_of_sectorBound
    (input.toParentReductionInput (fun _ _ _ => rfl)).sectorBound

/-- The original below-one prime premise is passed to the actual local
producer family. The induction itself is the same three-stage argument. -/
theorem paired_positive_recipe_below_one
    (hB : c.family.B < 1)
    (hprime : PairedPrimeProductBoundFor (recipeMomentModels K c R) (2 * c.family.B - 1))
    (producers : c.family.B < 1 →
      PairedPrimeProductBoundFor (recipeMomentModels K c R) (2 * c.family.B - 1) →
        Nonempty (RecipeLocalInput.{u} R (fun _ _ i => i)
          (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  obtain ⟨input⟩ := producers hB hprime
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.positiveSlotBound_of_sectorBound
    (input.toParentReductionInput (fun _ _ _ => rfl)).sectorBound

/-- The endpoint uses exactly kappa=1 and has no below-one or zero-free
premise. Its local producers receive only the absolute prime-product input. -/
theorem paired_positive_recipe_endpoint
    (hB : c.family.B = 1)
    (hprime : PairedPrimeProductBoundFor (recipeMomentModels K c R) 1)
    (producers : c.family.B = 1 → PairedPrimeProductBoundFor (recipeMomentModels K c R) 1 →
      Nonempty (RecipeLocalInput.{u} R (fun _ _ i => i)
        (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))) :
    UniformMomentBoundFor
      (fun _ _ i => pairedModelEnergyFor (recipeMomentModels K c R) i)
      (fun _ _ i => rowWidthFor i)
      (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty) := by
  obtain ⟨input⟩ := producers hB hprime
  let F := sourceFamily K c (recipeMomentSourceData K c R) (recipeMomentModels K c R)
  exact F.positiveSlotBound_of_sectorBound
    (input.toParentReductionInput (fun _ _ _ => rfl)).sectorBound

end HeckeSkeleton.Moments.EngineInduction.Source
