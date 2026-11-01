import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CoverHybridPhaseIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

/-!
# The actual covered second source has a literal finite leaf carrier

The carrier retains the actual common pair, outer mask divisor, both
original Cartesian-cover keys, row label, both second support keys,
inner Möbius divisor, finite phase and both full occurrence allocations.
All data precede either continuous Fourier variable.  Each leaf uses
the original full-source physical row set and the same two kernels.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance actualGaussFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

private theorem sourceLeftCoefficient_withMultiplier
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι) :
    ((s.withMultiplier u).charts DE D).sourceLeftCoefficient i =
      u i * (s.charts DE D).sourceLeftCoefficient i := by
  change (u i * (s.charts DE D).leftCoefficient i) * _ =
    u i * ((s.charts DE D).leftCoefficient i * _)
  exact mul_assoc _ _ _

private theorem sourceRightCoefficient_withMultiplier
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι) :
    ((s.withMultiplier u).charts DE D).sourceRightCoefficient i =
      u i * (s.charts DE D).sourceRightCoefficient i := by
  change (u i * (s.charts DE D).rightCoefficient i) * _ =
    u i * ((s.charts DE D).rightCoefficient i * _)
  exact mul_assoc _ _ _

/-- The seven source-class labels are exactly those in
`coverHybridNonzeroCost`; no bounded surrogate carrier is substituted. -/
abbrev CoveredClassKey :=
  Σ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    Σ D : s.mask.powerset,
    Σ a : LC.labels, Σ e : RC.labels,
    Σ label : Fin ((s.charts DE D).rowLabelCount + 1),
      (LC.branch a).labels (primeSupport DE.val.1) DE.val.1 ×
        (RC.branch e).labels (primeSupport DE.val.1) DE.val.2

namespace CoveredClassKey

variable {s LC RC}
variable (v : s.CoveredClassKey LC RC)

abbrev block :=
  canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal v.1.val v.1.property

abbrev chart := s.charts v.1 v.2.1

abbrev rowLabel := v.2.2.2.2.1

abbrev leftReindex :=
  (LC.branch v.2.2.1).residualReindex (primeSupport v.1.val.1) v.1.val.1
    v.block.leftResidual (fun i _ => v.block.left_residual i) v.2.2.2.2.2.1

abbrev rightReindex :=
  (RC.branch v.2.2.2.1).residualReindex (primeSupport v.1.val.1) v.1.val.2
    v.block.rightResidual (fun j _ => v.block.right_residual j) v.2.2.2.2.2.2

abbrev leftSlots :=
  ((LC.branch v.2.2.1).branch (primeSupport v.1.val.1) v.1.val.1
    v.2.2.2.2.2.1).keep.card

abbrev AllocationKey :=
  HybridAllocationLabel v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
    (fun j => (v.block.rightResidual (v.rightReindex.index j)).val)
    v.leftSlots ((PUnit × PUnit) →* Circle)

def leaf (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : v.AllocationKey) :
    ActualHybridLeaf K Q W E :=
  fullCorrelationHybridLeaf F v.chart.kernel
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).rows
    v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
    v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
    (fun i => (v.block.rightResidual (v.rightReindex.index i)).val)
    (fun h =>
      (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).weight h *
        generatedIdealCorrelation (σ := σ) v.block.commonLeftIdeal v.block.commonRightIdeal
          (engineAllowedGenerator C v.block.commonLeftIdeal)
          (engineAllowedGenerator C v.block.commonRightIdeal)
          (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
          ((v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency h))
    (fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)))
    (fun χ h i => v.chart.sourceLeftCoefficient (v.leftReindex.index i) *
      (fixedLeftPhase PUnit χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (v.block.leftResidual (v.leftReindex.index i))
          ((v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency h)))
    (fun χ h i => v.chart.sourceRightCoefficient (v.rightReindex.index i) *
      (fixedRightPhase PUnit χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (v.block.rightResidual (v.rightReindex.index i))
          (-((v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency h))))
    (fun _ i => x (v.leftReindex.index i))
    (fun h i => v.chart.leftPoint h (v.leftReindex.index i))
    (fun _ i => x (v.rightReindex.index i))
    (fun h i => v.chart.rightPoint h (v.rightReindex.index i))
    (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
      v.2.2.2.2.2.1 v.2.2.2.2.2.2) j

@[simp] theorem leaf_firstKernel (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : v.AllocationKey) :
    (v.leaf exceptional F x j).firstKernel = F := rfl

private theorem phase_mul_four_factors (phase a b c d : ℂ) :
    (((phase * a) * b) * c) * d = (((a * b) * c) * d) * phase := by
  ring

private theorem phase_mul_three_factors (phase a b c : ℂ) :
    ((phase * a) * b) * c = ((a * b) * c) * phase := by
  ring

/-- This is the actual phase multiplication from the first transform,
followed by the literal finite allocation sum from the second. -/
theorem phase_class_eq_leaf_sum (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost s.mask s.cutoff s.cutoff_one v.rowLabel
        v.leftReindex v.rightReindex
        (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) =
      ∑ j : v.AllocationKey, (v.leaf exceptional F x j).firstPhaseCost ξ := by
  let rows := v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel
  let rightSlots := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1)
    v.1.val.2 v.2.2.2.2.2.2).keep.card
  let rowWeight : Q → ℂ := fun h => rows.weight h *
    generatedIdealCorrelation (σ := σ) v.block.commonLeftIdeal v.block.commonRightIdeal
      (engineAllowedGenerator C v.block.commonLeftIdeal)
      (engineAllowedGenerator C v.block.commonRightIdeal)
      (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
      (rows.frequency h)
  let c : ((PUnit × PUnit) →* Circle) → Q → AllocationColumn K v.leftSlots → ℂ :=
    fun χ h i => v.chart.sourceLeftCoefficient (v.leftReindex.index i) *
      (fixedLeftPhase PUnit χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (v.block.leftResidual (v.leftReindex.index i)) (rows.frequency h))
  let d : ((PUnit × PUnit) →* Circle) → Q → AllocationColumn K rightSlots → ℂ :=
    fun χ h i => v.chart.sourceRightCoefficient (v.rightReindex.index i) *
      (fixedRightPhase PUnit χ PUnit.unit : ℂ) *
        σ (A.sexticResidue (v.block.rightResidual (v.rightReindex.index i)) (-rows.frequency h))
  let phasedLeft := fun χ h i => c χ h i * jointPhase ξ (x (v.leftReindex.index i))
  let phasedRight := fun χ h i => d χ h i * jointPhase ξ (x (v.rightReindex.index i))
  let multipliedLeft : ((PUnit × PUnit) →* Circle) → Q →
      AllocationColumn K v.leftSlots → ℂ := fun χ h i =>
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).sourceLeftCoefficient
        (v.leftReindex.index i) * (fixedLeftPhase PUnit χ PUnit.unit : ℂ) *
      σ (A.sexticResidue (v.block.leftResidual (v.leftReindex.index i)) (rows.frequency h))
  let multipliedRight : ((PUnit × PUnit) →* Circle) → Q →
      AllocationColumn K rightSlots → ℂ := fun χ h i =>
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).sourceRightCoefficient
        (v.rightReindex.index i) * (fixedRightPhase PUnit χ PUnit.unit : ℂ) *
      σ (A.sexticResidue (v.block.rightResidual (v.rightReindex.index i)) (-rows.frequency h))
  let cost (carrier : Finset Q)
      (leftCoefficient : ((PUnit × PUnit) →* Circle) → Q → AllocationColumn K v.leftSlots → ℂ)
      (rightCoefficient : ((PUnit × PUnit) →* Circle) → Q → AllocationColumn K rightSlots → ℂ) : ℝ :=
    fullCorrelationHybridCost v.chart.kernel carrier
      v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
      v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
      (fun i => (v.block.rightResidual (v.rightReindex.index i)).val)
      rowWeight (fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)))
      leftCoefficient rightCoefficient
      (fun h i => v.chart.leftPoint h (v.leftReindex.index i))
      (fun h i => v.chart.rightPoint h (v.rightReindex.index i))
      (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
        v.2.2.2.2.2.1 v.2.2.2.2.2.2)
  have hrows : ((s.withMultiplier (fun i => jointPhase ξ (x i))).sources v.1).rows =
      (s.sources v.1).rows :=
    s.withMultiplier_rows (fun i => Real.fourierChar (inner ℝ ξ (x i))) v.1
  have hfilter :
      (((s.withMultiplier (fun i => jointPhase ξ (x i))).sources v.1).rows.filter
        (fun h => v.chart.rowLabel h = v.rowLabel)) = rows.rows :=
    congrArg (fun carrier : Finset Q =>
      carrier.filter (fun h => v.chart.rowLabel h = v.rowLabel)) hrows
  have hleft : multipliedLeft = phasedLeft := by
    funext χ h i
    dsimp only [multipliedLeft, phasedLeft, c]
    rw [sourceLeftCoefficient_withMultiplier s (fun i => jointPhase ξ (x i))
      v.1 v.2.1 (v.leftReindex.index i)]
    exact phase_mul_three_factors _ _ _ _
  have hright : multipliedRight = phasedRight := by
    funext χ h i
    dsimp only [multipliedRight, phasedRight, d]
    rw [sourceRightCoefficient_withMultiplier s (fun i => jointPhase ξ (x i))
      v.1 v.2.1 (v.rightReindex.index i)]
    exact phase_mul_three_factors _ _ _ _
  have hsplit : cost rows.rows phasedLeft phasedRight =
      ∑ j : v.AllocationKey, (v.leaf exceptional F x j).firstPhaseCost ξ :=
    fullCorrelationHybridCost_eq_leaf_sum F v.chart.kernel rows.rows
      v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
      v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
      (fun i => (v.block.rightResidual (v.rightReindex.index i)).val)
      rowWeight (fixedPhaseCoefficient PUnit (fun _ => (1 : Circle))) c d
      (fun _ i => x (v.leftReindex.index i))
      (fun h i => v.chart.leftPoint h (v.leftReindex.index i))
      (fun _ i => x (v.rightReindex.index i))
      (fun h i => v.chart.rightPoint h (v.rightReindex.index i))
      (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
        v.2.2.2.2.2.1 v.2.2.2.2.2.2) ξ
  change cost
      (((s.withMultiplier (fun i => jointPhase ξ (x i))).sources v.1).rows.filter
        (fun h => v.chart.rowLabel h = v.rowLabel)) multipliedLeft multipliedRight = _
  calc
    _ = cost rows.rows multipliedLeft multipliedRight :=
      congrArg (fun carrier : Finset Q => cost carrier multipliedLeft multipliedRight) hfilter
    _ = cost rows.rows phasedLeft phasedRight :=
      congrArg₂ (cost rows.rows) hleft hright
    _ = _ := hsplit

end CoveredClassKey

/-- Every source key and every actual allocation label is retained. -/
abbrev CoveredLeafKey := Σ v : s.CoveredClassKey LC RC, v.AllocationKey

def coveredLeaf (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey LC RC) :
    ActualHybridLeaf K Q W E :=
  b.1.leaf exceptional F x b.2

@[simp] theorem coveredLeaf_firstKernel (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey LC RC) :
    (s.coveredLeaf LC RC exceptional F x b).firstKernel = F := rfl

/-- Exact finite flattening of the covered source, at the first
continuous Fourier parameter. -/
theorem coverHybridPhaseNonzeroCost_eq_leaf_sum
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
      ∑ b : s.CoveredLeafKey LC RC, (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ := by
  unfold coverHybridPhaseNonzeroCost coverHybridNonzeroCost
    SecondBlockProfileChart.coverHybridCost SecondBlockProfileChart.subsetHybridCost
    SecondBlockProfileChart.subsetHybridClassCost
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, coveredLeaf]
  apply Finset.sum_congr rfl
  intro DE _
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro keyLeft _
  apply Finset.sum_congr rfl
  intro keyRight _
  exact (CoveredClassKey.phase_class_eq_leaf_sum
    (s := s) (LC := LC) (RC := RC)
    ⟨DE, D, a, e, label, keyLeft, keyRight⟩ exceptional F x ξ)

/-- The original first integral is exactly the sum of the genuine
nested-measure leaves.  Each leaf already separates exceptional row
products from ordinary paired energies. -/
theorem integral_coverHybridPhaseNonzeroCost_eq_leaf_sum
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) :
    (∫ ξ, s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ ∂actualFourierMeasure F) =
      ∑ b : s.CoveredLeafKey LC RC, (s.coveredLeaf LC RC exceptional F x b).cost := by
  simp_rw [s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    exact (s.coveredLeaf LC RC exceptional F x b).integral_firstPhaseCost
  · intro b _
    exact (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable

/-- The true orbital fibre multiplicity is paid exactly once per
nonzero leaf, alongside the identical multiplicity in the zero/tail budget. -/
def fiberCoveredLeaf (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey LC RC) :
    ActualHybridLeaf K Q W E :=
  (s.coveredLeaf LC RC exceptional F x b).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

@[simp] theorem fiberCoveredLeaf_firstKernel
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : s.CoveredLeafKey LC RC) :
    (s.fiberCoveredLeaf LC RC exceptional F x b).firstKernel = F := rfl

namespace TerminalCalibration

variable {s LC RC}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

def zeroBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (ε Czero : ℝ) : ℝ :=
  (s.fiber : ℝ) * Czero * (T.windows.multiplicity * T.zeroAmplitude) *
    Z ^ (T.productExponent * ε)

def tailBudget (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (Cerror : ℝ) : ℝ :=
  (s.fiber : ℝ) * Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)

/-- Exact terminal and nonzero separation on the original second
source.  Neither terminal budget is a new assumed aggregate estimate. -/
theorem phase_cost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) (ε Cerror Czero : ℝ) :
    (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero =
      T.zeroBudget ε Czero + T.tailBudget Cerror +
        ∑ b : s.CoveredLeafKey LC RC,
          (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost ξ := by
  change (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) = _
  rw [s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x ξ]
  simp only [fiberCoveredLeaf, ActualHybridLeaf.scale_firstPhaseCost,
    zeroBudget, tailBudget, Finset.mul_sum, mul_add, mul_assoc]
  ring

theorem integral_phase_cost_eq_budgets_leaves
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (LC RC : SourceCartesianCover G.columns G.ideal)
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).coverHybridCost LC RC exceptional ε Cerror Czero
        ∂actualFourierMeasure F) =
      (actualFourierMeasure F).real Set.univ * (T.zeroBudget ε Czero + T.tailBudget Cerror) +
        ∑ b : s.CoveredLeafKey LC RC, (s.fiberCoveredLeaf LC RC exceptional F x b).cost := by
  letI := actualFourierMeasure_finite F
  simp_rw [T.phase_cost_eq_budgets_leaves LC RC exceptional F x]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun b _ =>
    (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable))]
  rw [integral_const, integral_finsetSum]
  · simp only [smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    exact (s.fiberCoveredLeaf LC RC exceptional F x b).integral_firstPhaseCost
  · intro b _
    exact (s.fiberCoveredLeaf LC RC exceptional F x b).firstPhaseCost_integrable

end TerminalCalibration

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.coverHybridPhaseNonzeroCost_eq_leaf_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.integral_coverHybridPhaseNonzeroCost_eq_leaf_sum

