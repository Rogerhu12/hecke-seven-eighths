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
instance actualGaussFiniteLeavesCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

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

private theorem charts_withMultiplier_leftPoint
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    ((s.withMultiplier u).charts DE D).leftPoint =
      (s.charts DE D).leftPoint := rfl

private theorem charts_withMultiplier_rightPoint
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    ((s.withMultiplier u).charts DE D).rightPoint =
      (s.charts DE D).rightPoint := rfl

private theorem charts_withMultiplier_rowLabelCount
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    ((s.withMultiplier u).charts DE D).rowLabelCount =
      (s.charts DE D).rowLabelCount := rfl

private theorem charts_withMultiplier_rowLabel
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    ((s.withMultiplier u).charts DE D).rowLabel =
      (s.charts DE D).rowLabel := rfl

private theorem actualRows_withMultiplier_frequency
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    (((s.withMultiplier u).charts DE D).actualRows
      s.mask s.cutoff s.cutoff_one label).frequency =
      ((s.charts DE D).actualRows
        s.mask s.cutoff s.cutoff_one label).frequency := rfl

private theorem actualRows_withMultiplier_weight
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    (((s.withMultiplier u).charts DE D).actualRows
      s.mask s.cutoff s.cutoff_one label).weight =
      ((s.charts DE D).actualRows
        s.mask s.cutoff s.cutoff_one label).weight := rfl

private theorem actualRows_rows_eq_source_filter
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    ((s.charts DE D).actualRows s.mask s.cutoff s.cutoff_one label).rows =
      (s.sources DE).rows.filter (fun h => (s.charts DE D).rowLabel h = label) := rfl

private theorem actualRows_withMultiplier_rows
    (u : ι → Circle)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    (((s.withMultiplier (fun i => (u i : ℂ))).charts DE D).actualRows
      s.mask s.cutoff s.cutoff_one label).rows =
      ((s.charts DE D).actualRows
        s.mask s.cutoff s.cutoff_one label).rows := by
  apply Finset.ext
  intro h
  have hcarrier :
      h ∈ ((s.withMultiplier (fun i => (u i : ℂ))).sources DE).rows ↔
        h ∈ (s.sources DE).rows :=
    (congrArg (fun carrier : Finset Q => h ∈ carrier)
      (s.withMultiplier_rows u DE)).to_iff
  have hlabel :
      ((s.withMultiplier (fun i => (u i : ℂ))).charts DE D).rowLabel h = label ↔
        (s.charts DE D).rowLabel h = label :=
    (congrArg
      (fun rowLabel : Q → Fin ((s.charts DE D).rowLabelCount + 1) =>
        rowLabel h = label)
      (charts_withMultiplier_rowLabel s (fun i => (u i : ℂ)) DE D)).to_iff
  dsimp only [SecondBlockProfileChart.actualRows]
  simp only [Finset.mem_filter]
  simpa only [ActualGaussStage.sources, ActualGaussStage.withMultiplier,
    ActualGaussSource.withMultiplier] using (and_congr hcarrier hlabel)

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

private theorem sourceLeftCoefficient_withMultiplier_product
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι) (a b : ℂ) :
    ((s.withMultiplier u).charts DE D).sourceLeftCoefficient i * a * b =
      ((s.charts DE D).sourceLeftCoefficient i * a * b) * u i :=
  (congrArg (fun coefficient : ℂ => coefficient * a * b)
    (sourceLeftCoefficient_withMultiplier s u DE D i)).trans
      (phase_mul_three_factors (u i) ((s.charts DE D).sourceLeftCoefficient i) a b)

private theorem sourceRightCoefficient_withMultiplier_product
    (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (i : ι) (a b : ℂ) :
    ((s.withMultiplier u).charts DE D).sourceRightCoefficient i * a * b =
      ((s.charts DE D).sourceRightCoefficient i * a * b) * u i :=
  (congrArg (fun coefficient : ℂ => coefficient * a * b)
    (sourceRightCoefficient_withMultiplier s u DE D i)).trans
      (phase_mul_three_factors (u i) ((s.charts DE D).sourceRightCoefficient i) a b)

/-- This is the actual phase multiplication from the first transform,
followed by the literal finite allocation sum from the second. -/
theorem phase_class_eq_leaf_sum (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost s.mask s.cutoff s.cutoff_one v.rowLabel
        v.leftReindex v.rightReindex
        (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) =
      ∑ j : v.AllocationKey, (v.leaf exceptional F x j).firstPhaseCost ξ := by
  unfold SecondBlockProfileChart.hybridClassCost secondResidualHybridCost
  simp only [s.withMultiplier_kernel (fun i => jointPhase ξ (x i)) v.1 v.2.1,
    actualRows_withMultiplier_rows s
      (fun i => Real.fourierChar (inner ℝ ξ (x i))) v.1 v.2.1 v.rowLabel,
    actualRows_withMultiplier_frequency s (fun i => jointPhase ξ (x i))
      v.1 v.2.1 v.rowLabel,
    actualRows_withMultiplier_weight s (fun i => jointPhase ξ (x i))
      v.1 v.2.1 v.rowLabel,
    charts_withMultiplier_leftPoint s (fun i => jointPhase ξ (x i)) v.1 v.2.1,
    charts_withMultiplier_rightPoint s (fun i => jointPhase ξ (x i)) v.1 v.2.1,
    sourceLeftCoefficient_withMultiplier_product (s := s)
      (fun i => jointPhase ξ (x i)) v.1 v.2.1,
    sourceRightCoefficient_withMultiplier_product (s := s)
      (fun i => jointPhase ξ (x i)) v.1 v.2.1]
  simpa only [leaf] using
    (fullCorrelationHybridCost_eq_leaf_sum
      (K := K) (H := Q) (U := W) (V := E)
      (k := v.leftSlots)
      (l := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1)
        v.1.val.2 v.2.2.2.2.2.2).keep.card)
      (γ := ((PUnit × PUnit) →* Circle))
      F v.chart.kernel
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
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) ξ)

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

private def coveredClassPhaseCost
    (exceptional : s.CoverHybridPredicates LC RC)
    (x : ι → W) (ξ : W) (v : s.CoveredClassKey LC RC) : ℝ :=
  ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost
    s.mask s.cutoff s.cutoff_one v.rowLabel v.leftReindex v.rightReindex
    (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.rowLabel
      v.2.2.2.2.2.1 v.2.2.2.2.2.2)

private def coveredClassNestedSum (f : s.CoveredClassKey LC RC → ℝ) : ℝ :=
  ∑ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∑ D : s.mask.powerset, ∑ a : LC.labels, ∑ e : RC.labels,
      ∑ label : Fin ((s.charts DE D).rowLabelCount + 1),
        ∑ keyLeft : (LC.branch a).labels (primeSupport DE.val.1) DE.val.1,
          ∑ keyRight : (RC.branch e).labels (primeSupport DE.val.1) DE.val.2,
            f ⟨DE, D, a, e, label, keyLeft, keyRight⟩

private theorem coveredClassNestedSum_eq_sum (f : s.CoveredClassKey LC RC → ℝ) :
    coveredClassNestedSum s LC RC f = ∑ v : s.CoveredClassKey LC RC, f v := by
  unfold coveredClassNestedSum
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

private theorem phase_subsetHybridClassCost_eq_key_sum
    (exceptional : s.CoverHybridPredicates LC RC) (x : ι → W) (ξ : W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (a : LC.labels) (e : RC.labels)
    (label : Fin ((s.charts DE D).rowLabelCount + 1)) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).subsetHybridClassCost
        (LC.branch a) (RC.branch e) s.mask s.cutoff s.cutoff_one
        label (exceptional DE D a e) =
      ∑ keyLeft : (LC.branch a).labels (primeSupport DE.val.1) DE.val.1,
        ∑ keyRight : (RC.branch e).labels (primeSupport DE.val.1) DE.val.2,
          coveredClassPhaseCost s LC RC exceptional x ξ
            ⟨DE, D, a, e, label, keyLeft, keyRight⟩ := by
  rfl

private theorem phase_subsetHybridCost_eq_row_sum
    (exceptional : s.CoverHybridPredicates LC RC) (x : ι → W) (ξ : W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (a : LC.labels) (e : RC.labels) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).subsetHybridCost
        (LC.branch a) (RC.branch e) s.mask s.cutoff s.cutoff_one
        (exceptional DE D a e) =
      ∑ label : Fin ((s.charts DE D).rowLabelCount + 1),
        ∑ keyLeft : (LC.branch a).labels (primeSupport DE.val.1) DE.val.1,
          ∑ keyRight : (RC.branch e).labels (primeSupport DE.val.1) DE.val.2,
            coveredClassPhaseCost s LC RC exceptional x ξ
              ⟨DE, D, a, e, label, keyLeft, keyRight⟩ := by
  unfold SecondBlockProfileChart.subsetHybridCost
  apply Finset.sum_congr rfl
  intro label _
  exact phase_subsetHybridClassCost_eq_key_sum s LC RC exceptional x ξ DE D a e label

private theorem phase_coverHybridCost_eq_cover_sum
    (exceptional : s.CoverHybridPredicates LC RC) (x : ι → W) (ξ : W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts DE D).coverHybridCost
        LC RC s.mask s.cutoff s.cutoff_one (exceptional DE D) =
      ∑ a : LC.labels, ∑ e : RC.labels,
        ∑ label : Fin ((s.charts DE D).rowLabelCount + 1),
          ∑ keyLeft : (LC.branch a).labels (primeSupport DE.val.1) DE.val.1,
            ∑ keyRight : (RC.branch e).labels (primeSupport DE.val.1) DE.val.2,
              coveredClassPhaseCost s LC RC exceptional x ξ
                ⟨DE, D, a, e, label, keyLeft, keyRight⟩ := by
  unfold SecondBlockProfileChart.coverHybridCost
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  exact phase_subsetHybridCost_eq_row_sum s LC RC exceptional x ξ DE D a e

private theorem phase_coverHybridNonzeroCost_eq_nested_sum
    (exceptional : s.CoverHybridPredicates LC RC) (x : ι → W) (ξ : W) :
    (s.withMultiplier (fun i => jointPhase ξ (x i))).coverHybridNonzeroCost
        LC RC exceptional =
      coveredClassNestedSum s LC RC (coveredClassPhaseCost s LC RC exceptional x ξ) := by
  unfold coverHybridNonzeroCost coveredClassNestedSum
  apply Finset.sum_congr rfl
  intro DE _
  apply Finset.sum_congr rfl
  intro D _
  exact phase_coverHybridCost_eq_cover_sum s LC RC exceptional x ξ DE D

private theorem coverHybridPhaseNonzeroCost_eq_class_sum
    (exceptional : s.CoverHybridPredicates LC RC) (x : ι → W) (ξ : W) :
    s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
      ∑ v : s.CoveredClassKey LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v := by
  change (s.withMultiplier (fun i => jointPhase ξ (x i))).coverHybridNonzeroCost
    LC RC exceptional = _
  exact (phase_coverHybridNonzeroCost_eq_nested_sum s LC RC exceptional x ξ).trans
    (coveredClassNestedSum_eq_sum s LC RC (coveredClassPhaseCost s LC RC exceptional x ξ))

private theorem coveredLeaf_sum_eq_class_sum (f : s.CoveredLeafKey LC RC → ℝ) :
    (∑ b : s.CoveredLeafKey LC RC, f b) =
      ∑ v : s.CoveredClassKey LC RC, ∑ j : v.AllocationKey, f ⟨v, j⟩ := by
  exact Fintype.sum_sigma f

/-- Exact finite flattening of the covered source, at the first
continuous Fourier parameter. -/
theorem coverHybridPhaseNonzeroCost_eq_leaf_sum
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
      ∑ b : s.CoveredLeafKey LC RC, (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ := by
  have hclasses :
      s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
        ∑ v : s.CoveredClassKey LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v :=
    coverHybridPhaseNonzeroCost_eq_class_sum s LC RC exceptional x ξ
  have hleaves :
      (∑ v : s.CoveredClassKey LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v) =
        ∑ v : s.CoveredClassKey LC RC,
          ∑ j : v.AllocationKey, (v.leaf exceptional F x j).firstPhaseCost ξ := by
    apply Finset.sum_congr rfl
    intro v _
    exact v.phase_class_eq_leaf_sum exceptional F x ξ
  exact hclasses.trans (hleaves.trans
    (coveredLeaf_sum_eq_class_sum s LC RC
      (fun b => (s.coveredLeaf LC RC exceptional F x b).firstPhaseCost ξ)).symm)

private theorem leaf_firstPhaseCost_integrable_of_firstKernel
    {H : Type*} (B : ActualHybridLeaf K H W E)
    (F : SchwartzMap W ℂ) (hF : B.firstKernel = F) :
    Integrable B.firstPhaseCost (actualFourierMeasure F) := by
  subst F
  exact B.firstPhaseCost_integrable

private theorem leaf_integral_firstPhaseCost_of_firstKernel
    {H : Type*} (B : ActualHybridLeaf K H W E)
    (F : SchwartzMap W ℂ) (hF : B.firstKernel = F) :
    (∫ ξ, B.firstPhaseCost ξ ∂actualFourierMeasure F) = B.cost := by
  subst F
  exact B.integral_firstPhaseCost

private theorem integral_eq_leafFamily_cost
    {J H : Type*} [Fintype J]
    (F : SchwartzMap W ℂ) (B : J → ActualHybridLeaf K H W E)
    (hkernel : ∀ b : J, (B b).firstKernel = F)
    (f : W → ℝ)
    (hsum : ∀ ξ, f ξ = ∑ b : J, (B b).firstPhaseCost ξ) :
    (∫ ξ, f ξ ∂actualFourierMeasure F) = ∑ b : J, (B b).cost := by
  have hterms : ∀ b : J,
      Integrable (B b).firstPhaseCost (actualFourierMeasure F) :=
    fun b => leaf_firstPhaseCost_integrable_of_firstKernel (B b) F (hkernel b)
  calc
    (∫ ξ, f ξ ∂actualFourierMeasure F) =
        ∫ ξ, ∑ b : J, (B b).firstPhaseCost ξ ∂actualFourierMeasure F :=
      integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ = ∑ b : J, ∫ ξ, (B b).firstPhaseCost ξ ∂actualFourierMeasure F :=
      integral_finsetSum (μ := actualFourierMeasure F)
        (f := fun b : J => (B b).firstPhaseCost) Finset.univ
        (fun b _ => hterms b)
    _ = ∑ b : J, (B b).cost :=
      Finset.sum_congr rfl
        (fun b _ => leaf_integral_firstPhaseCost_of_firstKernel (B b) F (hkernel b))

/-- The original first integral is exactly the sum of the genuine
nested-measure leaves.  Each leaf already separates exceptional row
products from ordinary paired energies. -/
theorem integral_coverHybridPhaseNonzeroCost_eq_leaf_sum
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) :
    (∫ ξ, s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ ∂actualFourierMeasure F) =
      ∑ b : s.CoveredLeafKey LC RC, (s.coveredLeaf LC RC exceptional F x b).cost := by
  exact integral_eq_leafFamily_cost
    (K := K) (H := Q) (W := W) (E := E)
    (J := s.CoveredLeafKey LC RC)
    F (s.coveredLeaf LC RC exceptional F x)
    (s.coveredLeaf_firstKernel LC RC exceptional F x)
    (s.coverHybridPhaseNonzeroCost LC RC exceptional x)
    (s.coverHybridPhaseNonzeroCost_eq_leaf_sum LC RC exceptional F x)

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

