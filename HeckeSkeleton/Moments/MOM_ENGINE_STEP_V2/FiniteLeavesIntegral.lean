import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData

set_option linter.unusedSectionVars false
set_option autoImplicit false

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

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesIntegral

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
open WholeAllocation

private theorem scalar_sum_sigma_of_class_sum
    {α : Type*} [Fintype α] {β : α → Type*} [∀ a, Fintype (β a)]
    (total : ℝ) (classes : α → ℝ) (leaves : (Σ a : α, β a) → ℝ)
    (hclasses : total = ∑ a : α, classes a)
    (hleaves : ∀ a : α, classes a = ∑ b : β a, leaves ⟨a, b⟩) :
    total = ∑ key : (Σ a : α, β a), leaves key := by
  exact hclasses.trans
    ((Finset.sum_congr rfl (fun a _ => hleaves a)).trans
      (Fintype.sum_sigma leaves).symm)

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
local instance actualGaussFiniteLeavesCircleCharacterFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

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
abbrev CoveredClassKey := Blueprint.SourceClassKey s LC RC

attribute [local instance] Blueprint.coveredClassKeyFintype

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
variable (v : CoveredClassKey s LC RC)

abbrev block := Blueprint.SourceClassKey.block (s := s) (LC := LC) (RC := RC) v
abbrev chart := Blueprint.SourceClassKey.chart (s := s) (LC := LC) (RC := RC) v
abbrev rowLabel := Blueprint.SourceClassKey.rowLabel (s := s) (LC := LC) (RC := RC) v
abbrev leftReindex := Blueprint.SourceClassKey.leftReindex (s := s) (LC := LC) (RC := RC) v
abbrev rightReindex := Blueprint.SourceClassKey.rightReindex (s := s) (LC := LC) (RC := RC) v
abbrev leftSlots := Blueprint.SourceClassKey.leftSlots (s := s) (LC := LC) (RC := RC) v
abbrev AllocationKey := Blueprint.SourceClassKey.AllocationKey (s := s) (LC := LC) (RC := RC) v

abbrev leaf (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : (CoveredClassKey.AllocationKey v)) :
    ActualHybridLeaf K Q W E :=
  Blueprint.SourceClassKey.rawLeaf (s := s) (LC := LC) (RC := RC) v exceptional F x j

@[simp] theorem leaf_firstKernel (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : (CoveredClassKey.AllocationKey v)) :
    (CoveredClassKey.leaf v exceptional F x j).firstKernel = F := rfl

private theorem phase_mul_three_factors (phase a b c : ℂ) :
    ((phase * a) * b) * c = ((a * b) * c) * phase := by
  ring

private theorem phase_seven_argument_congr
    {X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y : Type*}
    (f : X₁ → X₂ → X₃ → X₄ → X₅ → X₆ → X₇ → Y)
    {a₁ b₁ : X₁} {a₂ b₂ : X₂} {a₃ b₃ : X₃} {a₄ b₄ : X₄}
    {a₅ b₅ : X₅} {a₆ b₆ : X₆} {a₇ b₇ : X₇}
    (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
    (h₄ : a₄ = b₄) (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
    f a₁ a₂ a₃ a₄ a₅ a₆ a₇ = f b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  cases h₆
  cases h₇
  rfl

private theorem phase_weight_frequency_congr
    {Row Frequency : Type*}
    (correlation : Frequency → ℂ)
    {weight₁ weight₂ : Row → ℂ} {frequency₁ frequency₂ : Row → Frequency}
    (hweight : weight₁ = weight₂) (hfrequency : frequency₁ = frequency₂) :
    (fun h => weight₁ h * correlation (frequency₁ h)) =
      (fun h => weight₂ h * correlation (frequency₂ h)) := by
  cases hweight
  cases hfrequency
  rfl

private theorem phase_coefficient_frequency_congr
    {Phase Row Column Frequency : Type*}
    (multiplier original updated : Column → ℂ)
    (fixedPhase : Phase → ℂ) (residue : Column → Frequency → ℂ)
    {frequency₁ frequency₂ : Row → Frequency}
    (hcoefficient : ∀ i, updated i = multiplier i * original i)
    (hfrequency : frequency₁ = frequency₂) :
    (fun χ h i => updated i * fixedPhase χ * residue i (frequency₁ h)) =
      (fun χ h i =>
        (original i * fixedPhase χ * residue i (frequency₂ h)) * multiplier i) := by
  subst frequency₂
  funext χ h i
  calc
    updated i * fixedPhase χ * residue i (frequency₁ h) =
        (multiplier i * original i) * fixedPhase χ * residue i (frequency₁ h) :=
      congrArg (fun coefficient : ℂ => coefficient * fixedPhase χ * residue i (frequency₁ h))
        (hcoefficient i)
    _ = (original i * fixedPhase χ * residue i (frequency₁ h)) * multiplier i :=
      phase_mul_three_factors (multiplier i) (original i)
        (fixedPhase χ) (residue i (frequency₁ h))

private theorem phase_point_reindex_congr
    {Row Source Target Point : Type*}
    (index : Target → Source)
    {points₁ points₂ : Row → Source → Point} (hpoints : points₁ = points₂) :
    (fun h i => points₁ h (index i)) = (fun h i => points₂ h (index i)) :=
  congrArg (fun points : Row → Source → Point => fun h i => points h (index i)) hpoints

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
private theorem phase_class_eq_fixed_fullCorrelation
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (x : ι → W) (ξ : W) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)
        (CoveredClassKey.leftReindex v) (CoveredClassKey.rightReindex v)
        (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) =
    fullCorrelationHybridCost
      (K := K) (H := Q) (V := E) (k := (CoveredClassKey.leftSlots v))
      (l := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card) (γ := ((PUnit.{1} × PUnit.{1}) →* Circle))
      (CoveredClassKey.chart v).kernel ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).rows
      (CoveredClassKey.leftReindex v).plain₁ (CoveredClassKey.leftReindex v).plain₂ (CoveredClassKey.leftReindex v).slots
      (CoveredClassKey.rightReindex v).plain₁ (CoveredClassKey.rightReindex v).plain₂ (CoveredClassKey.rightReindex v).slots
      (fun i => ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i)).val)
      (fun h =>
        ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).weight h *
          generatedIdealCorrelation (σ := σ) (CoveredClassKey.block v).commonLeftIdeal (CoveredClassKey.block v).commonRightIdeal
            (engineAllowedGenerator C (CoveredClassKey.block v).commonLeftIdeal)
            (engineAllowedGenerator C (CoveredClassKey.block v).commonRightIdeal)
            (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
            (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))
      (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
      (fun χ h i =>
        ((CoveredClassKey.chart v).sourceLeftCoefficient ((CoveredClassKey.leftReindex v).index i) *
          (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).leftResidual ((CoveredClassKey.leftReindex v).index i))
              (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))) *
          jointPhase ξ (x ((CoveredClassKey.leftReindex v).index i)))
      (fun χ h i =>
        ((CoveredClassKey.chart v).sourceRightCoefficient ((CoveredClassKey.rightReindex v).index i) *
          (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i))
              (-(((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h)))) *
          jointPhase ξ (x ((CoveredClassKey.rightReindex v).index i)))
      (fun h i => (CoveredClassKey.chart v).leftPoint h ((CoveredClassKey.leftReindex v).index i))
      (fun h i => (CoveredClassKey.chart v).rightPoint h ((CoveredClassKey.rightReindex v).index i))
      (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
        v.2.2.2.2.2.1 v.2.2.2.2.2.2) := by
  have hkernel := s.withMultiplier_kernel
    (fun i => jointPhase ξ (x i)) v.1 v.2.1
  have hrows := actualRows_withMultiplier_rows s
    (fun i => Real.fourierChar (inner ℝ ξ (x i))) v.1 v.2.1 (CoveredClassKey.rowLabel v)
  have hfrequency := actualRows_withMultiplier_frequency s
    (fun i => jointPhase ξ (x i)) v.1 v.2.1 (CoveredClassKey.rowLabel v)
  have hweight := actualRows_withMultiplier_weight s
    (fun i => jointPhase ξ (x i)) v.1 v.2.1 (CoveredClassKey.rowLabel v)
  have hrowCoefficient := phase_weight_frequency_congr
    (fun frequency : A.R =>
      generatedIdealCorrelation (σ := σ) (CoveredClassKey.block v).commonLeftIdeal (CoveredClassKey.block v).commonRightIdeal
        (engineAllowedGenerator C (CoveredClassKey.block v).commonLeftIdeal)
        (engineAllowedGenerator C (CoveredClassKey.block v).commonRightIdeal)
        (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
        frequency)
    hweight hfrequency
  have hleftCoefficient := phase_coefficient_frequency_congr
    (Phase := ((PUnit.{1} × PUnit.{1}) →* Circle)) (Row := Q)
    (Column := AllocationColumn K (CoveredClassKey.leftSlots v)) (Frequency := A.R)
    (fun i => jointPhase ξ (x ((CoveredClassKey.leftReindex v).index i)))
    (fun i => (CoveredClassKey.chart v).sourceLeftCoefficient ((CoveredClassKey.leftReindex v).index i))
    (fun i => ((s.withMultiplier (fun j => jointPhase ξ (x j))).charts
      v.1 v.2.1).sourceLeftCoefficient ((CoveredClassKey.leftReindex v).index i))
    (fun χ => (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ))
    (fun i frequency =>
      σ (A.sexticResidue ((CoveredClassKey.block v).leftResidual ((CoveredClassKey.leftReindex v).index i)) frequency))
    (fun i => sourceLeftCoefficient_withMultiplier s
      (fun j => jointPhase ξ (x j)) v.1 v.2.1 ((CoveredClassKey.leftReindex v).index i))
    hfrequency
  have hrightCoefficient := phase_coefficient_frequency_congr
    (Phase := ((PUnit.{1} × PUnit.{1}) →* Circle)) (Row := Q)
    (Column := AllocationColumn K (((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card)) (Frequency := A.R)
    (fun i => jointPhase ξ (x ((CoveredClassKey.rightReindex v).index i)))
    (fun i => (CoveredClassKey.chart v).sourceRightCoefficient ((CoveredClassKey.rightReindex v).index i))
    (fun i => ((s.withMultiplier (fun j => jointPhase ξ (x j))).charts
      v.1 v.2.1).sourceRightCoefficient ((CoveredClassKey.rightReindex v).index i))
    (fun χ => (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ))
    (fun i frequency =>
      σ (A.sexticResidue ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i)) (-frequency)))
    (fun i => sourceRightCoefficient_withMultiplier s
      (fun j => jointPhase ξ (x j)) v.1 v.2.1 ((CoveredClassKey.rightReindex v).index i))
    hfrequency
  have hleftPoint := phase_point_reindex_congr (CoveredClassKey.leftReindex v).index
    (charts_withMultiplier_leftPoint s (fun i => jointPhase ξ (x i)) v.1 v.2.1)
  have hrightPoint := phase_point_reindex_congr (CoveredClassKey.rightReindex v).index
    (charts_withMultiplier_rightPoint s (fun i => jointPhase ξ (x i)) v.1 v.2.1)
  unfold SecondBlockProfileChart.hybridClassCost secondResidualHybridCost
  exact phase_seven_argument_congr
    (fun (kernel : SchwartzMap E ℂ) (rows : Finset Q) (rowCoefficient : Q → ℂ)
      (leftCoefficient : ((PUnit.{1} × PUnit.{1}) →* Circle) → Q → AllocationColumn K (CoveredClassKey.leftSlots v) → ℂ)
      (rightCoefficient : ((PUnit.{1} × PUnit.{1}) →* Circle) → Q →
        AllocationColumn K (((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card) → ℂ)
      (leftPoint : Q → AllocationColumn K (CoveredClassKey.leftSlots v) → E)
      (rightPoint : Q → AllocationColumn K (((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card) → E) =>
        fullCorrelationHybridCost
          (K := K) (H := Q) (V := E) (k := (CoveredClassKey.leftSlots v))
          (l := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card) (γ := ((PUnit.{1} × PUnit.{1}) →* Circle))
          kernel rows
          (CoveredClassKey.leftReindex v).plain₁ (CoveredClassKey.leftReindex v).plain₂ (CoveredClassKey.leftReindex v).slots
          (CoveredClassKey.rightReindex v).plain₁ (CoveredClassKey.rightReindex v).plain₂ (CoveredClassKey.rightReindex v).slots
          (fun i => ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i)).val)
          rowCoefficient (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
          leftCoefficient rightCoefficient leftPoint rightPoint
          (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
        v.2.2.2.2.2.1 v.2.2.2.2.2.2))
    hkernel hrows hrowCoefficient hleftCoefficient hrightCoefficient hleftPoint hrightPoint

set_option linter.unusedSectionVars false in
private theorem fixed_fullCorrelation_eq_leaf_sum
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    fullCorrelationHybridCost
      (K := K) (H := Q) (V := E) (k := (CoveredClassKey.leftSlots v))
      (l := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2).keep.card) (γ := ((PUnit.{1} × PUnit.{1}) →* Circle))
      (CoveredClassKey.chart v).kernel ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).rows
      (CoveredClassKey.leftReindex v).plain₁ (CoveredClassKey.leftReindex v).plain₂ (CoveredClassKey.leftReindex v).slots
      (CoveredClassKey.rightReindex v).plain₁ (CoveredClassKey.rightReindex v).plain₂ (CoveredClassKey.rightReindex v).slots
      (fun i => ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i)).val)
      (fun h =>
        ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).weight h *
          generatedIdealCorrelation (σ := σ) (CoveredClassKey.block v).commonLeftIdeal (CoveredClassKey.block v).commonRightIdeal
            (engineAllowedGenerator C (CoveredClassKey.block v).commonLeftIdeal)
            (engineAllowedGenerator C (CoveredClassKey.block v).commonRightIdeal)
            (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
            (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))
      (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
      (fun χ h i =>
        ((CoveredClassKey.chart v).sourceLeftCoefficient ((CoveredClassKey.leftReindex v).index i) *
          (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).leftResidual ((CoveredClassKey.leftReindex v).index i))
              (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))) *
          jointPhase ξ (x ((CoveredClassKey.leftReindex v).index i)))
      (fun χ h i =>
        ((CoveredClassKey.chart v).sourceRightCoefficient ((CoveredClassKey.rightReindex v).index i) *
          (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i))
              (-(((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h)))) *
          jointPhase ξ (x ((CoveredClassKey.rightReindex v).index i)))
      (fun h i => (CoveredClassKey.chart v).leftPoint h ((CoveredClassKey.leftReindex v).index i))
      (fun h i => (CoveredClassKey.chart v).rightPoint h ((CoveredClassKey.rightReindex v).index i))
      (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
        v.2.2.2.2.2.1 v.2.2.2.2.2.2) =
      ∑ j : (CoveredClassKey.AllocationKey v), (CoveredClassKey.leaf v exceptional F x j).firstPhaseCost ξ := by
  exact
    (fullCorrelationHybridCost_eq_leaf_sum
      (K := K) (H := Q) (U := W) (V := E)
      (k := (CoveredClassKey.leftSlots v))
      (l := ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1)
        v.1.val.2 v.2.2.2.2.2.2).keep.card)
      (γ := ((PUnit.{1} × PUnit.{1}) →* Circle))
      F (CoveredClassKey.chart v).kernel
        ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).rows
        (CoveredClassKey.leftReindex v).plain₁ (CoveredClassKey.leftReindex v).plain₂ (CoveredClassKey.leftReindex v).slots
        (CoveredClassKey.rightReindex v).plain₁ (CoveredClassKey.rightReindex v).plain₂ (CoveredClassKey.rightReindex v).slots
        (fun i => ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i)).val)
        (fun h =>
          ((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).weight h *
            generatedIdealCorrelation (σ := σ) (CoveredClassKey.block v).commonLeftIdeal (CoveredClassKey.block v).commonRightIdeal
              (engineAllowedGenerator C (CoveredClassKey.block v).commonLeftIdeal)
              (engineAllowedGenerator C (CoveredClassKey.block v).commonRightIdeal)
              (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
              (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))
        (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
        (fun χ h i => (CoveredClassKey.chart v).sourceLeftCoefficient ((CoveredClassKey.leftReindex v).index i) *
          (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).leftResidual ((CoveredClassKey.leftReindex v).index i))
              (((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h)))
        (fun χ h i => (CoveredClassKey.chart v).sourceRightCoefficient ((CoveredClassKey.rightReindex v).index i) *
          (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
            σ (A.sexticResidue ((CoveredClassKey.block v).rightResidual ((CoveredClassKey.rightReindex v).index i))
              (-(((CoveredClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)).frequency h))))
        (fun _ i => x ((CoveredClassKey.leftReindex v).index i))
        (fun h i => (CoveredClassKey.chart v).leftPoint h ((CoveredClassKey.leftReindex v).index i))
        (fun _ i => x ((CoveredClassKey.rightReindex v).index i))
        (fun h i => (CoveredClassKey.chart v).rightPoint h ((CoveredClassKey.rightReindex v).index i))
        (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) ξ)

set_option linter.unusedSectionVars false in
/-- This is the actual phase multiplication from the first transform,
followed by the literal finite allocation sum from the second. -/
theorem phase_class_eq_leaf_sum (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v)
        (CoveredClassKey.leftReindex v) (CoveredClassKey.rightReindex v)
        (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
          v.2.2.2.2.2.1 v.2.2.2.2.2.2) =
      ∑ j : (CoveredClassKey.AllocationKey v), (CoveredClassKey.leaf v exceptional F x j).firstPhaseCost ξ := by
  exact (phase_class_eq_fixed_fullCorrelation v exceptional x ξ).trans
    (fixed_fullCorrelation_eq_leaf_sum v exceptional F x ξ)

end CoveredClassKey

/-- Every source key and every actual allocation label is retained. -/
abbrev CoveredLeafKey := Σ v : CoveredClassKey s LC RC, (CoveredClassKey.AllocationKey v)

def coveredLeaf (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    ActualHybridLeaf K Q W E :=
  CoveredClassKey.leaf b.1 exceptional F x b.2

@[simp] theorem coveredLeaf_firstKernel (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    (coveredLeaf s LC RC exceptional F x b).firstKernel = F := rfl

private def coveredClassPhaseCost
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (x : ι → W) (ξ : W) (v : CoveredClassKey s LC RC) : ℝ :=
  ((s.withMultiplier (fun i => jointPhase ξ (x i))).charts v.1 v.2.1).hybridClassCost
    s.mask s.cutoff s.cutoff_one (CoveredClassKey.rowLabel v) (CoveredClassKey.leftReindex v) (CoveredClassKey.rightReindex v)
    (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (CoveredClassKey.rowLabel v)
      v.2.2.2.2.2.1 v.2.2.2.2.2.2)

private def coveredClassNestedSum (f : CoveredClassKey s LC RC → ℝ) : ℝ :=
  ∑ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∑ D : s.mask.powerset, ∑ a : LC.labels, ∑ e : RC.labels,
      ∑ label : Fin ((s.charts DE D).rowLabelCount + 1),
        ∑ keyLeft : (LC.branch a).labels (primeSupport DE.val.1) DE.val.1,
          ∑ keyRight : (RC.branch e).labels (primeSupport DE.val.1) DE.val.2,
            f ⟨DE, D, a, e, label, keyLeft, keyRight⟩

private theorem coveredClassNestedSum_eq_sum (f : CoveredClassKey s LC RC → ℝ) :
    coveredClassNestedSum s LC RC f = ∑ v : CoveredClassKey s LC RC, f v := by
  unfold coveredClassNestedSum
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]

private theorem phase_subsetHybridClassCost_eq_key_sum
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC) (x : ι → W) (ξ : W)
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
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC) (x : ι → W) (ξ : W)
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
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC) (x : ι → W) (ξ : W)
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
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC) (x : ι → W) (ξ : W) :
    (s.withMultiplier (fun i => jointPhase ξ (x i))).coverHybridNonzeroCost
        LC RC exceptional =
      coveredClassNestedSum s LC RC (coveredClassPhaseCost s LC RC exceptional x ξ) := by
  unfold EngineStep.ActualGaussStage.coverHybridNonzeroCost coveredClassNestedSum
  apply Finset.sum_congr rfl
  intro DE _
  apply Finset.sum_congr rfl
  intro D _
  exact phase_coverHybridCost_eq_cover_sum s LC RC exceptional x ξ DE D

private theorem coverHybridPhaseNonzeroCost_eq_class_sum
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC) (x : ι → W) (ξ : W) :
    s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
      ∑ v : CoveredClassKey s LC RC, coveredClassPhaseCost s LC RC exceptional x ξ v := by
  change (s.withMultiplier (fun i => jointPhase ξ (x i))).coverHybridNonzeroCost
    LC RC exceptional = _
  exact (phase_coverHybridNonzeroCost_eq_nested_sum s LC RC exceptional x ξ).trans
    (coveredClassNestedSum_eq_sum s LC RC (coveredClassPhaseCost s LC RC exceptional x ξ))

set_option linter.unusedSectionVars false in
/-- Exact finite flattening of the covered source, at the first
continuous Fourier parameter. -/
theorem coverHybridPhaseNonzeroCost_eq_leaf_sum
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (ξ : W) :
    s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ =
      ∑ b : CoveredLeafKey s LC RC, (coveredLeaf s LC RC exceptional F x b).firstPhaseCost ξ := by
  exact scalar_sum_sigma_of_class_sum
    (α := CoveredClassKey s LC RC) (β := fun v => (CoveredClassKey.AllocationKey v))
    (s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ)
    (coveredClassPhaseCost s LC RC exceptional x ξ)
    (fun b => (coveredLeaf s LC RC exceptional F x b).firstPhaseCost ξ)
    (coverHybridPhaseNonzeroCost_eq_class_sum s LC RC exceptional x ξ)
    (fun v => CoveredClassKey.phase_class_eq_leaf_sum v exceptional F x ξ)

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
    (exceptional : EngineStep.ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) :
    (∫ ξ, s.coverHybridPhaseNonzeroCost LC RC exceptional x ξ ∂actualFourierMeasure F) =
      ∑ b : CoveredLeafKey s LC RC, (coveredLeaf s LC RC exceptional F x b).cost := by
  exact integral_eq_leafFamily_cost
    (K := K) (H := Q) (W := W) (E := E)
    (J := CoveredLeafKey s LC RC)
    F (coveredLeaf s LC RC exceptional F x)
    (coveredLeaf_firstKernel s LC RC exceptional F x)
    (s.coverHybridPhaseNonzeroCost LC RC exceptional x)
    (coverHybridPhaseNonzeroCost_eq_leaf_sum s LC RC exceptional F x)

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesIntegral

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesIntegral.ActualGaussStage.coverHybridPhaseNonzeroCost_eq_leaf_sum
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeavesIntegral.ActualGaussStage.integral_coverHybridPhaseNonzeroCost_eq_leaf_sum
