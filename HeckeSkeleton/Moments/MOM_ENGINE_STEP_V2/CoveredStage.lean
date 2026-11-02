import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CoverHybridPhaseIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

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

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

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

abbrev coveredClassKeyFintype : Fintype (CoveredClassKey s LC RC) :=
  inferInstance

attribute [local instance] coveredClassKeyFintype

namespace CoveredClassKey

variable {s LC RC}
variable (v : CoveredClassKey s LC RC)

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

end CoveredClassKey

/-- Every source key and every actual allocation label is retained. -/
abbrev CoveredLeafKey := Σ v : CoveredClassKey s LC RC, v.AllocationKey

abbrev coveredLeafKeyFintype : Fintype (CoveredLeafKey s LC RC) :=
  inferInstance

attribute [local instance] coveredLeafKeyFintype

def coveredLeaf (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    ActualHybridLeaf K Q W E :=
  b.1.leaf exceptional F x b.2

@[simp] theorem coveredLeaf_firstKernel (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    (coveredLeaf s LC RC exceptional F x b).firstKernel = F := rfl

/-- The true orbital fibre multiplicity is paid exactly once per
nonzero leaf, alongside the identical multiplicity in the zero/tail budget. -/
def fiberCoveredLeaf (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    ActualHybridLeaf K Q W E :=
  (coveredLeaf s LC RC exceptional F x b).scale (s.fiber : ℝ) (Nat.cast_nonneg _)

@[simp] theorem fiberCoveredLeaf_firstKernel
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (b : CoveredLeafKey s LC RC) :
    (fiberCoveredLeaf s LC RC exceptional F x b).firstKernel = F := rfl


end ActualGaussStage
end HeckeSkeleton.Moments.EngineStepV2

