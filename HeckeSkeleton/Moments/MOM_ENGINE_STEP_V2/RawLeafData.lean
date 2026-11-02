import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CoverHybridPhaseIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

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

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]

section Generic

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
local instance actualGaussFiniteLeavesCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

/-- The seven source-class labels are exactly those in
`coverHybridNonzeroCost`; no bounded surrogate carrier is substituted. -/
abbrev SourceClassKey :=
  Σ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    Σ D : s.mask.powerset,
    Σ a : LC.labels, Σ e : RC.labels,
    Σ label : Fin ((s.charts DE D).rowLabelCount + 1),
      (LC.branch a).labels (primeSupport DE.val.1) DE.val.1 ×
        (RC.branch e).labels (primeSupport DE.val.1) DE.val.2

abbrev coveredClassKeyFintype : Fintype (SourceClassKey s LC RC) :=
  inferInstance

attribute [local instance] coveredClassKeyFintype

namespace SourceClassKey

variable {s LC RC}
variable (v : SourceClassKey s LC RC)

abbrev block :=
  canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal v.1.val v.1.property

abbrev chart := s.charts v.1 v.2.1

abbrev rowLabel := v.2.2.2.2.1

/-- Keep the parameters of each reindex short as well as its result type.
The slot count remains named when Lean infers an index or slots projection. -/
def leftFibre : Finset ι :=
  (LC.branch v.2.2.1).commonFibre (primeSupport v.1.val.1) v.1.val.1
    v.2.2.2.2.2.1

def rightFibre : Finset ι :=
  (RC.branch v.2.2.2.1).commonFibre (primeSupport v.1.val.1) v.1.val.2
    v.2.2.2.2.2.2

def leftResidual : ι → A.Exterior := (SourceClassKey.block v).leftResidual

def rightResidual : ι → A.Exterior := (SourceClassKey.block v).rightResidual

def leftSlots : ℕ :=
  ((LC.branch v.2.2.1).branch (primeSupport v.1.val.1) v.1.val.1
    v.2.2.2.2.2.1).keep.card

def rightSlots : ℕ :=
  ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2
    v.2.2.2.2.2.2).keep.card

def LeftReindexType : Type _ :=
  CartesianSourceReindex (leftFibre v) (leftResidual v) (leftSlots v)

def RightReindexType : Type _ :=
  CartesianSourceReindex (rightFibre v) (rightResidual v) (rightSlots v)

def leftReindex : LeftReindexType v :=
  (LC.branch v.2.2.1).residualReindex (primeSupport v.1.val.1) v.1.val.1
    (SourceClassKey.block v).leftResidual (fun i _ => (SourceClassKey.block v).left_residual i) v.2.2.2.2.2.1

def rightReindex : RightReindexType v :=
  (RC.branch v.2.2.2.1).residualReindex (primeSupport v.1.val.1) v.1.val.2
    (SourceClassKey.block v).rightResidual (fun j _ => (SourceClassKey.block v).right_residual j) v.2.2.2.2.2.2

abbrev AllocationKey :=
  HybridAllocationLabel (SourceClassKey.rightReindex v).plain₁ (SourceClassKey.rightReindex v).plain₂ (SourceClassKey.rightReindex v).slots
    (fun j => ((SourceClassKey.block v).rightResidual ((SourceClassKey.rightReindex v).index j)).val)
    (SourceClassKey.leftSlots v) ((PUnit.{1} × PUnit.{1}) →* Circle)

def rawLeaf (exceptional :
    ActualGaussStage.CoverHybridPredicates.{_, _, 0, 0} s LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : (SourceClassKey.AllocationKey v)) :
    ActualHybridLeaf K Q W E :=
  fullCorrelationHybridLeaf F (SourceClassKey.chart v).kernel
    ((SourceClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (SourceClassKey.rowLabel v)).rows
    (SourceClassKey.leftReindex v).plain₁ (SourceClassKey.leftReindex v).plain₂ (SourceClassKey.leftReindex v).slots
    (SourceClassKey.rightReindex v).plain₁ (SourceClassKey.rightReindex v).plain₂ (SourceClassKey.rightReindex v).slots
    (fun i => ((SourceClassKey.block v).rightResidual ((SourceClassKey.rightReindex v).index i)).val)
    (fun h =>
      ((SourceClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (SourceClassKey.rowLabel v)).weight h *
        generatedIdealCorrelation (σ := σ) (SourceClassKey.block v).commonLeftIdeal (SourceClassKey.block v).commonRightIdeal
          (engineAllowedGenerator C (SourceClassKey.block v).commonLeftIdeal)
          (engineAllowedGenerator C (SourceClassKey.block v).commonRightIdeal)
          (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
          (((SourceClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (SourceClassKey.rowLabel v)).frequency h))
    (fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle)))
    (fun χ h i => (SourceClassKey.chart v).sourceLeftCoefficient ((SourceClassKey.leftReindex v).index i) *
      (fixedLeftPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue ((SourceClassKey.block v).leftResidual ((SourceClassKey.leftReindex v).index i))
          (((SourceClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (SourceClassKey.rowLabel v)).frequency h)))
    (fun χ h i => (SourceClassKey.chart v).sourceRightCoefficient ((SourceClassKey.rightReindex v).index i) *
      (fixedRightPhase PUnit.{1} χ PUnit.unit : ℂ) *
        σ (A.sexticResidue ((SourceClassKey.block v).rightResidual ((SourceClassKey.rightReindex v).index i))
          (-(((SourceClassKey.chart v).actualRows s.mask s.cutoff s.cutoff_one (SourceClassKey.rowLabel v)).frequency h))))
    (fun _ i => x ((SourceClassKey.leftReindex v).index i))
    (fun h i => (SourceClassKey.chart v).leftPoint h ((SourceClassKey.leftReindex v).index i))
    (fun _ i => x ((SourceClassKey.rightReindex v).index i))
    (fun h i => (SourceClassKey.chart v).rightPoint h ((SourceClassKey.rightReindex v).index i))
    (exceptional v.1 v.2.1 v.2.2.1 v.2.2.2.1 (SourceClassKey.rowLabel v)
      v.2.2.2.2.2.1 v.2.2.2.2.2.2) j


end SourceClassKey

end Generic

attribute [local instance]
  actualGaussFiniteLeavesCircleCharacterFintype coveredClassKeyFintype
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

open HeckeGeneral.ThetaSkeleton.Global

variable {c : TargetContext K}

/-- All costs use the original physical source multiplier and its one
orbital fibre factor. The two independent divisor allocations stay in
the actual class key's `AllocationKey`. -/
def secondSourceLeaf {call : Call c} {p : SourceParameters c}
    (source : SecondSource call p)
    (LC RC : SourceCartesianCover source.physical.source.columns
      source.physical.source.ideal)
    (key : SourceClassKey source.stage LC RC)
    (exceptional :
      ActualGaussStage.CoverHybridPredicates.{0, 0, 0, 0} source.stage LC RC)
    (allocation : SourceClassKey.AllocationKey key) :
    ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  (SourceClassKey.rawLeaf key exceptional source.physical.firstKernel
    source.physical.firstPoint allocation).scale
      (source.physical.outerWeight * (source.stage.fiber : ℝ))
      (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))

/-- A named proposition keeps the complete covered-leaf construction
out of the dependent packet constructor's field telescope. -/
def secondSourceLeafLive {call : Call c} {p : SourceParameters c}
    (source : SecondSource call p)
    (LC RC : SourceCartesianCover source.physical.source.columns
      source.physical.source.ideal)
    (key : SourceClassKey source.stage LC RC)
    (exceptional :
      ActualGaussStage.CoverHybridPredicates.{0, 0, 0, 0} source.stage LC RC)
    (allocation : SourceClassKey.AllocationKey
      (s := source.stage) (LC := LC) (RC := RC) key) : Prop :=
  (secondSourceLeaf (call := call) (p := p) source LC RC key exceptional allocation).Live

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
set_option genInjectivity false in
set_option genSizeOf false in
/-- One nonzero physical leaf with both original occurrence labels.
Empty source rows or a non-live polynomial produce no member of the
eventual finite family; neither an arbitrary reference row nor a
reference column is assumed later. -/
structure RawLeafPacket (call : Call c) (p : SourceParameters c) where
  second : SecondSource call p
  leftCover : SourceCartesianCover second.physical.source.columns
    second.physical.source.ideal
  rightCover : SourceCartesianCover second.physical.source.columns
    second.physical.source.ideal
  key : SourceClassKey second.stage leftCover rightCover
  exceptional :
    ActualGaussStage.CoverHybridPredicates.{0, 0, 0, 0} second.stage leftCover rightCover
  allocation : SourceClassKey.AllocationKey
    (s := second.stage) (LC := leftCover) (RC := rightCover) key
  physicalRows : second.physical.source.rows.Nonempty
  live : secondSourceLeafLive (call := call) (p := p)
    second leftCover rightCover key exceptional allocation
  nominal : Bool → OriginalNominalGeometry (K := K) call.workingParameters call.base
    (EngineInduction.Source.recipeInductionSigma c)
  leftFirst : SupportCartesianBranch call.workingRaw.originalPlain₁
    call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots
    second.physical.first.fullDeletion
  rightFirst : SupportCartesianBranch call.workingRaw.originalPlain₁
    call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots
    second.physical.first.fullDeletion

namespace RawLeafPacket

variable {call : Call c} {p : SourceParameters c} (packet : RawLeafPacket call p)

def leaf : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  secondSourceLeaf packet.second packet.leftCover packet.rightCover
    packet.key packet.exceptional packet.allocation

abbrev chart := SourceClassKey.chart packet.key
abbrev block := SourceClassKey.block packet.key
abbrev leftReindex := SourceClassKey.leftReindex packet.key
abbrev rightReindex := SourceClassKey.rightReindex packet.key
abbrev R := (SourceClassKey.chart packet.key).actualRows packet.second.stage.mask
  packet.second.stage.cutoff packet.second.stage.cutoff_one
  (SourceClassKey.rowLabel packet.key)

theorem leaf_live : packet.leaf.Live := packet.live

theorem rows_nonempty : packet.leaf.rows.Nonempty := by
  obtain ⟨h, hh, i, hi, hcoef⟩ := packet.live.2.1
  exact ⟨h, hh⟩

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint


