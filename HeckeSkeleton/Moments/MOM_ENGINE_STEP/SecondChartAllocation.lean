import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource

/-!
# The actual second profile chart on its Cartesian factor support

The expansion dictionary identifies individual retained source columns
with their two plain ideals and all prime-slot ideals.  A finite-support
bijection and the individual ideal product are the only reindexing
inputs.  The complete divisor pool, whole coefficients, Fourier
polynomials and common kernel are transported internally.

The actual orbit rows, negative Poisson frequency, canonical common
prime powers and allowed generators directly construct the arithmetic
row data.  No frequency extraction or parent-to-child estimate is supplied
by the chart.  A Cartesian support dictionary is required only after the
original valuation/allocation labels have fixed that rectangular branch.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}

/-- A primitive finite expansion dictionary for one actual rectangular
branch.  It contains no coefficient sum or analytic inequality. -/
structure CartesianSourceReindex {ι : Type*} (columns : Finset ι)
    (ideal : ι → A.Exterior) (k : ℕ) where
  plain₁ : Finset (Ideal (𝓞 K))
  plain₂ : Finset (Ideal (𝓞 K))
  slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))
  index : AllocationColumn K k → ι
  maps : ∀ x ∈ childCartesianColumns plain₁ plain₂ slots, index x ∈ columns
  injective : Set.InjOn index (childCartesianColumns plain₁ plain₂ slots : Set (AllocationColumn K k))
  surjective : ∀ i ∈ columns, ∃ x ∈ childCartesianColumns plain₁ plain₂ slots, index x = i
  ideal_product : ∀ x ∈ childCartesianColumns plain₁ plain₂ slots,
    (ideal (index x)).val = allocationColumnIdeal x

namespace CartesianSourceReindex

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior} {k : ℕ}
variable (R : CartesianSourceReindex columns ideal k)

def cartesian : Finset (AllocationColumn K k) :=
  childCartesianColumns R.plain₁ R.plain₂ R.slots

theorem image_eq : R.cartesian.image R.index = columns := by
  ext i
  constructor
  · rintro hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact R.maps x hx
  · intro hi
    obtain ⟨x, hx, hxi⟩ := R.surjective i hi
    exact Finset.mem_image.mpr ⟨x, hx, hxi⟩

theorem sum_reindex {M : Type*} [AddCommMonoid M] (f : ι → M) :
    (∑ i ∈ columns, f i) = ∑ x ∈ R.cartesian, f (R.index x) := by
  calc
    _ = ∑ i ∈ R.cartesian.image R.index, f i :=
      congrArg (fun s : Finset ι => ∑ i ∈ s, f i) R.image_eq.symm
    _ = _ := Finset.sum_image R.injective

theorem divisorPool_reindex :
    divisorPool columns (fun i => (ideal i).val) =
      divisorPool R.cartesian (fun x => (ideal (R.index x)).val) := by
  ext L
  constructor
  · intro hL
    obtain ⟨i, hi, hLi⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨x, hx, hxi⟩ := R.surjective i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa only [hxi] using hLi⟩
  · intro hL
    obtain ⟨x, hx, hLx⟩ := Finset.mem_biUnion.mp hL
    exact Finset.mem_biUnion.mpr ⟨R.index x, R.maps x hx, hLx⟩

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem energy_reindex (rows : Finset H) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    jointColumnEnergy rows columns q c x ξ =
      jointColumnEnergy rows R.cartesian q (fun h i => c h (R.index i))
        (fun h i => x h (R.index i)) ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h _
  have hp : jointFourierColumn columns (c h) (x h) ξ =
      jointFourierColumn R.cartesian (fun i => c h (R.index i))
        (fun i => x h (R.index i)) ξ :=
    R.sum_reindex (fun i => c h i * jointPhase ξ (x h i))
  rw [hp]

end CartesianSourceReindex

section ReindexKernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H ι κ : Type*} {k l : ℕ}
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]

theorem second_residual_kernel_reindex
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (left : Finset ι) (right : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (L : CartesianSourceReindex left IA k) (R : CartesianSourceReindex right IB l)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (q : H → ℂ) (c : ι → ℂ) (f : κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    secondResidualKernelCost (σ := σ) Ray F rows frequency left right ID IE IA IB d e hd he
      rayLeft rayRight phaseTable q c f x y =
      secondResidualKernelCost (σ := σ) Ray F rows frequency L.cartesian R.cartesian ID IE
        (fun i => IA (L.index i)) (fun j => IB (R.index j)) d e hd he
        (fun i => rayLeft (L.index i)) (fun j => rayRight (R.index j)) phaseTable q
        (fun i => c (L.index i)) (fun j => f (R.index j))
        (fun h i => x h (L.index i)) (fun h j => y h (R.index j)) := by
  unfold secondResidualKernelCost
  rw [R.divisorPool_reindex]
  apply Finset.sum_congr rfl
  intro D _
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    exact congrArg₂ (fun a b : ℝ =>
      ‖(FourierTransform.fourier F) ξ‖ * (Real.sqrt a * Real.sqrt b))
      (L.energy_reindex rows
        (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
        (kernelDivisorCoefficient (fun i => (IA i).val) D c
          (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
          (fun i h => σ (A.sexticResidue (IA i) (frequency h)))) x ξ)
      (R.energy_reindex rows
        (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
        (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) D f
          (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
          (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j)) y ξ)

/-- The complete original second kernel, reindexed and then allocated
on all plain and prime occurrences, with no aggregate premise. -/
theorem second_residual_kernel_cartesian_allocation
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (left : Finset ι) (right : Finset κ)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (L : CartesianSourceReindex left IA k) (R : CartesianSourceReindex right IB l)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : ι → Ray) (rayRight : κ → Ray) (phaseTable : Ray × Ray → Circle)
    (q : H → ℂ) (c : ι → ℂ) (f : κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    secondResidualKernelCost (σ := σ) Ray F rows frequency left right ID IE IA IB d e hd he
      rayLeft rayRight phaseTable q c f x y ≤
      secondAllocatedKernelCost (σ := σ) Ray F rows frequency
        L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots ID IE
        (fun i => IA (L.index i)) (fun j => IB (R.index j)) d e hd he
        (fun i => rayLeft (L.index i)) (fun j => rayRight (R.index j)) phaseTable q
        (fun i => c (L.index i)) (fun j => f (R.index j))
        (fun h i => x h (L.index i)) (fun h j => y h (R.index j)) := by
  rw [second_residual_kernel_reindex Ray F rows frequency left right ID IE IA IB L R
    d e hd he rayLeft rayRight phaseTable q c f x y]
  exact actual_second_kernel_allocation_bound Ray F rows frequency
    L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots ID IE
    (fun i => IA (L.index i)) (fun j => IB (R.index j)) L.ideal_product R.ideal_product
    d e hd he (fun i => rayLeft (L.index i)) (fun j => rayRight (R.index j)) phaseTable q
    (fun i => c (L.index i)) (fun j => f (R.index j))
    (fun h i => x h (L.index i)) (fun h j => y h (R.index j))

end ReindexKernel

section ActualChart

variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η htrace} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {hΓ μv hDiff}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)

def actualRows (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) :
    ActualSecondCorrelationRows A σ Q (Fin b.primeCount) where
  primes := b.primes
  primes_injective := b.primes_injective
  leftMultiplicity := b.leftMultiplicity
  rightMultiplicity := b.rightMultiplicity
  leftGenerator := engineAllowedGenerator C b.commonLeftIdeal
  rightGenerator := engineAllowedGenerator C b.commonRightIdeal
  leftGenerates := engineAllowedGenerator_generates C b.commonLeftIdeal
  rightGenerates := engineAllowedGenerator_generates C b.commonRightIdeal
  rows := (b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows.filter
    (fun q => chart.rowLabel q = label)
  originalIdeal q := ProbeOrbitNormSum.principalExterior A
    ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩
  frequency q := -q.out.val
  generates q _ := ProbeOrbitNormSum.principalExterior_generates A
    ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩
  weight q := secondOrbitalScalar radius D * chart.weight q

def sourceLeftCoefficient (i : ι) : ℂ :=
  chart.leftCoefficient i *
    (generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
      (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (b.secondLeft_generates C i)).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

def sourceRightCoefficient (j : κ) : ℂ :=
  chart.rightCoefficient j *
    (generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
      (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (b.secondRight_generates C j)).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val

def allocatedClassCost
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) {k l : ℕ}
    (label : Fin (chart.rowLabelCount + 1))
    (L : CartesianSourceReindex (b.leftColumns left) b.leftResidual k)
    (R : CartesianSourceReindex (b.rightColumns right) b.rightResidual l) : ℝ :=
  secondAllocatedKernelCost (σ := σ) PUnit.{1} chart.kernel
        (chart.actualRows M X hX label).rows
        (chart.actualRows M X hX label).frequency
        L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
        b.commonLeftIdeal b.commonRightIdeal
        (fun i => b.leftResidual (L.index i)) (fun j => b.rightResidual (R.index j))
        (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
        (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
        (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
        (chart.actualRows M X hX label).weight
        (fun i => chart.sourceLeftCoefficient (L.index i))
        (fun j => chart.sourceRightCoefficient (R.index j))
        (fun q i => chart.leftPoint q (L.index i))
        (fun q j => chart.rightPoint q (R.index j))

/-- A direct adapter from one genuine retained row class.  Its row
type fixes the actual support classification before the Cauchy step. -/
theorem classKernelCost_le_cartesian_allocation
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) {k l : ℕ}
    (label : Fin (chart.rowLabelCount + 1))
    (L : CartesianSourceReindex (b.leftColumns left) b.leftResidual k)
    (R : CartesianSourceReindex (b.rightColumns right) b.rightResidual l) :
    chart.classKernelCost M X hX label ≤ chart.allocatedClassCost M X hX label L R := by
  exact second_residual_kernel_cartesian_allocation PUnit.{1} chart.kernel
    ((b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows.filter
      (fun q => chart.rowLabel q = label))
    (fun q : Q => -q.out.val) (b.leftColumns left) (b.rightColumns right)
    b.commonLeftIdeal b.commonRightIdeal b.leftResidual b.rightResidual L R
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun q => secondOrbitalScalar radius D * chart.weight q)
    chart.sourceLeftCoefficient chart.sourceRightCoefficient
    chart.leftPoint chart.rightPoint

/-- Every original row label remains in the outer cost.  Its support
and exceptional classification is not discarded or charged for free. -/
theorem kernelCost_le_cartesian_allocation
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) {k l : ℕ}
    (L : CartesianSourceReindex (b.leftColumns left) b.leftResidual k)
    (R : CartesianSourceReindex (b.rightColumns right) b.rightResidual l) :
    chart.kernelCost M X hX ≤
      ∑ label : Fin (chart.rowLabelCount + 1), chart.allocatedClassCost M X hX label L R := by
  exact Finset.sum_le_sum (fun label _ =>
    chart.classKernelCost_le_cartesian_allocation M X hX label L R)

end SecondBlockProfileChart
end ActualChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_residual_kernel_cartesian_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.kernelCost_le_cartesian_allocation
