import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedActualCapacityChild

/-!
# One actual second row class produces normalized capacity children

The input factorization concerns individual original Cartesian columns,
their finite ray labels and their Fourier locations.  The engine chooses
the witness of each nonempty divisor allocation, constructs its actual
side frames, and proves equality with the literal allocated kernel
energies.  Empty allocations and nonsquarefree Möbius terms vanish
internally.

The final class theorem keeps the actual second divisor, finite phase
character and both allocation labels.  For every retained branch it
calls the genuine capacity and profile-normalization producers.  The
same row class is used on both sides; it was fixed in the original
complex source before Cauchy.  Ordinary rectangle inputs contain their
actual nonexceptional row calibrations, so this statement cannot be
used to discard exceptional centered cancellation.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum
open WholeAllocation UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}

def SecondColumnSide.actualCoefficient (side : SecondColumnSide)
    (Ray : Type*) [CommGroup Ray] [Fintype Ray]
    (ideal : AllocationColumn K k → A.Exterior) (frequency : H → A.R)
    (ray : AllocationColumn K k → Ray) (χ : (Ray × Ray) →* Circle)
    (c : AllocationColumn K k → ℂ) : H → AllocationColumn K k → ℂ :=
  match side with
  | .left => secondAllocatedLeftCoefficient (σ := σ) Ray ideal frequency ray χ c
  | .right => secondAllocatedRightCoefficient (σ := σ) Ray ideal frequency ray χ c

/-- A single original-column factorization, before any polynomial sum.
Its two plain factors and every prime occurrence retain their own
central normalizer and actual finite ray dictionary. -/
structure SecondRectangularFactors
    (R : ActualSecondCorrelationRows A σ H ι)
    (Ray : Type*) [CommGroup Ray] [Fintype Ray] (side : SecondColumnSide)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (ideal : AllocationColumn K k → A.Exterior)
    (ray : AllocationColumn K k → Ray) (c : AllocationColumn K k → ℂ)
    (point : H → AllocationColumn K k → V) (χ : (Ray × Ray) →* Circle) where
  characters : FixedChildCharacters K k
  dictionary : SecondCoefficientTermDictionary characters (side.phase Ray χ) S₁ S₂ S
  base_gt_one : 1 < dictionary.base
  length_pos : ∀ i, 0 < dictionary.length i
  plain₁_nonzero : ∀ I ∈ S₁, I ≠ 0
  plain₂_nonzero : ∀ I ∈ S₂, I ≠ 0
  ideal_product : ∀ i ∈ childCartesianColumns S₁ S₂ S, (ideal i).val = allocationColumnIdeal i
  gaussScale₁ : ℝ
  gaussScale₂ : ℝ
  gaussSlotScale : Fin k → ℝ
  gaussScale₁_pos : 0 < gaussScale₁
  gaussScale₂_pos : 0 < gaussScale₂
  gaussSlotScale_pos : ∀ i, 0 < gaussSlotScale i
  coefficient_factor : ∀ i ∈ childCartesianColumns S₁ S₂ S,
    c i = dictionary.normalizedCoefficient (Real.sqrt gaussScale₁ : ℂ)⁻¹
      (Real.sqrt gaussScale₂ : ℂ)⁻¹ (fun j => (Real.sqrt (gaussSlotScale j) : ℂ)⁻¹) i
  ray_factor : ∀ i ∈ childCartesianColumns S₁ S₂ S, ray i = dictionary.ray i
  leftLocation : H → HeckeGeneral.Analysis.NonzeroIdeal K → V
  rightLocation : H → HeckeGeneral.Analysis.NonzeroIdeal K → V
  slotLocation : H → Fin k → HeightOneSpectrum (𝓞 K) → V
  point_factor : ∀ h ∈ R.rows, ∀ i ∈ childCartesianColumns S₁ S₂ S,
    point h i = rawSourceLocation (leftLocation h) (rightLocation h) (slotLocation h) i

namespace SecondRectangularFactors

variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {side : SecondColumnSide}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {ideal : AllocationColumn K k → A.Exterior}
variable {ray : AllocationColumn K k → Ray} {c : AllocationColumn K k → ℂ}
variable {point : H → AllocationColumn K k → V} {χ : (Ray × Ray) →* Circle}
variable (f : SecondRectangularFactors R Ray side S₁ S₂ S ideal ray c point χ)

def allocation (L : Ideal (𝓞 K)) (a : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty) :
    ActualColumnAllocation K k where
  divisor := L
  selection := a
  plain₁ := S₁
  plain₂ := S₂
  slots := S
  plain₁_nonzero := f.plain₁_nonzero
  plain₂_nonzero := f.plain₂_nonzero
  witness := hne.choose
  witness_mem := hne.choose_spec

def frame (C : A.GeneralArithmeticContext σ η hS)
    (L : Ideal (𝓞 K)) (a : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty) :
    SecondSideFrame (V := V) C R Ray side k where
  allocation := f.allocation L a hne
  characters := f.characters
  phaseCharacter := χ
  dictionary := f.dictionary
  base_gt_one := f.base_gt_one
  length_pos := f.length_pos
  ideal := ideal
  ideal_product := f.ideal_product
  gaussScale₁ := f.gaussScale₁
  gaussScale₂ := f.gaussScale₂
  gaussSlotScale := f.gaussSlotScale
  gaussScale₁_pos := f.gaussScale₁_pos
  gaussScale₂_pos := f.gaussScale₂_pos
  gaussSlotScale_pos := f.gaussSlotScale_pos
  leftLocation := f.leftLocation
  rightLocation := f.rightLocation
  slotLocation := f.slotLocation

theorem frame_energy (C : A.GeneralArithmeticContext σ η hS)
    (L : Ideal (𝓞 K)) (a : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty)
    (ξ : V) :
    (f.frame C L a hne).energy ξ =
      jointColumnEnergy R.rows
        (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
        (fun h => R.weight h * R.correlation h)
        (side.actualCoefficient (σ := σ) Ray ideal R.frequency ray χ c) point ξ := by
  unfold SecondSideFrame.energy jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have hp :
      jointFourierColumn (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
        ((f.frame C L a hne).coefficient h)
        (fun i => rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h) i) ξ =
      jointFourierColumn (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
        (side.actualCoefficient (σ := σ) Ray ideal R.frequency ray χ c h) (point h) ξ := by
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∈ childCartesianColumns S₁ S₂ S := by
      rw [paired_allocated_columns_eq_filter] at hi
      exact (Finset.mem_filter.mp hi).1
    rw [f.point_factor h hh i hi']
    congr 1
    cases side <;>
      simp only [SecondSideFrame.coefficient, SecondColumnSide.actualCoefficient,
        frame, secondAllocatedLeftCoefficient, secondAllocatedRightCoefficient,
        f.coefficient_factor i hi', f.ray_factor i hi']
  rw [hp]

end SecondRectangularFactors

/-- All inputs are primitive calibrations or individual-profile
windows.  No capacity choice, energy inequality or normalized-family
membership is supplied. -/
structure SecondSideNormalization
    {R : ActualSecondCorrelationRows A σ H ι} {Ray : Type*}
    [CommGroup Ray] [Fintype Ray] {side : SecondColumnSide}
    {C : A.GeneralArithmeticContext σ η hS}
    (f : SecondSideFrame (V := V) C R Ray side k)
    (ω ψ : HeckeCharacter K)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ)) where
  calibration : f.source.Calibration (σ := σ) ω ψ
  capacity : calibration.CapacityInput
  amplitude : V → ℝ
  amplitude_pos : ∀ ξ, 0 < amplitude ξ
  bounds : Fin f.source.allocation.keep.card → ℝ
  bounds_nonneg : ∀ i, 0 ≤ bounds i
  factor : ∀ ξ i, capacity.primeBound ξ i = amplitude ξ ^ 2 * bounds i
  profile : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms
    (calibration.clippedData ξ) (amplitude ξ)

namespace SecondSideNormalization

variable {R : ActualSecondCorrelationRows A σ H ι} {Ray : Type*}
  [CommGroup Ray] [Fintype Ray] {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable {left : SecondSideFrame (V := V) C R Ray .left k}
variable {right : SecondSideFrame (V := V) C R Ray .right l}

def Produced (P : ProfileNormalizationInput K ω ψ)
    (lc : SecondSideNormalization left ω ψ rowDomain heightDomain window seminorms)
    (rc : SecondSideNormalization right ω ψ rowDomain heightDomain window seminorms) : Prop :=
  (∀ ξ, Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) = 0) ∨
    ∃ lchild : lc.calibration.CapacityChild lc.capacity,
    ∃ rchild : rc.calibration.CapacityChild rc.capacity, ∀ ξ,
      InFixedProfileWindow rowDomain heightDomain window seminorms
        (lchild.normalizedData P lc.amplitude lc.amplitude_pos ξ) ∧
      InFixedProfileWindow rowDomain heightDomain window seminorms
        (rchild.normalizedData P rc.amplitude rc.amplitude_pos ξ) ∧
      Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) ≤
        (Real.sqrt (lchild.envelopeFreeCost lc.bounds) *
            Real.sqrt (rchild.envelopeFreeCost rc.bounds) /
          (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
        (lc.amplitude ξ ^ (left.source.allocation.keep.card + 2) *
          rc.amplitude ξ ^ (right.source.allocation.keep.card + 2)) *
        (Real.sqrt (pairedEnergy (lchild.normalizedData P lc.amplitude lc.amplitude_pos ξ)
            lchild.parameters left.source.base (lc.calibration.height ξ)) *
          Real.sqrt (pairedEnergy (rchild.normalizedData P rc.amplitude rc.amplitude_pos ξ)
            rchild.parameters right.source.base (rc.calibration.height ξ)))

theorem produce (P : ProfileNormalizationInput K ω ψ)
    (lc : SecondSideNormalization left ω ψ rowDomain heightDomain window seminorms)
    (rc : SecondSideNormalization right ω ψ rowDomain heightDomain window seminorms) :
    Produced P lc rc :=
  actual_second_pair_produces_normalized_children left right lc.calibration rc.calibration
    lc.capacity rc.capacity P lc.amplitude rc.amplitude lc.amplitude_pos rc.amplitude_pos
    lc.bounds rc.bounds lc.bounds_nonneg rc.bounds_nonneg lc.factor rc.factor
    rowDomain heightDomain window seminorms lc.profile rc.profile

end SecondSideNormalization

section FiniteClass

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance secondClassProductionCircleCharacterFintype1 : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

/-- The literal labels of the actual second Möbius and allocation sums. -/
abbrev SecondAllocationBranch
    (T₁ T₂ : Finset (Ideal (𝓞 K)))
    (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (IB : AllocationColumn K l → A.Exterior) (k : ℕ) :=
  Σ L : divisorPool (childCartesianColumns T₁ T₂ T) (fun j => (IB j).val),
    ((Ray × Ray) →* Circle) ×
      (AllocationMass.idealAllocations L.val (k + 2)) ×
      (AllocationMass.idealAllocations L.val (l + 2))

variable {Ray}

namespace SecondAllocationBranch

variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {IB : AllocationColumn K l → A.Exterior}
variable (b : SecondAllocationBranch Ray T₁ T₂ T IB k)
variable (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))

def leftColumns : Finset (AllocationColumn K k) :=
  pairedAllocatedColumns b.1.val b.2.2.1.val S₁ S₂ S id id HeightOneSpectrum.asIdeal

def rightColumns : Finset (AllocationColumn K l) :=
  pairedAllocatedColumns b.1.val b.2.2.2.val T₁ T₂ T id id HeightOneSpectrum.asIdeal

def Live : Prop :=
  Squarefree b.1.val ∧ (b.leftColumns S₁ S₂ S).Nonempty ∧ b.rightColumns.Nonempty

def weight (phaseTable : Ray × Ray → Circle) : ℝ :=
  ‖(moebius b.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray phaseTable b.2.1‖

theorem weight_nonneg (phaseTable : Ray × Ray → Circle) : 0 ≤ b.weight phaseTable :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

end SecondAllocationBranch

def liveSecondAllocationBranches
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (IB : AllocationColumn K l → A.Exterior) :
    Finset (SecondAllocationBranch Ray T₁ T₂ T IB k) :=
  Finset.univ.filter (fun b => b.Live S₁ S₂ S)

variable (R : ActualSecondCorrelationRows A σ H ι)
variable (F : 𝓢(V, ℂ))
variable (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
variable (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
variable (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
variable (phaseTable : Ray × Ray → Circle)
variable (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
variable (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)

def secondAllocationBranchCost (b : SecondAllocationBranch Ray T₁ T₂ T IB k) : ℝ :=
  b.weight phaseTable * ∫ ξ : V, ‖(𝓕 F) ξ‖ *
    (Real.sqrt (jointColumnEnergy R.rows (b.leftColumns S₁ S₂ S)
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.2.1 c) x ξ) *
    Real.sqrt (jointColumnEnergy R.rows b.rightColumns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.2.1 f) y ξ))

theorem secondAllocationBranchCost_zero
    (b : SecondAllocationBranch Ray T₁ T₂ T IB k) (hb : ¬b.Live S₁ S₂ S) :
    secondAllocationBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b = 0 := by
  by_cases hsq : Squarefree b.1.val
  · by_cases hl : (b.leftColumns S₁ S₂ S).Nonempty
    · have hr : b.rightColumns = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun h => hb ⟨hsq, hl, h⟩)
      simp [secondAllocationBranchCost, hr, jointColumnEnergy, jointFourierColumn]
    · have he := Finset.not_nonempty_iff_eq_empty.mp hl
      simp [secondAllocationBranchCost, he, jointColumnEnergy, jointFourierColumn]
  · simp only [secondAllocationBranchCost, SecondAllocationBranch.weight,
      moebius_of_not_squarefree hsq, Int.cast_zero, norm_zero, zero_mul]

/-- Empty allocations and zero Möbius terms do not require any child
calibration.  They disappear from the genuine finite kernel internally. -/
theorem secondAllocatedKernelCost_eq_live_branches :
    secondAllocatedKernelCost (σ := σ) Ray F R.rows R.frequency S₁ S₂ S T₁ T₂ T
      (primePowerProduct R.primes R.leftMultiplicity)
      (primePowerProduct R.primes R.rightMultiplicity) IA IB
      R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
      rayLeft rayRight phaseTable R.weight c f x y =
    ∑ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      secondAllocationBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
        phaseTable c f x y b.val := by
  have hall :
      secondAllocatedKernelCost (σ := σ) Ray F R.rows R.frequency S₁ S₂ S T₁ T₂ T
        (primePowerProduct R.primes R.leftMultiplicity)
        (primePowerProduct R.primes R.rightMultiplicity) IA IB
        R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
        rayLeft rayRight phaseTable R.weight c f x y =
      ∑ b : SecondAllocationBranch Ray T₁ T₂ T IB k,
        secondAllocationBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
          phaseTable c f x y b := by
    simp only [secondAllocatedKernelCost, secondAllocationBranchCost,
      SecondAllocationBranch.weight, SecondAllocationBranch.leftColumns,
      SecondAllocationBranch.rightColumns, ActualSecondCorrelationRows.correlation,
      Fintype.sum_sigma, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    refine (Finset.sum_coe_sort
      (divisorPool (childCartesianColumns T₁ T₂ T) (fun j => (IB j).val)) _).symm.trans ?_
    apply Finset.sum_congr rfl
    intro L _
    apply Finset.sum_congr rfl
    intro χ _
    refine (Finset.sum_coe_sort (AllocationMass.idealAllocations L.val (k + 2)) _).symm.trans ?_
    apply Finset.sum_congr rfl
    intro a _
    exact (Finset.sum_coe_sort (AllocationMass.idealAllocations L.val (l + 2)) _).symm
  rw [hall, Finset.sum_coe_sort]
  unfold liveSecondAllocationBranches
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.Live S₁ S₂ S
  · simp only [hb, ite_true]
  · rw [if_neg hb]
    exact secondAllocationBranchCost_zero R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b hb


variable (C : A.GeneralArithmeticContext σ η hS)
variable (leftFactors : ∀ χ : (Ray × Ray) →* Circle,
  SecondRectangularFactors R Ray .left S₁ S₂ S IA rayLeft c x χ)
variable (rightFactors : ∀ χ : (Ray × Ray) →* Circle,
  SecondRectangularFactors R Ray .right T₁ T₂ T IB rayRight f y χ)

def secondLiveLeftFrame
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) :
    SecondSideFrame (V := V) C R Ray .left k :=
  (leftFactors b.val.2.1).frame C b.val.1.val b.val.2.2.1.val
    (Finset.mem_filter.mp b.property).2.2.1

def secondLiveRightFrame
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) :
    SecondSideFrame (V := V) C R Ray .right l :=
  (rightFactors b.val.2.1).frame C b.val.1.val b.val.2.2.2.val
    (Finset.mem_filter.mp b.property).2.2.2

def secondProducedBranchCost
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) : ℝ :=
  b.val.weight phaseTable * ∫ ξ : V, ‖(𝓕 F) ξ‖ *
    (Real.sqrt ((secondLiveLeftFrame R S₁ S₂ S T₁ T₂ T IA IB rayLeft c x C leftFactors b).energy ξ) *
      Real.sqrt ((secondLiveRightFrame R S₁ S₂ S T₁ T₂ T IB rayRight f y C rightFactors b).energy ξ))

theorem secondAllocationBranchCost_eq_produced
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) :
    secondAllocationBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b.val =
    secondProducedBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y C leftFactors rightFactors b := by
  apply congrArg (fun t : ℝ => b.val.weight phaseTable * t)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    have hl := (leftFactors b.val.2.1).frame_energy C b.val.1.val b.val.2.2.1.val
      (Finset.mem_filter.mp b.property).2.2.1 ξ
    have hr := (rightFactors b.val.2.1).frame_energy C b.val.1.val b.val.2.2.2.val
      (Finset.mem_filter.mp b.property).2.2.2 ξ
    exact (congrArg (fun z : ℝ × ℝ => ‖(𝓕 F) ξ‖ * (Real.sqrt z.1 * Real.sqrt z.2))
      (Prod.ext hl hr)).symm

variable {ω ψ : HeckeCharacter K}
variable (P : ProfileNormalizationInput K ω ψ)
variable (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
variable (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))

/-- Every actual second-divisor branch has been bound to its true
source frames before the producing theorem is called.  The right
conjuguation and frequency sign are inside those frames. -/
theorem secondAllocatedKernel_produces_normalized_children
    (lc : ∀ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      SecondSideNormalization
        (secondLiveLeftFrame R S₁ S₂ S T₁ T₂ T IA IB rayLeft c x C leftFactors b)
        ω ψ rowDomain heightDomain window seminorms)
    (rc : ∀ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      SecondSideNormalization
        (secondLiveRightFrame R S₁ S₂ S T₁ T₂ T IB rayRight f y C rightFactors b)
        ω ψ rowDomain heightDomain window seminorms) :
    (secondAllocatedKernelCost (σ := σ) Ray F R.rows R.frequency S₁ S₂ S T₁ T₂ T
      (primePowerProduct R.primes R.leftMultiplicity)
      (primePowerProduct R.primes R.rightMultiplicity) IA IB
      R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
      rayLeft rayRight phaseTable R.weight c f x y =
      ∑ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
        secondProducedBranchCost R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
          phaseTable c f x y C leftFactors rightFactors b) ∧
    ∀ b, SecondSideNormalization.Produced P (lc b) (rc b) := by
  constructor
  · rw [secondAllocatedKernelCost_eq_live_branches R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y]
    exact Finset.sum_congr rfl fun b _ =>
      secondAllocationBranchCost_eq_produced R F S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
        phaseTable c f x y C leftFactors rightFactors b
  · intro b
    exact SecondSideNormalization.produce P (lc b) (rc b)


end FiniteClass


section ActualChart

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance secondClassProductionCircleCharacterFintype2 : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {block : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff block C left right
  profiles finiteTest radius D)
variable (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
variable (label : Fin (chart.rowLabelCount + 1))
variable (L : CartesianSourceReindex (block.leftColumns left) block.leftResidual k)
variable (R : CartesianSourceReindex (block.rightColumns right) block.rightResidual l)

local notation "Rows" => chart.actualRows M X hX label
local notation "IA" => (fun i => block.leftResidual (L.index i))
local notation "IB" => (fun i => block.rightResidual (R.index i))
local notation "rayL" => (fun _ : AllocationColumn K k => (PUnit.unit : PUnit.{1}))
local notation "rayR" => (fun _ : AllocationColumn K l => (PUnit.unit : PUnit.{1}))
local notation "cL" => (fun i => chart.sourceLeftCoefficient (L.index i))
local notation "cR" => (fun i => chart.sourceRightCoefficient (R.index i))
local notation "xL" => (fun q i => chart.leftPoint q (L.index i))
local notation "xR" => (fun q i => chart.rightPoint q (R.index i))
local notation "branches" => liveSecondAllocationBranches (Ray := PUnit.{1})
  L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots IB

/-- The complete class-production bridge from the literal source chart.
All output children are constructed from the original individual
column dictionaries and actual extracted rows.  The Fourier integrals
still use the chart's original kernel. -/
theorem class_produces_normalized_children
    {ω ψ : HeckeCharacter K}
    (P : ProfileNormalizationInput K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))
    (lf : ∀ χ : (PUnit.{1} × PUnit.{1}) →* Circle,
      SecondRectangularFactors Rows PUnit.{1} .left L.plain₁ L.plain₂ L.slots IA rayL cL xL χ)
    (rf : ∀ χ : (PUnit.{1} × PUnit.{1}) →* Circle,
      SecondRectangularFactors Rows PUnit.{1} .right R.plain₁ R.plain₂ R.slots IB rayR cR xR χ)
    (lc : ∀ b : branches,
      SecondSideNormalization
        (secondLiveLeftFrame Rows L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
          IA IB rayL cL xL C lf b)
        ω ψ rowDomain heightDomain window seminorms)
    (rc : ∀ b : branches,
      SecondSideNormalization
        (secondLiveRightFrame Rows L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots
          IB rayR cR xR C rf b)
        ω ψ rowDomain heightDomain window seminorms) :
    (chart.classKernelCost M X hX label ≤
      ∑ b : branches,
        secondProducedBranchCost Rows chart.kernel L.plain₁ L.plain₂ L.slots
          R.plain₁ R.plain₂ R.slots IA IB rayL rayR (fun _ => (1 : Circle))
          cL cR xL xR C lf rf b) ∧
    ∀ b, SecondSideNormalization.Produced P (lc b) (rc b) := by
  have h := secondAllocatedKernel_produces_normalized_children (Ray := PUnit.{1}) Rows chart.kernel
    L.plain₁ L.plain₂ L.slots R.plain₁ R.plain₂ R.slots IA IB rayL rayR
    (fun _ => (1 : Circle)) cL cR xL xR C lf rf P
    rowDomain heightDomain window seminorms lc rc
  refine ⟨?_, h.2⟩
  exact (chart.classKernelCost_le_cartesian_allocation M X hX label L R).trans_eq h.1

end SecondBlockProfileChart
end ActualChart


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondRectangularFactors.frame_energy
#print axioms HeckeSkeleton.Moments.EngineStep.secondAllocatedKernel_produces_normalized_children
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.class_produces_normalized_children

