import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondClassProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedSecondResidual

/-!
# Actual allocated children under the original two-frequency measure

The measure lives on the ordinary product. Both Fourier locations live
in its actual Hilbert WithLp 2 version. Every source frame, allocation,
capacity deletion and profile family is fixed before either frequency.

This file repeats neither Fourier inversion nor a profile comparison:
it applies the proved finite whole-column allocation inside the original
positive finite measure, and then the genuine normalized child producer.
No product Haar Jacobian, independent pool, or extra central denominator
is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι] {k l : ℕ}

local notation "W" => WithLp 2 (U × V)

theorem allocated_joint_measure_bound
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (L : Ideal (𝓞 K)) (hL : Squarefree L) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (q : H → ℂ) (c : H → AllocationColumn K k → ℂ)
    (f : H → AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → W) (y : H → AllocationColumn K l → W) :
    (∫ z, Real.sqrt (jointColumnEnergy rows
      ((childCartesianColumns S₁ S₂ S).filter (fun i => L ∣ allocationColumnIdeal i))
      q c x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows
        ((childCartesianColumns T₁ T₂ T).filter (fun j => L ∣ allocationColumnIdeal j))
        q f y (WithLp.toLp 2 z)) ∂μ) ≤
    ∑ a ∈ AllocationMass.idealAllocations L (k + 2),
      ∑ b ∈ AllocationMass.idealAllocations L (l + 2),
        ∫ z, Real.sqrt (jointColumnEnergy rows
          (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
          q c x (WithLp.toLp 2 z)) *
          Real.sqrt (jointColumnEnergy rows
            (pairedAllocatedColumns L b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
            q f y (WithLp.toLp 2 z)) ∂μ := by
  let AL := AllocationMass.idealAllocations L (k + 2)
  let AR := AllocationMass.idealAllocations L (l + 2)
  let integrand := fun a b (z : U × V) =>
    Real.sqrt (jointColumnEnergy rows
      (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
      q c x (WithLp.toLp 2 z)) *
    Real.sqrt (jointColumnEnergy rows
      (pairedAllocatedColumns L b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
      q f y (WithLp.toLp 2 z))
  have hi a b : Integrable (integrand a b) μ :=
    nested_joint_cauchy_integrable rows _ _ q c f x y μ
  calc
    _ ≤ ∫ z, ∑ a ∈ AL, ∑ b ∈ AR, integrand a b z ∂μ := by
      apply integral_mono (nested_joint_cauchy_integrable rows _ _ q c f x y μ)
        (integrable_finsetSum AL (fun a _ => integrable_finsetSum AR (fun b _ => hi a b)))
      intro z
      have hl := sqrt_joint_energy_divisor_allocation L hL rows S₁ S₂ S
        id id HeightOneSpectrum.asIdeal q c x (WithLp.toLp 2 z)
      have hr := sqrt_joint_energy_divisor_allocation L hL rows T₁ T₂ T
        id id HeightOneSpectrum.asIdeal q f y (WithLp.toLp 2 z)
      apply (mul_le_mul hl hr (Real.sqrt_nonneg _)
        (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)).trans_eq
      simp only [Finset.sum_mul_sum, integrand]
    _ = _ := by
      rw [integral_finsetSum AL (fun a _ => integrable_finsetSum AR (fun b _ => hi a b))]
      exact Finset.sum_congr rfl fun a _ => integral_finsetSum AR (fun b _ => hi a b)

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _
variable (R : ActualSecondCorrelationRows A σ H ι)

def actualMeasuredSecondKernelCost {α β : Type*}
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W) : ℝ :=
  ∑ L ∈ divisorPool right (fun j => (IB j).val), ‖(moebius L : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∫ z, Real.sqrt (jointColumnEnergy R.rows left
        (fun h => R.weight h * R.correlation h)
        (kernelDivisorCoefficient (fun i => (IA i).val) L c
          (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
          (fun i h => σ (A.sexticResidue (IA i) (R.frequency h)))) x (WithLp.toLp 2 z)) *
        Real.sqrt (jointColumnEnergy R.rows right
          (fun h => R.weight h * R.correlation h)
          (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
            (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
            (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) y (WithLp.toLp 2 z)) ∂μ

def actualMeasuredAllocatedKernelCost
    (μ : Measure (U × V))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle) (c : AllocationColumn K k → ℂ)
    (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → W) (y : H → AllocationColumn K l → W) : ℝ :=
  ∑ L ∈ divisorPool (childCartesianColumns T₁ T₂ T) (fun j => (IB j).val), ‖(moebius L : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      ∑ a ∈ AllocationMass.idealAllocations L (k + 2),
        ∑ b ∈ AllocationMass.idealAllocations L (l + 2),
          ∫ z, Real.sqrt (jointColumnEnergy R.rows
            (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
            (fun h => R.weight h * R.correlation h)
            (secondAllocatedLeftCoefficient Ray IA R.frequency rayLeft χ c) x (WithLp.toLp 2 z)) *
            Real.sqrt (jointColumnEnergy R.rows
              (pairedAllocatedColumns L b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
              (fun h => R.weight h * R.correlation h)
              (secondAllocatedRightCoefficient Ray IB R.frequency rayRight χ f) y (WithLp.toLp 2 z)) ∂μ

theorem actual_measured_second_allocation_bound
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (hIB : ∀ i ∈ childCartesianColumns T₁ T₂ T, (IB i).val = allocationColumnIdeal i)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle) (c : AllocationColumn K k → ℂ)
    (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → W) (y : H → AllocationColumn K l → W) :
    actualMeasuredSecondKernelCost Ray R μ
      (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
      IA IB rayLeft rayRight phaseTable c f x y ≤
    actualMeasuredAllocatedKernelCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y := by
  unfold actualMeasuredSecondKernelCost actualMeasuredAllocatedKernelCost
  apply Finset.sum_le_sum
  intro L hL
  by_cases hsq : Squarefree L
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro χ _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    let weight := fun h => R.weight h * R.correlation h
    have hl (z : U × V) :
        jointColumnEnergy R.rows (childCartesianColumns S₁ S₂ S) weight
          (kernelDivisorCoefficient (fun i => (IA i).val) L c
            (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
            (fun i h => σ (A.sexticResidue (IA i) (R.frequency h)))) x (WithLp.toLp 2 z) =
        jointColumnEnergy R.rows
          ((childCartesianColumns S₁ S₂ S).filter (fun i => L ∣ allocationColumnIdeal i)) weight
          (secondAllocatedLeftCoefficient Ray IA R.frequency rayLeft χ c) x (WithLp.toLp 2 z) := by
      unfold jointColumnEnergy
      apply Finset.sum_congr rfl
      intro h _
      have hp : jointFourierColumn (childCartesianColumns S₁ S₂ S)
          (kernelDivisorCoefficient (fun i => (IA i).val) L c
            (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
            (fun i h => σ (A.sexticResidue (IA i) (R.frequency h))) h) (x h) (WithLp.toLp 2 z) =
          jointFourierColumn
            ((childCartesianColumns S₁ S₂ S).filter (fun i => L ∣ allocationColumnIdeal i))
            (secondAllocatedLeftCoefficient Ray IA R.frequency rayLeft χ c h) (x h)
            (WithLp.toLp 2 z) := by
        simp only [jointFourierColumn, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        unfold kernelDivisorCoefficient
        rw [hIA i hi]
        split_ifs <;> simp only [secondAllocatedLeftCoefficient, zero_mul]
      rw [hp]
    have hr (z : U × V) :
        jointColumnEnergy R.rows (childCartesianColumns T₁ T₂ T) weight
          (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
            (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
            (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) y (WithLp.toLp 2 z) =
        jointColumnEnergy R.rows
          ((childCartesianColumns T₁ T₂ T).filter (fun j => L ∣ allocationColumnIdeal j)) weight
          (secondAllocatedRightCoefficient Ray IB R.frequency rayRight χ f) y (WithLp.toLp 2 z) := by
      unfold jointColumnEnergy
      apply Finset.sum_congr rfl
      intro h _
      have hp : jointFourierColumn (childCartesianColumns T₁ T₂ T)
          (fun j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
            (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
            (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) (y h) (WithLp.toLp 2 z) =
          jointFourierColumn
            ((childCartesianColumns T₁ T₂ T).filter (fun j => L ∣ allocationColumnIdeal j))
            (secondAllocatedRightCoefficient Ray IB R.frequency rayRight χ f h) (y h)
            (WithLp.toLp 2 z) := by
        simp only [jointFourierColumn, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        unfold kernelDivisorCoefficient
        rw [hIB j hj]
        split_ifs <;> simp only [secondAllocatedRightCoefficient, star_zero, zero_mul]
      rw [hp]
    simp_rw [hl, hr]
    exact allocated_joint_measure_bound μ L hsq R.rows S₁ S₂ S T₁ T₂ T weight
      (secondAllocatedLeftCoefficient Ray IA R.frequency rayLeft χ c)
      (secondAllocatedRightCoefficient Ray IB R.frequency rayRight χ f) x y
  · simp only [moebius_of_not_squarefree hsq, Int.cast_zero, norm_zero, zero_mul, le_refl]

/-- Individual source-column reindexing also commutes with the original
two-frequency measure. No integrability assumption is needed for this
exact identity. -/
theorem actual_measured_second_reindex {α β : Type*}
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (L : CartesianSourceReindex left IA k) (B : CartesianSourceReindex right IB l)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB rayLeft rayRight phaseTable c f x y =
    actualMeasuredSecondKernelCost Ray R μ L.cartesian B.cartesian
      (fun i => IA (L.index i)) (fun j => IB (B.index j))
      (fun i => rayLeft (L.index i)) (fun j => rayRight (B.index j)) phaseTable
      (fun i => c (L.index i)) (fun j => f (B.index j))
      (fun h i => x h (L.index i)) (fun h j => y h (B.index j)) := by
  unfold actualMeasuredSecondKernelCost
  rw [B.divisorPool_reindex]
  apply Finset.sum_congr rfl
  intro L' _
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    rw [L.energy_reindex, B.energy_reindex]


variable (μ : Measure (U × V))
variable (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
variable (IA : AllocationColumn K k → A.Exterior) (IB : AllocationColumn K l → A.Exterior)
variable (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
variable (phaseTable : Ray × Ray → Circle)
variable (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
variable (x : H → AllocationColumn K k → W) (y : H → AllocationColumn K l → W)

def measuredSecondBranchCost (b : SecondAllocationBranch Ray T₁ T₂ T IB k) : ℝ :=
  b.weight phaseTable * ∫ z, Real.sqrt (jointColumnEnergy R.rows (b.leftColumns S₁ S₂ S)
    (fun h => R.weight h * R.correlation h)
    (secondAllocatedLeftCoefficient Ray IA R.frequency rayLeft b.2.1 c) x (WithLp.toLp 2 z)) *
    Real.sqrt (jointColumnEnergy R.rows b.rightColumns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient Ray IB R.frequency rayRight b.2.1 f) y (WithLp.toLp 2 z)) ∂μ

theorem measuredSecondBranchCost_zero (b : SecondAllocationBranch Ray T₁ T₂ T IB k)
    (hb : ¬b.Live S₁ S₂ S) :
    measuredSecondBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b = 0 := by
  by_cases hsq : Squarefree b.1.val
  · by_cases hl : (b.leftColumns S₁ S₂ S).Nonempty
    · have hr : b.rightColumns = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun h => hb ⟨hsq, hl, h⟩)
      simp [measuredSecondBranchCost, hr, jointColumnEnergy, jointFourierColumn]
    · have he := Finset.not_nonempty_iff_eq_empty.mp hl
      simp [measuredSecondBranchCost, he, jointColumnEnergy, jointFourierColumn]
  · simp only [measuredSecondBranchCost, SecondAllocationBranch.weight,
      moebius_of_not_squarefree hsq, Int.cast_zero, norm_zero, zero_mul]

theorem actualMeasuredAllocatedKernelCost_eq_live :
    actualMeasuredAllocatedKernelCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight phaseTable c f x y =
    ∑ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      measuredSecondBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
        phaseTable c f x y b.val := by
  have hall :
      actualMeasuredAllocatedKernelCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB
        rayLeft rayRight phaseTable c f x y =
      ∑ b : SecondAllocationBranch Ray T₁ T₂ T IB k,
        measuredSecondBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
          phaseTable c f x y b := by
    simp only [actualMeasuredAllocatedKernelCost, measuredSecondBranchCost,
      SecondAllocationBranch.weight, SecondAllocationBranch.leftColumns,
      SecondAllocationBranch.rightColumns, Fintype.sum_sigma, Fintype.sum_prod_type,
      Finset.sum_coe_sort, Finset.mul_sum, mul_assoc]
  rw [hall, Finset.sum_coe_sort]
  unfold liveSecondAllocationBranches
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.Live S₁ S₂ S
  · simp only [hb, ite_true]
  · rw [if_neg hb]
    exact measuredSecondBranchCost_zero Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b hb

variable (C : A.GeneralArithmeticContext σ η hS)
variable (leftFactors : ∀ χ : (Ray × Ray) →* Circle,
  SecondRectangularFactors R Ray .left S₁ S₂ S IA rayLeft c x χ)
variable (rightFactors : ∀ χ : (Ray × Ray) →* Circle,
  SecondRectangularFactors R Ray .right T₁ T₂ T IB rayRight f y χ)

def measuredProducedBranchCost
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) : ℝ :=
  b.val.weight phaseTable * ∫ z,
    Real.sqrt ((secondLiveLeftFrame R S₁ S₂ S T₁ T₂ T IA IB rayLeft c x C leftFactors b).energy
      (WithLp.toLp 2 z)) *
    Real.sqrt ((secondLiveRightFrame R S₁ S₂ S T₁ T₂ T IB rayRight f y C rightFactors b).energy
      (WithLp.toLp 2 z)) ∂μ

theorem measuredSecondBranchCost_eq_produced
    (b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB) :
    measuredSecondBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y b.val =
    measuredProducedBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
      phaseTable c f x y C leftFactors rightFactors b := by
  unfold measuredSecondBranchCost measuredProducedBranchCost
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    unfold secondLiveLeftFrame secondLiveRightFrame
    rw [SecondRectangularFactors.frame_energy, SecondRectangularFactors.frame_energy]
    rfl

/-- This is the producing theorem used after genuine Fubini. The source
and its true Hilbert locations precede both continuous variables; the
positive measure remains on the original ordinary product. -/
theorem actual_measured_kernel_produces_normalized_children [IsFiniteMeasure μ]
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (hIB : ∀ i ∈ childCartesianColumns T₁ T₂ T, (IB i).val = allocationColumnIdeal i)
    {ω ψ : HeckeCharacter K}
    (P : ProfileNormalizationInput K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))
    (lc : ∀ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      SecondSideNormalization
        (secondLiveLeftFrame R S₁ S₂ S T₁ T₂ T IA IB rayLeft c x C leftFactors b)
        ω ψ rowDomain heightDomain window seminorms)
    (rc : ∀ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
      SecondSideNormalization
        (secondLiveRightFrame R S₁ S₂ S T₁ T₂ T IB rayRight f y C rightFactors b)
        ω ψ rowDomain heightDomain window seminorms) :
    (actualMeasuredSecondKernelCost Ray R μ
      (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
      IA IB rayLeft rayRight phaseTable c f x y ≤
      ∑ b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB,
        measuredProducedBranchCost Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
          phaseTable c f x y C leftFactors rightFactors b) ∧
    ∀ b, SecondSideNormalization.Produced P (lc b) (rc b) := by
  constructor
  · apply (actual_measured_second_allocation_bound Ray R μ S₁ S₂ S T₁ T₂ T IA IB
      hIA hIB rayLeft rayRight phaseTable c f x y).trans_eq
    rw [actualMeasuredAllocatedKernelCost_eq_live Ray R μ S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight phaseTable c f x y]
    exact Finset.sum_congr rfl fun b _ =>
      measuredSecondBranchCost_eq_produced Ray R μ S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight
        phaseTable c f x y C leftFactors rightFactors b
  · intro b
    exact SecondSideNormalization.produce P (lc b) (rc b)

section OriginalNestedKernel

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

/-- The original nested second transform is literally the measured
kernel above. Its right first-Fourier location is negative because
the whole original right coefficient was conjugated. -/
theorem nestedSecondResidualKernelCost_eq_actualMeasured {α β : Type*}
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(V, ℂ)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c : α → ℂ) (f : β → ℂ) (x₁ : α → U) (y₁ : β → U)
    (x₂ : H → α → V) (y₂ : H → β → V) :
    nestedSecondResidualKernelCost Ray F₁ F₂ R.rows R.frequency left right
      (primePowerProduct R.primes R.leftMultiplicity)
      (primePowerProduct R.primes R.rightMultiplicity) IA IB
      R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
      rayLeft rayRight phaseTable R.weight c f x₁ y₁ x₂ y₂ =
    actualMeasuredSecondKernelCost Ray R (nestedFourierMeasure F₁ F₂) left right
      IA IB rayLeft rayRight phaseTable c f
      (fun h i => WithLp.toLp 2 (x₁ i, x₂ h i))
      (fun h j => WithLp.toLp 2 (-y₁ j, y₂ h j)) := rfl

end OriginalNestedKernel

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_measured_second_allocation_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_measured_kernel_produces_normalized_children
#print axioms HeckeSkeleton.Moments.EngineStep.nestedSecondResidualKernelCost_eq_actualMeasured

