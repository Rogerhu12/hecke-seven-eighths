import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstWeightedReduction

/-!
# The literal finite labels of the second allocation kernel

The divisor carrier and both occurrence-allocation carriers are those
computed by the actual second kernel.  Empty Cartesian allocations are
removed by an exact zero identity.  Every retained label constructs its
two actual allocation objects, with no choice depending on a Fourier
parameter.  This is the carrier used for the final child kernel family.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum WholeAllocation UniqueFactorizationMonoid
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance secondAllocationLabelsCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

abbrev SecondAllocationLabel
    (T₁ T₂ : Finset (Ideal (𝓞 F)))
    (T : Fin l → Finset (HeightOneSpectrum (𝓞 F)))
    (IB : AllocationColumn F l → A.Exterior) (k : ℕ) :=
  Σ L : divisorPool (childCartesianColumns T₁ T₂ T) (fun j => (IB j).val),
    Σ _χ : (Ray × Ray) →* Circle,
      Σ _a : AllocationMass.idealAllocations L.val (k + 2),
        AllocationMass.idealAllocations L.val (l + 2)

variable {Ray}
variable {S₁ S₂ T₁ T₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 F))}
variable {IB : AllocationColumn F l → A.Exterior}

namespace SecondAllocationLabel

variable (z : SecondAllocationLabel Ray T₁ T₂ T IB k)

def leftColumns (S₁ S₂ : Finset (Ideal (𝓞 F)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 F))) : Finset (AllocationColumn F k) :=
  pairedAllocatedColumns z.1.val z.2.2.1.val S₁ S₂ S id id HeightOneSpectrum.asIdeal

def rightColumns : Finset (AllocationColumn F l) :=
  pairedAllocatedColumns z.1.val z.2.2.2.val T₁ T₂ T id id HeightOneSpectrum.asIdeal

def weight (phaseTable : Ray × Ray → Circle) : ℝ :=
  ‖(moebius z.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray phaseTable z.2.1‖

theorem weight_nonneg (phaseTable : Ray × Ray → Circle) : 0 ≤ z.weight phaseTable :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

def pairEnergy (R : ActualSecondCorrelationRows A σ H ι)
    (IA : AllocationColumn F k → A.Exterior)
    (rayLeft : AllocationColumn F k → Ray) (rayRight : AllocationColumn F l → Ray)
    (c : AllocationColumn F k → ℂ) (f : AllocationColumn F l → ℂ)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V) (ξ : V) : ℝ :=
  Real.sqrt (jointColumnEnergy R.rows (z.leftColumns S₁ S₂ S)
    (fun h => R.weight h * R.correlation h)
    (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft z.2.1 c) x ξ) *
  Real.sqrt (jointColumnEnergy R.rows z.rightColumns
    (fun h => R.weight h * R.correlation h)
    (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight z.2.1 f) y ξ)

theorem pairEnergy_eq_zero_of_empty (R : ActualSecondCorrelationRows A σ H ι)
    (IA : AllocationColumn F k → A.Exterior)
    (rayLeft : AllocationColumn F k → Ray) (rayRight : AllocationColumn F l → Ray)
    (c : AllocationColumn F k → ℂ) (f : AllocationColumn F l → ℂ)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V)
    (he : ¬ ((z.leftColumns S₁ S₂ S).Nonempty ∧ z.rightColumns.Nonempty)) (ξ : V) :
    z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA rayLeft rayRight c f x y ξ = 0 := by
  have hz : z.leftColumns S₁ S₂ S = ∅ ∨ z.rightColumns = ∅ := by
    by_cases hl : (z.leftColumns S₁ S₂ S).Nonempty
    · exact Or.inr (Finset.not_nonempty_iff_eq_empty.mp (fun hr => he ⟨hl, hr⟩))
    · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hl)
  rcases hz with hl | hr
  · simp only [pairEnergy, hl, jointColumnEnergy, jointFourierColumn, Finset.sum_empty,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero,
      Real.sqrt_zero, zero_mul]
  · simp only [pairEnergy, hr, jointColumnEnergy, jointFourierColumn, Finset.sum_empty,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero,
      Real.sqrt_zero]

/-- Integrability is automatic for the original finite allocated
columns: their joint Fourier phases have modulus one and the common
Schwartz transform supplies the integrable density. -/
theorem pairEnergy_integrable (Fker : 𝓢(V, ℂ))
    (R : ActualSecondCorrelationRows A σ H ι)
    (IA : AllocationColumn F k → A.Exterior)
    (rayLeft : AllocationColumn F k → Ray) (rayRight : AllocationColumn F l → Ray)
    (c : AllocationColumn F k → ℂ) (f : AllocationColumn F l → ℂ)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V) :
    Integrable (z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA rayLeft rayRight c f x y)
      (actualFourierMeasure Fker) := by
  have hm : Measurable (fun ξ : V => ENNReal.ofReal ‖(𝓕 Fker) ξ‖) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun ξ : V => ENNReal.ofReal_lt_top))).mpr
  simpa only [pairEnergy, ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using
    joint_kernel_energy_integrable Fker R.rows (z.leftColumns S₁ S₂ S) z.rightColumns
      (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft z.2.1 c)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight z.2.1 f) x y

end SecondAllocationLabel

variable (Ray)

def liveSecondAllocationLabels
    (S₁ S₂ : Finset (Ideal (𝓞 F))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (T₁ T₂ : Finset (Ideal (𝓞 F))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 F)))
    (IB : AllocationColumn F l → A.Exterior) : Finset (SecondAllocationLabel Ray T₁ T₂ T IB k) :=
  Finset.univ.filter (fun z => (z.leftColumns S₁ S₂ S).Nonempty ∧ z.rightColumns.Nonempty)

variable {Ray}

def secondLabelLeftAllocation
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB) : ActualColumnAllocation F k :=
  actualAllocationOfNonempty z.val.1.val z.val.2.2.1.val S₁ S₂ S hS₁ hS₂
    (Finset.mem_filter.mp z.property).2.1

def secondLabelRightAllocation
    (hT₁ : ∀ I ∈ T₁, I ≠ 0) (hT₂ : ∀ I ∈ T₂, I ≠ 0)
    (z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB) : ActualColumnAllocation F l :=
  actualAllocationOfNonempty z.val.1.val z.val.2.2.2.val T₁ T₂ T hT₁ hT₂
    (Finset.mem_filter.mp z.property).2.2

theorem secondLabelLeftAllocation_columns
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB) :
    (secondLabelLeftAllocation hS₁ hS₂ z).columns = z.val.leftColumns S₁ S₂ S := rfl

theorem secondLabelRightAllocation_columns
    (hT₁ : ∀ I ∈ T₁, I ≠ 0) (hT₂ : ∀ I ∈ T₂, I ≠ 0)
    (z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB) :
    (secondLabelRightAllocation hT₁ hT₂ z).columns = z.val.rightColumns := rfl

variable (Ray)

/-- Flatten exactly the original divisor, finite phase and two
allocation sums.  No analytic or arithmetic mass estimate enters. -/
theorem secondAllocatedKernelCost_eq_labels
    (Fker : 𝓢(V, ℂ)) (R : ActualSecondCorrelationRows A σ H ι)
    (S₁ S₂ : Finset (Ideal (𝓞 F))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (T₁ T₂ : Finset (Ideal (𝓞 F))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 F)))
    (IA : AllocationColumn F k → A.Exterior) (IB : AllocationColumn F l → A.Exterior)
    (rayLeft : AllocationColumn F k → Ray) (rayRight : AllocationColumn F l → Ray)
    (phaseTable : Ray × Ray → Circle)
    (c : AllocationColumn F k → ℂ) (f : AllocationColumn F l → ℂ)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V) :
    secondAllocatedKernelCost (σ := σ) Ray Fker R.rows R.frequency S₁ S₂ S T₁ T₂ T
      (primePowerProduct R.primes R.leftMultiplicity) (primePowerProduct R.primes R.rightMultiplicity)
      IA IB R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
      rayLeft rayRight phaseTable R.weight c f x y =
      ∑ z : SecondAllocationLabel Ray T₁ T₂ T IB k,
        z.weight phaseTable * ∫ ξ : V, ‖(𝓕 Fker) ξ‖ *
          z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA rayLeft rayRight c f x y ξ := by
  simp only [SecondAllocationLabel, Fintype.sum_sigma,
    secondAllocatedKernelCost, SecondAllocationLabel.weight, SecondAllocationLabel.pairEnergy,
    SecondAllocationLabel.leftColumns, SecondAllocationLabel.rightColumns,
    ActualSecondCorrelationRows.correlation, Finset.mul_sum, mul_assoc]
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

/-- Empty allocation branches are removed by their literal zero
polynomial; all other original labels and weights remain unchanged. -/
theorem secondAllocatedKernelCost_eq_live_labels
    (Fker : 𝓢(V, ℂ)) (R : ActualSecondCorrelationRows A σ H ι)
    (S₁ S₂ : Finset (Ideal (𝓞 F))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 F)))
    (T₁ T₂ : Finset (Ideal (𝓞 F))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 F)))
    (IA : AllocationColumn F k → A.Exterior) (IB : AllocationColumn F l → A.Exterior)
    (rayLeft : AllocationColumn F k → Ray) (rayRight : AllocationColumn F l → Ray)
    (phaseTable : Ray × Ray → Circle)
    (c : AllocationColumn F k → ℂ) (f : AllocationColumn F l → ℂ)
    (x : H → AllocationColumn F k → V) (y : H → AllocationColumn F l → V) :
    secondAllocatedKernelCost (σ := σ) Ray Fker R.rows R.frequency S₁ S₂ S T₁ T₂ T
      (primePowerProduct R.primes R.leftMultiplicity) (primePowerProduct R.primes R.rightMultiplicity)
      IA IB R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
      rayLeft rayRight phaseTable R.weight c f x y =
      ∑ z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB,
        z.val.weight phaseTable * ∫ ξ : V, ‖(𝓕 Fker) ξ‖ *
          z.val.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA rayLeft rayRight c f x y ξ := by
  rw [secondAllocatedKernelCost_eq_labels]
  let cost : SecondAllocationLabel Ray T₁ T₂ T IB k → ℝ := fun z =>
    z.weight phaseTable * ∫ ξ : V, ‖(𝓕 Fker) ξ‖ *
      z.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA rayLeft rayRight c f x y ξ
  change (∑ z, cost z) =
    ∑ z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB, cost z.val
  calc
    _ = ∑ z ∈ liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB, cost z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have he : ¬ ((z.leftColumns S₁ S₂ S).Nonempty ∧ z.rightColumns.Nonempty) := by
        intro hne
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      simp only [cost, z.pairEnergy_eq_zero_of_empty R IA rayLeft rayRight c f x y he,
        mul_zero, integral_zero]
    _ = _ := (Finset.sum_coe_sort _ cost).symm

variable {η : RayClassCharacter F A.modulus}
variable {hS : A.ContainsTraceBadPlaces}

/-- Each retained original finite label is bound to the two computed
actual allocated sources.  The right source keeps its negative frequency
and negated joint locations.  The equality follows from the individual
term dictionaries, not an assumed whole-polynomial equality. -/
theorem secondAllocationLabel_pair_eq_actual_sources
    (R : ActualSecondCorrelationRows A σ H ι)
    (C : A.GeneralArithmeticContext σ η hS)
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (hT₁ : ∀ I ∈ T₁, I ≠ 0) (hT₂ : ∀ I ∈ T₂, I ≠ 0)
    (z : liveSecondAllocationLabels Ray S₁ S₂ S T₁ T₂ T IB)
    (leftCharacters : FixedChildCharacters F k) (rightCharacters : FixedChildCharacters F l)
    (DL : SecondCoefficientTermDictionary leftCharacters (fixedLeftPhase Ray z.val.2.1) S₁ S₂ S)
    (DR : SecondCoefficientTermDictionary rightCharacters (fixedRightPhase Ray z.val.2.1) T₁ T₂ T)
    (hbaseL : 1 < DL.base) (hlengthL : ∀ i, 0 < DL.length i)
    (hbaseR : 1 < DR.base) (hlengthR : ∀ i, 0 < DR.length i)
    (IA : AllocationColumn F k → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (hIB : ∀ i ∈ childCartesianColumns T₁ T₂ T, (IB i).val = allocationColumnIdeal i)
    (uL vL uR vR : ℂ) (tL : Fin k → ℂ) (tR : Fin l → ℂ)
    (x₁ x₂ y₁ y₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V)
    (y : H → Fin l → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    z.val.pairEnergy (S₁ := S₁) (S₂ := S₂) (S := S) R IA DL.ray DR.ray
      (DL.normalizedCoefficient uL vL tL) (DR.normalizedCoefficient uR vR tR)
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h))
      (fun h => rawSourceLocation (y₁ h) (y₂ h) (y h)) ξ =
    Real.sqrt (‖SecondCoefficientTermDictionary.centralNormalizer uL vL tL‖ ^ 2 *
      (R.source C (secondLabelLeftAllocation hS₁ hS₂ z) leftCharacters
        (fixedLeftPhase Ray z.val.2.1) DL hbaseL hlengthL x₁ x₂ x).energy (σ := σ) ξ) *
    Real.sqrt (‖SecondCoefficientTermDictionary.centralNormalizer uR vR tR‖ ^ 2 *
      (R.source C (secondLabelRightAllocation hT₁ hT₂ z) rightCharacters
        (fixedRightPhase Ray z.val.2.1) DR hbaseR hlengthR y₁ y₂ y).negativeSide.energy (σ := σ) ξ) := by
  unfold SecondAllocationLabel.pairEnergy
  rw [← secondLabelLeftAllocation_columns hS₁ hS₂ z,
    ← secondLabelRightAllocation_columns hT₁ hT₂ z]
  exact congrArg₂ (fun a b : ℝ => Real.sqrt a * Real.sqrt b)
    (R.left_energy_eq_source Ray C (secondLabelLeftAllocation hS₁ hS₂ z) leftCharacters
      z.val.2.1 DL hbaseL hlengthL IA hIA uL vL tL x₁ x₂ x ξ)
    (R.right_energy_eq_source Ray C (secondLabelRightAllocation hT₁ hT₂ z) rightCharacters
      z.val.2.1 DR hbaseR hlengthR IB hIB uR vR tR y₁ y₂ y ξ)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.secondAllocatedKernelCost_eq_labels
#print axioms HeckeSkeleton.Moments.EngineStep.secondAllocatedKernelCost_eq_live_labels
#print axioms HeckeSkeleton.Moments.EngineStep.secondAllocationLabel_pair_eq_actual_sources
