import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientBinding

/-!
# Actual second correlation rows and allocated child sources

Rows on which the complete common correlation vanishes are removed by
an exact finite-sum identity.  On every remaining row the proved local
correlation theorem constructs the residual ideal and its generator.
Both columns use this same residual ideal; the right column keeps the
negative frequency and negated Fourier locations required by its star.

The source coefficient identities below are derived from individual
plain/prime dictionaries.  Additional Gauss normalizers are computed
from the original factor normalizers and appear once outside the source
energy, separately from the child's central normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums HeckeGeneral.Characters
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Only the original common ideals, their chosen generators and actual
nonzero source frequencies are stored.  Extracted rows are constructed. -/
structure ActualSecondCorrelationRows (A : SArithmeticData F) (σ : F →+* ℂ)
    (H ι : Type*) [Fintype ι] where
  primes : ι → ExteriorPrime A
  primes_injective : Function.Injective primes
  leftMultiplicity : ι → ℕ
  rightMultiplicity : ι → ℕ
  leftGenerator : A.R
  rightGenerator : A.R
  leftGenerates : A.Generates (primePowerProduct primes leftMultiplicity) leftGenerator
  rightGenerates : A.Generates (primePowerProduct primes rightMultiplicity) rightGenerator
  rows : Finset H
  originalIdeal : H → A.Exterior
  frequency : H → A.R
  generates : ∀ h ∈ rows, A.Generates (originalIdeal h) (frequency h)
  weight : H → ℂ

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)

def correlation (h : H) : ℂ :=
  generatedIdealCorrelation (σ := σ)
    (primePowerProduct R.primes R.leftMultiplicity)
    (primePowerProduct R.primes R.rightMultiplicity)
    R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates (R.frequency h)

def live : Finset H := R.rows.filter (fun h => R.correlation h ≠ 0)

def factor (C : A.GeneralArithmeticContext σ η hS) (h : H) : A.R :=
  primePowerProductGenerator C R.primes
      (fun i => min (R.leftMultiplicity i) (R.rightMultiplicity i)) *
    nonunitFrequencyGenerator C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h)

def normFactor (C : A.GeneralArithmeticContext σ η hS) (h : H) : ℝ :=
  (Ideal.absNorm (gcd (primePowerProduct R.primes R.leftMultiplicity).val
    (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) *
    A.exteriorNorm (nonunitFrequencyRadical C R.primes R.leftMultiplicity
      R.rightMultiplicity (R.frequency h))

def extractedRow (C : A.GeneralArithmeticContext σ η hS) (h : R.live) :
    ActualChildRow (R.originalIdeal h.val) (R.frequency h.val)
      (R.factor C h.val) (R.normFactor C h.val) :=
  Classical.choice (exists_actual_extracted_child_row_of_generates C R.primes
    R.primes_injective R.leftMultiplicity R.rightMultiplicity
    R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
    (R.originalIdeal h.val) (R.frequency h.val)
    (R.generates h.val (Finset.mem_filter.mp h.property).1)
    (Finset.mem_filter.mp h.property).2)

/-- All omitted rows have weight zero because their actual correlation
vanishes; no analytic estimate is used for this restriction. -/
theorem energy_live {J : Type*} (columns : Finset J)
    (c : H → J → ℂ) (x : H → J → V) (ξ : V) :
    jointColumnEnergy R.rows columns (fun h => R.weight h * R.correlation h) c x ξ =
      jointColumnEnergy Finset.univ columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => c h.val) (fun h => x h.val) ξ := by
  unfold jointColumnEnergy
  calc
    _ = ∑ h ∈ R.live, ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn columns (c h) (x h) ξ‖ ^ 2 := by
      rw [live, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hz : R.correlation h = 0 <;> simp [hz]
    _ = _ := (Finset.sum_coe_sort R.live
      (fun h => ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn columns (c h) (x h) ξ‖ ^ 2)).symm

variable {k : ℕ} {Ray : Type*} [CommGroup Ray]

/-- A source on the actual allocation.  All fields precede the Fourier
variable, so its capacity choice also precedes both continuous modes
when V is the genuine Hilbert product. -/
def source (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (phase : Ray →* Circle)
    (D : SecondCoefficientTermDictionary T phase B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) :
    ActualAllocatedSource A V R.live k where
  allocation := B
  rows := Finset.univ
  weight h := R.weight h.val * R.correlation h.val
  originalIdeal h := R.originalIdeal h.val
  frequency h := R.frequency h.val
  extractedFactor h := R.factor C h.val
  normFactor h := R.normFactor C h.val
  row := R.extractedRow C
  characters _ := T
  scale₁ := D.scale₁
  scale₂ := D.scale₂
  base := D.base
  base_gt_one := hbase
  length := D.length
  length_pos := hlength
  leftWeight _ := D.leftWeight
  rightWeight _ := D.rightWeight
  slotWeight _ := D.slotWeight
  leftLocation h := x₁ h.val
  rightLocation h := x₂ h.val
  slotLocation h := x h.val

end ActualSecondCorrelationRows

namespace ActualAllocatedSource

variable {k : ℕ}

/-- The same actual residual ideal serves the conjugated right side.
Its complete character sees -g, and both continuous phases are negated
by negating their joint location. -/
def negativeSide (s : ActualAllocatedSource A V H k) : ActualAllocatedSource A V H k :=
  { s with
    frequency := fun h => -s.frequency h
    extractedFactor := fun h => -s.extractedFactor h
    row := fun h => (s.row h).negative
    leftLocation := fun h I => -s.leftLocation h I
    rightLocation := fun h I => -s.rightLocation h I
    slotLocation := fun h j p => -s.slotLocation h j p }

end ActualAllocatedSource

private theorem actual_allocation_column_mem {k : ℕ}
    (B : ActualColumnAllocation F k) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
    i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots := by
  rw [ActualColumnAllocation.columns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

private theorem joint_energy_coefficients_congr {J : Type*}
    (rows : Finset H) (columns : Finset J) (q : H → ℂ)
    (c f : H → J → ℂ) (x : H → J → V) (ξ : V)
    (hc : ∀ h ∈ rows, ∀ i ∈ columns, c h i = f h i) :
    jointColumnEnergy rows columns q c x ξ = jointColumnEnergy rows columns q f x ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have hp : jointFourierColumn columns (c h) (x h) ξ =
      jointFourierColumn columns (f h) (x h) ξ := by
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc h hh i hi]
  rw [hp]

namespace ActualSecondCorrelationRows

variable (R : ActualSecondCorrelationRows A σ H ι)
variable {k : ℕ} (Ray : Type*) [CommGroup Ray] [Fintype Ray]

/-- The literal left energy of secondAllocatedKernelCost is the energy
of its computed actual source, times the additional original Gauss
normalization.  All character and central identities come from the
single-factor dictionaries. -/
theorem left_energy_eq_source
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedLeftPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IA : AllocationColumn F k → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IA i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency D.ray χ
        (D.normalizedCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ =
      ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ ^ 2 *
        (R.source C B T (fixedLeftPhase Ray χ) D hbase hlength x₁ x₂ x).energy (σ := σ) ξ := by
  rw [R.energy_live]
  let s := R.source C B T (fixedLeftPhase Ray χ) D hbase hlength x₁ x₂ x
  let c := fun h : R.live => rawSourceCoefficient (σ := σ) T (R.factor C h.val)
    (R.extractedRow C h).element D.scale₁ D.scale₂ D.base D.length
      D.leftWeight D.rightWeight D.slotWeight
  have hc (h : R.live) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
      secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency D.ray χ
        (D.normalizedCoefficient u v t) h.val i =
      SecondCoefficientTermDictionary.centralNormalizer u v t * c h i :=
    D.normalized_coefficient_residue u v t i (actual_allocation_column_mem B i hi)
      (IA i) (hIA i (actual_allocation_column_mem B i hi))
      (R.frequency h.val) (R.factor C h.val) (R.extractedRow C h).element
      (R.extractedRow C h).frequency
  calc
    _ = jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => SecondCoefficientTermDictionary.centralNormalizer u v t * c h i)
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ :=
      joint_energy_coefficients_congr _ _ _ _ _ _ _ (fun h _ i hi => hc h i hi)
    _ = _ := joint_energy_constant_coefficient _ _ _ c _ _ ξ

/-- The right side is bound to an actual source on the same residual
ideals, after removing the star of the complete column. -/
theorem right_energy_eq_source
    (C : A.GeneralArithmeticContext σ η hS)
    (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k)
    (χ : (Ray × Ray) →* Circle)
    (D : SecondCoefficientTermDictionary T (fixedRightPhase Ray χ)
      B.plain₁ B.plain₂ B.slots)
    (hbase : 1 < D.base) (hlength : ∀ i, 0 < D.length i)
    (IB : AllocationColumn F k → A.Exterior)
    (hIB : ∀ i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots,
      (IB i).val = allocationColumnIdeal i)
    (u v : ℂ) (t : Fin k → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency D.ray χ
        (D.normalizedCoefficient u v t))
      (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) ξ =
      ‖SecondCoefficientTermDictionary.centralNormalizer u v t‖ ^ 2 *
        (R.source C B T (fixedRightPhase Ray χ) D hbase hlength x₁ x₂ x).negativeSide.energy
          (σ := σ) ξ := by
  rw [R.energy_live]
  let c := fun h : R.live => rawSourceCoefficient (σ := σ) T (-R.factor C h.val)
    (R.extractedRow C h).element D.scale₁ D.scale₂ D.base D.length
      D.leftWeight D.rightWeight D.slotWeight
  let ν := SecondCoefficientTermDictionary.centralNormalizer u v t
  have hc (h : R.live) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
      secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency D.ray χ
        (D.normalizedCoefficient u v t) h.val i = star ν * star (c h i) := by
    have he := D.normalized_coefficient_residue (σ := σ) u v t i
      (actual_allocation_column_mem B i hi) (IB i)
      (hIB i (actual_allocation_column_mem B i hi))
      (-R.frequency h.val) (-R.factor C h.val) (R.extractedRow C h).element
      ((congrArg Neg.neg (R.extractedRow C h).frequency).trans (neg_mul _ _).symm)
    exact (congrArg star he).trans (star_mul' _ _)
  calc
    _ = jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => star ν * star (c h i))
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ :=
      joint_energy_coefficients_congr _ _ _ _ _ _ _ (fun h _ i hi => hc h i hi)
    _ = ‖ν‖ ^ 2 * jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => star (c h i))
        (fun h => rawSourceLocation (x₁ h.val) (x₂ h.val) (x h.val)) ξ := by
      rw [joint_energy_constant_coefficient, norm_star]
    _ = _ := by
      rw [joint_energy_star_neg_locations]
      simp only [source, ActualAllocatedSource.negativeSide, ActualAllocatedSource.energy,
        ActualChildRow.negative]
      apply congrArg (fun locations : R.live → AllocationColumn F k → V =>
        ‖ν‖ ^ 2 * jointColumnEnergy Finset.univ B.columns
          (fun h : R.live => R.weight h.val * R.correlation h.val) c locations ξ)
      funext h i
      exact (rawSourceLocation_neg (x₁ h.val) (x₂ h.val) (x h.val) i).symm

end ActualSecondCorrelationRows
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.extractedRow
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.left_energy_eq_source
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.right_energy_eq_source
