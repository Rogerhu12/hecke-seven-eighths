import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedChildKernel

/-!
# The original finite allocations produce normalized child kernels

Each label contains only its two actual sources, raw term calibrations,
primitive capacity ledgers, and original Gauss normalizers.  The retained
label set is computed by discarding a branch when either actual source
vanishes for every continuous parameter.  For every remaining original
label the proved capacity theorem chooses the two fixed removals.

Thus all choices precede the Fourier parameter, all nonzero original
labels occur, and the total positive mass is the sum of the exact same
computed weights and the precise pre-removal profile envelopes.  No
child moment bound or aggregate mass is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F}

structure ActualNormalizedPairFamily (A : SArithmeticData F) (σ : F →+* ℂ)
    (V Λ : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ω ψ : HeckeCharacter F) (Z : ℝ) where
  LeftRow : Λ → Type
  RightRow : Λ → Type
  leftSlots : Λ → ℕ
  rightSlots : Λ → ℕ
  leftSource : ∀ b, ActualAllocatedSource A V (LeftRow b) (leftSlots b)
  rightSource : ∀ b, ActualAllocatedSource A V (RightRow b) (rightSlots b)
  leftCalibration : ∀ b, (leftSource b).Calibration (σ := σ) ω ψ
  rightCalibration : ∀ b, (rightSource b).Calibration (σ := σ) ω ψ
  leftCapacity : ∀ b, (leftCalibration b).NormalizedCapacityData
  rightCapacity : ∀ b, (rightCalibration b).NormalizedCapacityData
  left_base : ∀ b, (leftSource b).base = Z
  right_base : ∀ b, (rightSource b).base = Z
  leftNormalizer : Λ → ℂ
  rightNormalizer : Λ → ℂ

namespace ActualNormalizedPairFamily

variable {Λ : Type*} {Z : ℝ}
variable (s : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

def active : Finset Λ := labels.filter (fun b =>
  ¬ (∀ ξ : V, (s.leftSource b).energy (σ := σ) ξ = 0) ∧
  ¬ (∀ ξ : V, (s.rightSource b).energy (σ := σ) ξ = 0))

def leftChild (b : s.active labels) : (s.leftCapacity b.val).Child :=
  Classical.choice ((s.leftCapacity b.val).zero_or_child.resolve_left
    (Finset.mem_filter.mp b.property).2.1)

def rightChild (b : s.active labels) : (s.rightCapacity b.val).Child :=
  Classical.choice ((s.rightCapacity b.val).zero_or_child.resolve_left
    (Finset.mem_filter.mp b.property).2.2)

/-- Actual normalized, restricted profiles with the evaluation height
frozen into the data.  These are the two zero-twist child moment data. -/
def leftData (b : s.active labels) (ξ : V) : MomentData F ω ψ :=
  (s.leftChild labels b).frozenData ξ

def rightData (b : s.active labels) (ξ : V) : MomentData F ω ψ :=
  (s.rightChild labels b).frozenData ξ

def leftParameters (b : s.active labels) : RealParameters := (s.leftChild labels b).parameters
def rightParameters (b : s.active labels) : RealParameters := (s.rightChild labels b).parameters

def sourcePair (parentWidth : ℝ) (b : Λ) (ξ : V) : ℝ :=
  (Real.sqrt (‖s.leftNormalizer b‖ ^ 2 * (s.leftSource b).energy (σ := σ) ξ) *
    Real.sqrt (‖s.rightNormalizer b‖ ^ 2 * (s.rightSource b).energy (σ := σ) ξ)) /
      Z ^ parentWidth

def childPair (b : s.active labels) (ξ : V) : ℝ :=
  Real.sqrt (normalizedPairedEnergy ((s.leftChild labels b).data ξ)
    (s.leftChild labels b).parameters Z ((s.leftCalibration b.val).height ξ)) *
  Real.sqrt (normalizedPairedEnergy ((s.rightChild labels b).data ξ)
    (s.rightChild labels b).parameters Z ((s.rightCalibration b.val).height ξ))

theorem childPair_eq_frozen (b : s.active labels) (ξ : V) :
    s.childPair labels b ξ =
      Real.sqrt (normalizedPairedEnergy (s.leftData labels b ξ) (s.leftParameters labels b) Z 0) *
        Real.sqrt (normalizedPairedEnergy (s.rightData labels b ξ) (s.rightParameters labels b) Z 0) := by
  simp only [leftData, rightData, leftParameters, rightParameters,
    ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.frozenData,
    normalizedPairedEnergy_frozenMomentProfiles] <;> rfl

def envelope (b : s.active labels) (ξ : V) : ℝ :=
  normalizedCapacityPairEnvelope (s.leftCapacity b.val) (s.rightCapacity b.val) ξ

def weight (parentWidth : ℝ) (b : s.active labels) : ℝ :=
  normalizedCapacityPairWeight (s.leftChild labels b) (s.rightChild labels b)
    (s.leftNormalizer b.val) (s.rightNormalizer b.val) Z parentWidth

theorem weight_nonneg (parentWidth : ℝ) (b : s.active labels) (hZ : 0 < Z) :
    0 ≤ s.weight labels parentWidth b :=
  normalizedCapacityPairWeight_nonneg _ _ _ _ _ _ hZ

theorem sourcePair_eq_zero_of_inactive (parentWidth : ℝ) (b : Λ)
    (hb : b ∈ labels) (hn : b ∉ s.active labels) (ξ : V) :
    s.sourcePair parentWidth b ξ = 0 := by
  have hz : (∀ ξ : V, (s.leftSource b).energy (σ := σ) ξ = 0) ∨
      (∀ ξ : V, (s.rightSource b).energy (σ := σ) ξ = 0) := by
    by_contra hz
    have h := not_or.mp hz
    exact hn (Finset.mem_filter.mpr ⟨hb, h.1, h.2⟩)
  rcases hz with hl | hr
  · simp only [sourcePair, hl ξ, mul_zero, Real.sqrt_zero, zero_mul, zero_div]
  · simp only [sourcePair, hr ξ, mul_zero, Real.sqrt_zero, zero_div]

theorem pointwise (parentWidth : ℝ) (hZ : 0 < Z)
    (b : s.active labels) (ξ : V) :
    s.sourcePair parentWidth b.val ξ ≤ s.weight labels parentWidth b * s.envelope labels b ξ * s.childPair labels b ξ :=
  normalized_capacity_pair_pointwise (s.leftChild labels b) (s.rightChild labels b)
    (s.leftNormalizer b.val) (s.rightNormalizer b.val) Z parentWidth hZ
    (s.left_base b.val) (s.right_base b.val) ξ

/-- Every original allocation label is retained or proved identically
zero.  There is no choice of a finite subset depending on ξ. -/
theorem finite_pointwise (parentWidth : ℝ) (hZ : 0 < Z) (ξ : V) :
    (∑ b ∈ labels, s.sourcePair parentWidth b ξ) ≤
      ∑ b : s.active labels, s.weight labels parentWidth b * s.envelope labels b ξ * s.childPair labels b ξ := by
  calc
    _ = ∑ b ∈ s.active labels, s.sourcePair parentWidth b ξ := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ labels)
        (fun b hb hn => s.sourcePair_eq_zero_of_inactive labels parentWidth b hb hn ξ)
    _ = ∑ b : s.active labels, s.sourcePair parentWidth b.val ξ :=
      (Finset.sum_coe_sort _ _).symm
    _ ≤ _ := Finset.sum_le_sum fun b _ => s.pointwise labels parentWidth hZ b ξ

variable [MeasurableSpace V]

def kernel (μ : Λ → Measure V) (parentWidth : ℝ) (b : s.active labels) : Measure V :=
  normalizedCapacityPairKernel (μ b.val) (s.leftChild labels b) (s.rightChild labels b)
    (s.leftNormalizer b.val) (s.rightNormalizer b.val) Z parentWidth

theorem kernel_finite (μ : Λ → Measure V)
    (parentWidth : ℝ) (b : s.active labels)
    (hprofile : Integrable (s.envelope labels b) (μ b.val)) :
    IsFiniteMeasure (s.kernel labels μ parentWidth b) :=
  normalizedCapacityPairKernel_finite _ _ _ _ _ _ _ hprofile

/-- The exact total mass on the original retained finite carrier.  Its
right-hand side is what the arithmetic divisor/allocation mass estimate
must bound, with the two normalization factors and removals each once. -/
theorem total_mass (μ : Λ → Measure V) (parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : ∀ b : s.active labels, AEStronglyMeasurable (s.envelope labels b) (μ b.val)) :
    (∑ b : s.active labels, (s.kernel labels μ parentWidth b).real Set.univ) =
      ∑ b : s.active labels, s.weight labels parentWidth b * ∫ ξ, s.envelope labels b ξ ∂μ b.val := by
  apply Finset.sum_congr rfl
  intro b _
  exact normalizedCapacityPairKernel_mass _ _ _ _ _ _ _ hZ (hprofile b)

/-- The whole finite source family reaches the same actual child
kernel family.  Analytic integrability facts can be discharged by the
raw finite atom controls before using this composition theorem. -/
theorem finite_integral (μ : Λ → Measure V) (parentWidth : ℝ) (hZ : 0 < Z)
    (hprofile : ∀ b : s.active labels, Measurable (s.envelope labels b))
    (hsource : ∀ b ∈ labels, Integrable (s.sourcePair parentWidth b) (μ b))
    (hchild : ∀ b : s.active labels, Integrable
      (fun ξ => s.envelope labels b ξ * s.childPair labels b ξ) (μ b.val)) :
    (∑ b ∈ labels, ∫ ξ, s.sourcePair parentWidth b ξ ∂μ b) ≤
      ∑ b : s.active labels,
        ∫ ξ, s.childPair labels b ξ ∂s.kernel labels μ parentWidth b := by
  calc
    _ = ∑ b ∈ s.active labels, ∫ ξ, s.sourcePair parentWidth b ξ ∂μ b := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ labels)
      intro b hb hn
      simp_rw [s.sourcePair_eq_zero_of_inactive labels parentWidth b hb hn]
      exact integral_zero _ _
    _ = ∑ b : s.active labels, ∫ ξ, s.sourcePair parentWidth b.val ξ ∂μ b.val :=
      (Finset.sum_coe_sort _ _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b _
      exact normalized_capacity_pair_integral (μ b.val) (s.leftChild labels b)
        (s.rightChild labels b) (s.leftNormalizer b.val) (s.rightNormalizer b.val)
        Z parentWidth hZ (s.left_base b.val) (s.right_base b.val) (hprofile b)
        (hsource b.val (Finset.mem_filter.mp b.property).1) (hchild b)

end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.finite_pointwise
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.total_mass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.finite_integral
