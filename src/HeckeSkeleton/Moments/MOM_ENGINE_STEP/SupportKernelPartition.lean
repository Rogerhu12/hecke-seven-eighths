import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportCartesianReindex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedSecondClassProduction

/-!
# Actual column partitions inside the second common kernel

The finite labels are images of the retained original columns.  Their
polynomials sum exactly to the original polynomial, so weighted L2
Minkowski produces the actual pair of branch kernels under the same
two-frequency measure.  Each right branch uses its own genuine divisor
pool: terms outside that pool vanish because every original divisor
coefficient on the right is zero.

The common-support occurrence labels below are computed from the
original Cartesian dictionary.  Thus a branch's residual Cartesian
dictionary from SupportCartesianReindex can be used after this estimate,
without assuming that an unsplit common-support carrier is rectangular.
-/

noncomputable section
open scoped Classical BigOperators NumberField
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.Moments HeckePort.Moments.Support
open HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum

section ColumnPartition

variable {H α β Λ Ω : Type*}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem joint_fourier_column_partition
    (columns : Finset α) (label : α → Λ) (c : α → ℂ) (x : α → E) (ξ : E) :
    jointFourierColumn columns c x ξ =
      ∑ a ∈ columns.image label,
        jointFourierColumn (columns.filter (fun i => label i = a)) c x ξ :=
  (Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem label hi)
    (fun i => c i * jointPhase ξ (x i))).symm

theorem sqrt_joint_energy_column_partition
    (rows : Finset H) (columns : Finset α) (label : α → Λ)
    (q : H → ℂ) (c : H → α → ℂ) (x : H → α → E) (ξ : E) :
    Real.sqrt (jointColumnEnergy rows columns q c x ξ) ≤
      ∑ a ∈ columns.image label,
        Real.sqrt (jointColumnEnergy rows (columns.filter (fun i => label i = a))
          q c x ξ) := by
  unfold jointColumnEnergy
  simp_rw [joint_fourier_column_partition columns label]
  exact sqrt_row_energy_sum rows (columns.image label) q
    (fun a h => jointFourierColumn (columns.filter (fun i => label i = a)) (c h) (x h) ξ)

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

local notation "W" => WithLp 2 (U × V)

theorem measured_column_partition_bound
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (rows : Finset H) (left : Finset α) (right : Finset β)
    (labelLeft : α → Λ) (labelRight : β → Ω)
    (q : H → ℂ) (c : H → α → ℂ) (f : H → β → ℂ)
    (x : H → α → W) (y : H → β → W) :
    (∫ z, Real.sqrt (jointColumnEnergy rows left q c x (WithLp.toLp 2 z)) *
      Real.sqrt (jointColumnEnergy rows right q f y (WithLp.toLp 2 z)) ∂μ) ≤
      ∑ ab ∈ (left.image labelLeft).product (right.image labelRight),
        ∫ z, Real.sqrt (jointColumnEnergy rows (left.filter (fun i => labelLeft i = ab.1))
          q c x (WithLp.toLp 2 z)) *
          Real.sqrt (jointColumnEnergy rows (right.filter (fun j => labelRight j = ab.2))
            q f y (WithLp.toLp 2 z)) ∂μ := by
  let labels := (left.image labelLeft).product (right.image labelRight)
  let F := fun (ab : Λ × Ω) (z : U × V) =>
    Real.sqrt (jointColumnEnergy rows (left.filter (fun i => labelLeft i = ab.1))
      q c x (WithLp.toLp 2 z)) *
    Real.sqrt (jointColumnEnergy rows (right.filter (fun j => labelRight j = ab.2))
      q f y (WithLp.toLp 2 z))
  have hi ab : Integrable (F ab) μ :=
    nested_joint_cauchy_integrable rows _ _ q c f x y μ
  calc
    _ ≤ ∫ z, ∑ ab ∈ labels, F ab z ∂μ := by
      apply integral_mono (nested_joint_cauchy_integrable rows left right q c f x y μ)
        (integrable_finsetSum labels (fun ab _ => hi ab))
      intro z
      have hl := sqrt_joint_energy_column_partition rows left labelLeft q c x (WithLp.toLp 2 z)
      have hr := sqrt_joint_energy_column_partition rows right labelRight q f y (WithLp.toLp 2 z)
      apply (mul_le_mul hl hr (Real.sqrt_nonneg _)
        (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)).trans_eq
      simp only [labels, F, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul_sum]
    _ = _ := integral_finsetSum labels (fun ab _ => hi ab)

end ColumnPartition

section KernelPartition

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H α β Λ Ω ι : Type*} [Fintype ι] [DecidableEq ι]
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

local notation "W" => WithLp 2 (U × V)

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance supportKernelPartitionCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _
variable (R : ActualSecondCorrelationRows A σ H ι)

/-- One literal second-divisor/finite-character term of the original kernel. -/
def measuredDivisorKernelTerm
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W)
    (L : Ideal (𝓞 K)) (χ : (Ray × Ray) →* Circle) : ℝ :=
  ∫ z, Real.sqrt (jointColumnEnergy R.rows left
      (fun h => R.weight h * R.correlation h)
      (kernelDivisorCoefficient (fun i => (IA i).val) L c
        (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
        (fun i h => σ (A.sexticResidue (IA i) (R.frequency h)))) x (WithLp.toLp 2 z)) *
    Real.sqrt (jointColumnEnergy R.rows right
      (fun h => R.weight h * R.correlation h)
      (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
        (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
        (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j))
      y (WithLp.toLp 2 z)) ∂μ

theorem measuredDivisorKernelTerm_zero
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W)
    (L : Ideal (𝓞 K)) (χ : (Ray × Ray) →* Circle)
    (hL : L ∉ divisorPool right (fun j => (IB j).val)) :
    measuredDivisorKernelTerm Ray R μ left right IA IB rayLeft rayRight c f x y L χ = 0 := by
  have hnd (j : β) (hj : j ∈ right) : ¬ L ∣ (IB j).val := by
    intro hd
    apply hL
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, (mem_idealDivisors (IB j).property.1).mpr hd⟩
  have he (ξ : W) :
      jointColumnEnergy R.rows right (fun h => R.weight h * R.correlation h)
        (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
          (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
          (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) y ξ = 0 := by
    unfold jointColumnEnergy
    apply Finset.sum_eq_zero
    intro h hh
    have hc : jointFourierColumn right
        (fun j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
          (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
          (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) (y h) ξ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [kernelDivisorCoefficient, if_neg (hnd j hj), star_zero, zero_mul]
    rw [hc]
    simp
  simp only [measuredDivisorKernelTerm, he, Real.sqrt_zero, mul_zero, integral_zero]

/-- Enlarging the right divisor pool only adds actual zero terms. -/
theorem actual_measured_kernel_extend_pool
    (μ : Measure (U × V)) (left : Finset α) (right : Finset β)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W)
    (pool : Finset (Ideal (𝓞 K)))
    (hpool : divisorPool right (fun j => (IB j).val) ⊆ pool) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB
      rayLeft rayRight phaseTable c f x y =
      ∑ L ∈ pool, ‖(moebius L : ℂ)‖ *
        ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
          measuredDivisorKernelTerm Ray R μ left right IA IB rayLeft rayRight c f x y L χ := by
  change (∑ L ∈ divisorPool right (fun j => (IB j).val), ‖(moebius L : ℂ)‖ *
    ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
      measuredDivisorKernelTerm Ray R μ left right IA IB rayLeft rayRight c f x y L χ) = _
  apply Finset.sum_subset hpool
  intro L hL hn
  have hz (χ : (Ray × Ray) →* Circle) :=
    measuredDivisorKernelTerm_zero Ray R μ left right IA IB rayLeft rayRight c f x y L χ hn
  simp only [hz, mul_zero, Finset.sum_const_zero]

private theorem sum_two_weights_swap {I J B : Type*}
    (s : Finset I) (t : Finset J) (u : Finset B)
    (a : I → ℝ) (b : J → ℝ) (f : I → J → B → ℝ) :
    (∑ i ∈ s, a i * ∑ j ∈ t, b j * ∑ z ∈ u, f i j z) =
      ∑ z ∈ u, ∑ i ∈ s, a i * ∑ j ∈ t, b j * f i j z := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := s) (t := t)]
  simp_rw [Finset.sum_comm (s := s) (t := u)]
  rw [Finset.sum_comm (s := t) (t := u)]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_comm

/-- The complete original kernel produces the actual finite branch
kernels, with their own right divisor pools and the same whole coefficients. -/
theorem actual_measured_kernel_column_partition
    (μ : Measure (U × V)) [IsFiniteMeasure μ]
    (left : Finset α) (right : Finset β) (labelLeft : α → Λ) (labelRight : β → Ω)
    (IA : α → A.Exterior) (IB : β → A.Exterior)
    (rayLeft : α → Ray) (rayRight : β → Ray) (phaseTable : Ray × Ray → Circle)
    (c : α → ℂ) (f : β → ℂ) (x : H → α → W) (y : H → β → W) :
    actualMeasuredSecondKernelCost Ray R μ left right IA IB
      rayLeft rayRight phaseTable c f x y ≤
      ∑ ab ∈ (left.image labelLeft).product (right.image labelRight),
        actualMeasuredSecondKernelCost Ray R μ
          (left.filter (fun i => labelLeft i = ab.1))
          (right.filter (fun j => labelRight j = ab.2))
          IA IB rayLeft rayRight phaseTable c f x y := by
  let pool := divisorPool right (fun j => (IB j).val)
  let labels := (left.image labelLeft).product (right.image labelRight)
  let F := fun L χ (ab : Λ × Ω) =>
    measuredDivisorKernelTerm Ray R μ
      (left.filter (fun i => labelLeft i = ab.1))
      (right.filter (fun j => labelRight j = ab.2))
      IA IB rayLeft rayRight c f x y L χ
  have hb L χ :
      measuredDivisorKernelTerm Ray R μ left right IA IB rayLeft rayRight c f x y L χ ≤
        ∑ ab ∈ labels, F L χ ab :=
    measured_column_partition_bound μ R.rows left right labelLeft labelRight
      (fun h => R.weight h * R.correlation h)
      (kernelDivisorCoefficient (fun i => (IA i).val) L c
        (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
        (fun i h => σ (A.sexticResidue (IA i) (R.frequency h))))
      (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
        (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
        (fun j h => σ (A.sexticResidue (IB j) (-R.frequency h))) h j)) x y
  calc
    _ ≤ ∑ L ∈ pool, ‖(moebius L : ℂ)‖ *
        ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
          ∑ ab ∈ labels, F L χ ab := by
      apply Finset.sum_le_sum
      intro L _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro χ _
      exact mul_le_mul_of_nonneg_left (hb L χ) (norm_nonneg _)
    _ = ∑ ab ∈ labels, ∑ L ∈ pool, ‖(moebius L : ℂ)‖ *
        ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
          F L χ ab :=
      sum_two_weights_swap pool Finset.univ labels
        (fun L => ‖(moebius L : ℂ)‖)
        (fun χ => ‖fixedPhaseCoefficient Ray phaseTable χ‖) F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ab _
      symm
      apply actual_measured_kernel_extend_pool
      intro L hL
      obtain ⟨j, hj, hd⟩ := Finset.mem_biUnion.mp hL
      exact Finset.mem_biUnion.mpr ⟨j, (Finset.mem_filter.mp hj).1, hd⟩

end KernelPartition

section ActualSupportLabels

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior} {k : ℕ}

namespace CartesianSourceReindex

variable (R : CartesianSourceReindex columns ideal k)

/-- The source label is computed from the unique original Cartesian
tuple on the retained support.  Its irrelevant outside value contains
no chosen prime. -/
def supportExtractionLabel (P : Finset (Ideal (𝓞 K))) (i : ι) :
    SupportCartesian.ExtractionKey K k :=
  if hi : i ∈ columns then
    SupportCartesian.extractionKey P (Classical.choose (R.surjective i hi))
  else ((1, 1), fun _ => 1)

theorem supportExtractionLabel_index
    (P : Finset (Ideal (𝓞 K))) (x : AllocationColumn K k) (hx : x ∈ R.cartesian) :
    R.supportExtractionLabel P (R.index x) = SupportCartesian.extractionKey P x := by
  have hi := R.maps x hx
  rw [supportExtractionLabel, dif_pos hi]
  have hc := Classical.choose_spec (R.surjective (R.index x) hi)
  exact congrArg (SupportCartesian.extractionKey P) (R.injective hc.1 hx hc.2)

theorem supportExtractionLabel_image (P : Finset (Ideal (𝓞 K))) :
    columns.image (R.supportExtractionLabel P) =
      R.cartesian.image (SupportCartesian.extractionKey P) := by
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨x, hx, rfl⟩ := R.surjective i hi
    exact Finset.mem_image.mpr
      ⟨x, hx, (R.supportExtractionLabel_index P x hx).symm⟩
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr
      ⟨R.index x, R.maps x hx, R.supportExtractionLabel_index P x hx⟩

/-- The kernel's literal source-label fibre is exactly the original
index image used by the proved residual Cartesian constructor. -/
theorem supportExtractionLabel_fibre
    (P : Finset (Ideal (𝓞 K)))
    (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P) :
    columns.filter (fun i => R.supportExtractionLabel P i = b.key) =
      b.originalColumns.image R.index := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx, hxi⟩ := R.surjective i (Finset.mem_filter.mp hi).1
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hxi⟩
    rw [b.originalColumns_eq_filter]
    apply Finset.mem_filter.mpr
    refine ⟨hx, ?_⟩
    rw [← R.supportExtractionLabel_index P x hx, hxi]
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨R.maps x (b.original_subset hx), ?_⟩
    rw [R.supportExtractionLabel_index P x (b.original_subset hx)]
    have hkey := hx
    rw [b.originalColumns_eq_filter] at hkey
    exact (Finset.mem_filter.mp hkey).2

/-- The dictionary consumed by the actual nested child producer now
has exactly the literal source-label fibre as its source support. -/
def supportResidualLabelBranch
    (P : Finset (Ideal (𝓞 K)))
    (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
    (J : ι → A.Exterior)
    (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P) :
    CartesianSourceReindex
      (columns.filter (fun i => R.supportExtractionLabel P i = b.key)) J b.keep.card := by
  rw [R.supportExtractionLabel_fibre P b]
  exact R.supportResidualBranchOf P b J hJ

end CartesianSourceReindex

end ActualSupportLabels

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sqrt_joint_energy_column_partition
#print axioms HeckeSkeleton.Moments.EngineStep.actual_measured_kernel_column_partition
#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.supportExtractionLabel_fibre

