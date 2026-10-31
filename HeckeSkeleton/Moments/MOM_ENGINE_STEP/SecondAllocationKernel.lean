import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel

/-!
# Literal second residual kernel with both actual allocation families

The only expansion dictionary here identifies each source ideal with the
product of its two plain occurrences and all its prime-slot occurrences.
The actual common correlation, divisor pool, finite phase coefficients,
complete centered coefficients, and Fourier measure are retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} {k l : ℕ}

abbrev AllocationColumn (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  (Ideal (𝓞 K) × Ideal (𝓞 K)) × (Fin k → HeightOneSpectrum (𝓞 K))

def allocationColumnIdeal (i : AllocationColumn K k) : Ideal (𝓞 K) :=
  i.1.1 * i.1.2 * ∏ j, (i.2 j).asIdeal

variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

def secondAllocatedLeftCoefficient
    (IA : AllocationColumn K k → A.Exterior) (frequency : H → A.R)
    (ray : AllocationColumn K k → Ray) (χ : (Ray × Ray) →* Circle)
    (c : AllocationColumn K k → ℂ) (h : H) (i : AllocationColumn K k) : ℂ :=
  c i * (fixedLeftPhase Ray χ (ray i) : ℂ) *
    σ (A.sexticResidue (IA i) (frequency h))

def secondAllocatedRightCoefficient
    (IB : AllocationColumn K l → A.Exterior) (frequency : H → A.R)
    (ray : AllocationColumn K l → Ray) (χ : (Ray × Ray) →* Circle)
    (c : AllocationColumn K l → ℂ) (h : H) (i : AllocationColumn K l) : ℂ :=
  star (c i * (fixedRightPhase Ray χ (ray i) : ℂ) *
    σ (A.sexticResidue (IB i) (-frequency h)))

/-- The two finite allocation labels are those of the same actual
squarefree divisor, and every summand uses the original Fourier measure. -/
def secondAllocatedKernelCost
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K)))
    (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (ID IE : A.Exterior) (IA : AllocationColumn K k → A.Exterior)
    (IB : AllocationColumn K l → A.Exterior)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle)
    (q : H → ℂ) (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V) : ℝ :=
  ∑ L ∈ divisorPool (childCartesianColumns T₁ T₂ T) (fun j => (IB j).val),
    ‖(moebius L : ℂ)‖ *
      ∑ χ : (Ray × Ray) →* Circle, ‖fixedPhaseCoefficient Ray phaseTable χ‖ *
        ∑ a ∈ AllocationMass.idealAllocations L (k + 2),
          ∑ b ∈ AllocationMass.idealAllocations L (l + 2),
            ∫ ξ : V, ‖(𝓕 F) ξ‖ *
              (Real.sqrt (jointColumnEnergy rows
                (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
                (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
                (secondAllocatedLeftCoefficient (σ := σ) Ray IA frequency rayLeft χ c) x ξ) *
               Real.sqrt (jointColumnEnergy rows
                (pairedAllocatedColumns L b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
                (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
                (secondAllocatedRightCoefficient (σ := σ) Ray IB frequency rayRight χ f) y ξ))

private theorem allocation_energy_filter_of_terms {ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ) (p : ι → Prop)
    (c f : H → ι → ℂ) (x : H → ι → V) (ξ : V)
    (hc : ∀ h ∈ rows, ∀ i ∈ columns, c h i = if p i then f h i else 0) :
    jointColumnEnergy rows columns q c x ξ =
      jointColumnEnergy rows (columns.filter p) q f x ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have he : jointFourierColumn columns (c h) (x h) ξ =
      jointFourierColumn (columns.filter p) (f h) (x h) ξ := by
    simp only [jointFourierColumn, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc h hh i hi]
    split_ifs <;> simp only [zero_mul]
  rw [he]

/-- This is the actual secondResidualKernelCost, rather than a generic
kernel identity supplied by the caller.  No polynomial equality or
energy estimate is assumed. -/
theorem actual_second_kernel_allocation_bound
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K)))
    (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (ID IE : A.Exterior) (IA : AllocationColumn K k → A.Exterior)
    (IB : AllocationColumn K l → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (hIB : ∀ j ∈ childCartesianColumns T₁ T₂ T, (IB j).val = allocationColumnIdeal j)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle)
    (q : H → ℂ) (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V) :
    secondResidualKernelCost (σ := σ) Ray F rows frequency
      (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
      ID IE IA IB d e hd he rayLeft rayRight phaseTable q c f x y ≤
        secondAllocatedKernelCost (σ := σ) Ray F rows frequency S₁ S₂ S T₁ T₂ T
          ID IE IA IB d e hd he rayLeft rayRight phaseTable q c f x y := by
  unfold secondResidualKernelCost secondAllocatedKernelCost
  apply Finset.sum_le_sum
  intro L hL
  by_cases hsq : Squarefree L
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro χ _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    let weight := fun h => q h *
      generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h)
    have hleft (ξ : V) :
        jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) weight
          (kernelDivisorCoefficient (fun i => (IA i).val) L c
            (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
            (fun i h => σ (A.sexticResidue (IA i) (frequency h)))) x ξ =
        jointColumnEnergy rows ((childCartesianColumns S₁ S₂ S).filter
          (fun i => L ∣ allocationColumnIdeal i)) weight
          (secondAllocatedLeftCoefficient (σ := σ) Ray IA frequency rayLeft χ c) x ξ := by
      apply allocation_energy_filter_of_terms
      intro h _ i hi
      unfold kernelDivisorCoefficient
      rw [hIA i hi]
      rfl
    have hright (ξ : V) :
        jointColumnEnergy rows (childCartesianColumns T₁ T₂ T) weight
          (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
            (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
            (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j)) y ξ =
        jointColumnEnergy rows ((childCartesianColumns T₁ T₂ T).filter
          (fun j => L ∣ allocationColumnIdeal j)) weight
          (secondAllocatedRightCoefficient (σ := σ) Ray IB frequency rayRight χ f) y ξ := by
      apply allocation_energy_filter_of_terms
      intro h _ j hj
      unfold kernelDivisorCoefficient
      rw [hIB j hj]
      by_cases hdiv : L ∣ allocationColumnIdeal j <;>
        simp only [hdiv, ite_true, ite_false, star_zero, secondAllocatedRightCoefficient]
    change (∫ ξ : V, ‖(𝓕 F) ξ‖ *
      (Real.sqrt (jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) weight
        (kernelDivisorCoefficient (fun i => (IA i).val) L c
          (fun i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
          (fun i h => σ (A.sexticResidue (IA i) (frequency h)))) x ξ) *
       Real.sqrt (jointColumnEnergy rows (childCartesianColumns T₁ T₂ T) weight
        (fun h j => star (kernelDivisorCoefficient (fun j => (IB j).val) L f
          (fun j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
          (fun j h => σ (A.sexticResidue (IB j) (-frequency h))) h j)) y ξ))) ≤ _
    simp_rw [hleft, hright]
    exact allocated_joint_kernel_bound F L hsq rows S₁ S₂ S T₁ T₂ T
      id id HeightOneSpectrum.asIdeal id id HeightOneSpectrum.asIdeal weight
      (secondAllocatedLeftCoefficient (σ := σ) Ray IA frequency rayLeft χ c)
      (secondAllocatedRightCoefficient (σ := σ) Ray IB frequency rayRight χ f) x y
  · simp only [moebius_of_not_squarefree hsq, Int.cast_zero, norm_zero, zero_mul, le_refl]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_kernel_allocation_bound
