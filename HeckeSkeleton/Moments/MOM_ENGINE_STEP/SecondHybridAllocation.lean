import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondResidualSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocationKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernelExceptionalSplit

/-!
# Actual second allocations before exceptional-row Cauchy

The complete complex correlation form is first expanded into its
genuine Möbius and finite-character blocks.  Each divisor filter is then
allocated on all factor occurrences while the original coupled kernel
is still present.  Only after these finite identities is the actual row
predicate applied: exceptional rows retain the product of their two
whole centered polynomials, and Cauchy is used on complementary rows.

The predicate may depend on the divisor, finite character, and both
allocations.  Thus no mixed exceptional/nonexceptional energy terms are
created, and no rowwise bound is used to bound a larger Cauchy product.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.IdealMobiusDivisorSum
open WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} {k l : ℕ}

def jointHybridKernelCost {α β : Type*}
    (F : 𝓢(V, ℂ)) (rows : Finset H) (left : Finset α) (right : Finset β)
    (q : H → ℂ) (c : H → α → ℂ) (d : H → β → ℂ)
    (x : H → α → V) (y : H → β → V) (exceptional : H → Prop) : ℝ :=
  ∫ ξ : V, ‖(𝓕 F) ξ‖ *
    (jointColumnPairMagnitude (rows.filter exceptional) left right q c
      (fun h j => star (d h j)) x y ξ +
      Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h) left q c x ξ) *
      Real.sqrt (jointColumnEnergy (rows.filter fun h => ¬exceptional h) right q
        (fun h j => star (d h j)) y ξ))

theorem joint_kernel_two_filters {α β : Type*}
    (F : 𝓢(V, ℂ)) (rows : Finset H) (left : Finset α) (right : Finset β)
    (q : H → ℂ) (c : H → α → ℂ) (d : H → β → ℂ)
    (x : H → α → V) (y : H → β → V)
    (P : α → Prop) (Q : β → Prop) :
    jointKernelPairing F rows left right q
      (fun h i => if P i then c h i else 0) (fun h j => if Q j then d h j else 0) x y =
      jointKernelPairing F rows (left.filter P) (right.filter Q) q c d x y := by
  unfold jointKernelPairing
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P i
  · simp only [if_pos hi]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : Q j <;>
      simp only [hj, if_true, if_false, star_zero, mul_zero, zero_mul]
  · simp only [if_neg hi, zero_mul, Finset.sum_const_zero]

/-- Exact allocation of both complete complex columns, with the
coupled Schwartz kernel retained throughout. -/
theorem joint_kernel_whole_allocation
    (F : 𝓢(V, ℂ)) (D : Ideal (𝓞 K)) (hD : Squarefree D) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (q : H → ℂ) (c : H → AllocationColumn K k → ℂ)
    (d : H → AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V) :
    jointKernelPairing F rows (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T) q
      (fun h i => if D ∣ allocationColumnIdeal i then c h i else 0)
      (fun h j => if D ∣ allocationColumnIdeal j then d h j else 0) x y =
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2), AllocationMass.sign (primeSupport D) a *
        ∑ b ∈ AllocationMass.idealAllocations D (l + 2), AllocationMass.sign (primeSupport D) b *
          jointKernelPairing F rows
            (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
            (pairedAllocatedColumns D b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
            q c d x y := by
  have halloc {m : ℕ}
      (U₁ U₂ : Finset (Ideal (𝓞 K)))
      (U : Fin m → Finset (HeightOneSpectrum (𝓞 K)))
      (C : AllocationColumn K m → ℂ) :
      (∑ i ∈ (childCartesianColumns U₁ U₂ U).filter
          (fun i => D ∣ allocationColumnIdeal i), C i) =
        ∑ a ∈ AllocationMass.idealAllocations D (m + 2),
          AllocationMass.sign (primeSupport D) a *
            ∑ i ∈ pairedAllocatedColumns D a U₁ U₂ U id id HeightOneSpectrum.asIdeal,
              C i := by
    calc
      _ = ∑ i ∈ (childCartesianColumns U₁ U₂ U).filter
          (fun i => D ∣ i.1.1 * i.1.2 * ∏ j, (i.2 j).asIdeal), C i := rfl
      _ = _ := whole_paired_divisor_allocation D hD U₁ U₂ U
        id id HeightOneSpectrum.asIdeal C
  rw [joint_kernel_two_filters]
  unfold jointKernelPairing
  simp_rw [halloc S₁ S₂ S, halloc T₁ T₂ T]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows) (t := AllocationMass.idealAllocations D (k + 2))]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Finset.sum_comm
    (s := pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
    (t := AllocationMass.idealAllocations D (l + 2))]
  rw [Finset.sum_comm (s := rows) (t := AllocationMass.idealAllocations D (l + 2))]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite allocation chooses its row predicate before its
Cauchy estimate.  Both original centered columns remain complete. -/
theorem joint_kernel_allocated_hybrid_bound
    (F : 𝓢(V, ℂ)) (D : Ideal (𝓞 K)) (hD : Squarefree D) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (q : H → ℂ) (c : H → AllocationColumn K k → ℂ)
    (d : H → AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (exceptional : (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) :
    ‖jointKernelPairing F rows (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T) q
      (fun h i => if D ∣ allocationColumnIdeal i then c h i else 0)
      (fun h j => if D ∣ allocationColumnIdeal j then d h j else 0) x y‖ ≤
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2),
        ∑ b ∈ AllocationMass.idealAllocations D (l + 2),
          jointHybridKernelCost F rows
            (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
            (pairedAllocatedColumns D b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
            q c d x y (exceptional a b) := by
  rw [joint_kernel_whole_allocation F D hD rows S₁ S₂ S T₁ T₂ T q c d x y]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul, AllocationMass.norm_sign, one_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_mul, AllocationMass.norm_sign, one_mul]
  exact joint_kernel_exceptional_split F rows _ _ q c d x y (exceptional a b)

section FullCorrelation

variable {γ : Type*} [Fintype γ]

/-- The literal positive hybrid cost of all actual divisor, phase and
allocation branches. -/
def fullCorrelationHybridCost
    (F : 𝓢(V, ℂ)) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (rightIdeals : AllocationColumn K l → Ideal (𝓞 K))
    (q : H → ℂ) (phaseCoefficient : γ → ℂ)
    (c : γ → H → AllocationColumn K k → ℂ)
    (d : γ → H → AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), γ →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) : ℝ :=
  ∑ D ∈ divisorPool (childCartesianColumns T₁ T₂ T) rightIdeals, ‖(moebius D : ℂ)‖ *
    ∑ χ : γ, ‖phaseCoefficient χ‖ *
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2),
        ∑ b ∈ AllocationMass.idealAllocations D (l + 2),
          jointHybridKernelCost F rows
            (pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
            (pairedAllocatedColumns D b T₁ T₂ T id id HeightOneSpectrum.asIdeal)
            q (c χ) (d χ) x y (exceptional D χ a b)

theorem full_correlation_cartesian_hybrid_bound
    (F : 𝓢(V, ℂ)) (rows : Finset H)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (leftIdeals : AllocationColumn K k → Ideal (𝓞 K))
    (rightIdeals : AllocationColumn K l → Ideal (𝓞 K))
    (hRight : ∀ j ∈ childCartesianColumns T₁ T₂ T, rightIdeals j ≠ 0)
    (hLeftProduct : ∀ i ∈ childCartesianColumns S₁ S₂ S, leftIdeals i = allocationColumnIdeal i)
    (hRightProduct : ∀ j ∈ childCartesianColumns T₁ T₂ T, rightIdeals j = allocationColumnIdeal j)
    (Corr : AllocationColumn K k → AllocationColumn K l → H → ℂ) (common q : H → ℂ)
    (phaseCoefficient : γ → ℂ)
    (leftPhase : γ → AllocationColumn K k → ℂ) (rightPhase : γ → AllocationColumn K l → ℂ)
    (leftColumn : AllocationColumn K k → H → ℂ) (rightColumn : AllocationColumn K l → H → ℂ)
    (hcommon : ∀ i j h, IsCoprime (leftIdeals i) (rightIdeals j) →
      Corr i j h = common h *
        (∑ χ : γ, phaseCoefficient χ * leftPhase χ i * star (rightPhase χ j)) *
          (leftColumn i h * star (rightColumn j h)))
    (c : AllocationColumn K k → ℂ) (d : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), γ →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) :
    ‖∑ h ∈ rows, q h * ∑ i ∈ childCartesianColumns S₁ S₂ S,
      ∑ j ∈ childCartesianColumns T₁ T₂ T,
        (if IsCoprime (leftIdeals i) (rightIdeals j) then Corr i j h else 0) *
          (c i * star (d j)) * F (x h i + y h j)‖ ≤
      fullCorrelationHybridCost F rows S₁ S₂ S T₁ T₂ T rightIdeals
        (fun h => q h * common h) phaseCoefficient
        (fun χ h i => c i * leftPhase χ i * leftColumn i h)
        (fun χ h j => d j * rightPhase χ j * rightColumn j h) x y exceptional := by
  rw [full_correlation_kernel_children F rows
    (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
    leftIdeals rightIdeals hRight Corr common q phaseCoefficient leftPhase rightPhase
    leftColumn rightColumn hcommon c d x y]
  unfold fullCorrelationHybridCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D _
  by_cases hD : Squarefree D
  · rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro χ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have he :
        jointKernelPairing F rows (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
          (fun h => q h * common h)
          (kernelDivisorCoefficient leftIdeals D c (leftPhase χ) leftColumn)
          (kernelDivisorCoefficient rightIdeals D d (rightPhase χ) rightColumn) x y =
        jointKernelPairing F rows (childCartesianColumns S₁ S₂ S) (childCartesianColumns T₁ T₂ T)
          (fun h => q h * common h)
          (fun h i => if D ∣ allocationColumnIdeal i then c i * leftPhase χ i * leftColumn i h else 0)
          (fun h j => if D ∣ allocationColumnIdeal j then d j * rightPhase χ j * rightColumn j h else 0)
          x y := by
      unfold jointKernelPairing
      apply Finset.sum_congr rfl
      intro h _
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [kernelDivisorCoefficient, hLeftProduct i hi, hRightProduct j hj]
    rw [he]
    exact joint_kernel_allocated_hybrid_bound F D hD rows S₁ S₂ S T₁ T₂ T
      (fun h => q h * common h)
      (fun h i => c i * leftPhase χ i * leftColumn i h)
      (fun h j => d j * rightPhase χ j * rightColumn j h) x y (exceptional D χ)
  · simp only [moebius_of_not_squarefree hD, Int.cast_zero, zero_mul, norm_zero, le_refl]

end FullCorrelation

section ActualCorrelation

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]
local instance secondHybridAllocationCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

def secondResidualHybridCost
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (ID IE : A.Exterior) (IA : AllocationColumn K k → A.Exterior)
    (IB : AllocationColumn K l → A.Exterior)
    (d e : A.R) (hd : A.Generates ID d) (he : A.Generates IE e)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle) (q : H → ℂ)
    (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), ((Ray × Ray) →* Circle) →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) : ℝ :=
  fullCorrelationHybridCost F rows S₁ S₂ S T₁ T₂ T (fun j => (IB j).val)
    (fun h => q h * generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h))
    (fixedPhaseCoefficient Ray phaseTable)
    (fun χ h i => c i * (fixedLeftPhase Ray χ (rayLeft i) : ℂ) *
      σ (A.sexticResidue (IA i) (frequency h)))
    (fun χ h j => f j * (fixedRightPhase Ray χ (rayRight j) : ℂ) *
      σ (A.sexticResidue (IB j) (-frequency h))) x y exceptional

/-- The actual complete nonprimitive correlation supplies its own
common-support factorization.  Only the primitive fixed-ray phase
dictionary remains as an arithmetic input. -/
theorem actual_second_residual_hybrid_allocated_bound
    (F : 𝓢(V, ℂ)) (rows : Finset H) (frequency : H → A.R)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (T₁ T₂ : Finset (Ideal (𝓞 K))) (T : Fin l → Finset (HeightOneSpectrum (𝓞 K)))
    (ID IE : A.Exterior) (IA : AllocationColumn K k → A.Exterior)
    (IB : AllocationColumn K l → A.Exterior)
    (hIA : ∀ i ∈ childCartesianColumns S₁ S₂ S, (IA i).val = allocationColumnIdeal i)
    (hIB : ∀ j ∈ childCartesianColumns T₁ T₂ T, (IB j).val = allocationColumnIdeal j)
    (IDA : AllocationColumn K k → A.Exterior) (IEB : AllocationColumn K l → A.Exterior)
    (hIDA : ∀ i, (IDA i).val = ID.val * (IA i).val)
    (hIEB : ∀ j, (IEB j).val = IE.val * (IB j).val)
    (d e : A.R) (a : AllocationColumn K k → A.R) (b : AllocationColumn K l → A.R)
    (hd : A.Generates ID d) (he : A.Generates IE e)
    (ha : ∀ i, A.Generates (IA i) (a i)) (hb : ∀ j, A.Generates (IB j) (b j))
    (hda : ∀ i, A.Generates (IDA i) (d * a i))
    (heb : ∀ j, A.Generates (IEB j) (e * b j))
    (hDa : ∀ i, IsCoprime ID.val (IA i).val) (hEa : ∀ i, IsCoprime IE.val (IA i).val)
    (hDb : ∀ j, IsCoprime ID.val (IB j).val) (hEb : ∀ j, IsCoprime IE.val (IB j).val)
    (rayLeft : AllocationColumn K k → Ray) (rayRight : AllocationColumn K l → Ray)
    (phaseTable : Ray × Ray → Circle)
    (hphase : ∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        (phaseTable (rayLeft i, rayRight j) : ℂ))
    (q : H → ℂ) (c : AllocationColumn K k → ℂ) (f : AllocationColumn K l → ℂ)
    (x : H → AllocationColumn K k → V) (y : H → AllocationColumn K l → V)
    (exceptional : ∀ D : Ideal (𝓞 K), ((Ray × Ray) →* Circle) →
      (primeSupport D → Finset (Fin (k + 2))) →
      (primeSupport D → Finset (Fin (l + 2))) → H → Prop) :
    ‖∑ h ∈ rows, q h * ∑ i ∈ childCartesianColumns S₁ S₂ S,
      ∑ j ∈ childCartesianColumns T₁ T₂ T,
        (if IsCoprime (IA i).val (IB j).val then
          generatedIdealCorrelation (σ := σ) (IDA i) (IEB j) (d * a i) (e * b j)
            (hda i) (heb j) (frequency h) else 0) *
          (c i * star (f j)) * F (x h i + y h j)‖ ≤
      secondResidualHybridCost (σ := σ) Ray F rows frequency S₁ S₂ S T₁ T₂ T
        ID IE IA IB d e hd he rayLeft rayRight phaseTable q c f x y exceptional := by
  apply full_correlation_cartesian_hybrid_bound F rows S₁ S₂ S T₁ T₂ T
    (fun i => (IA i).val) (fun j => (IB j).val) (fun j _ => (IB j).property.1) hIA hIB
    (fun i j h => generatedIdealCorrelation (σ := σ) (IDA i) (IEB j)
      (d * a i) (e * b j) (hda i) (heb j) (frequency h))
    (fun h => generatedIdealCorrelation (σ := σ) ID IE d e hd he (frequency h)) q
    (fixedPhaseCoefficient Ray phaseTable)
    (fun χ i => (fixedLeftPhase Ray χ (rayLeft i) : ℂ))
    (fun χ j => (fixedRightPhase Ray χ (rayRight j) : ℂ))
    (fun i h => σ (A.sexticResidue (IA i) (frequency h)))
    (fun j h => σ (A.sexticResidue (IB j) (-frequency h)))
  intro i j h hij
  rw [generated_correlation_common_support ID IE (IA i) (IB j) (IDA i) (IEB j)
    (hIDA i) (hIEB j) d e (a i) (b j) hd he (ha i) (hb j) (hda i) (heb j)
    (hDa i) (hEa i) (hDb j) (hEb j) hij (frequency h), hphase i j hij,
    fixed_phase_expansion Ray phaseTable]

end ActualCorrelation

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_whole_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_allocated_hybrid_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_residual_hybrid_allocated_bound

