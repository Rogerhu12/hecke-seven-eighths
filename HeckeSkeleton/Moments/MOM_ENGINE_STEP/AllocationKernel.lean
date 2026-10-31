import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeAllocation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondResidualSource

/-!
# Actual divisor allocations under the common Fourier measure

The literal squarefree divisor filter is expanded on all factor
occurrences before a norm is taken.  Finite weighted Minkowski then
separates its actual allocations inside each Cauchy half.  Both halves
retain the original complete coefficient and the same Fourier measure.
All finite exchanges are justified by the genuine Schwartz integrability
of the original column polynomials.
-/

noncomputable section
open scoped Classical BigOperators NumberField FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open WholeAllocation

section Minkowski

variable {H β : Type*}

private theorem allocation_energy_nonneg (rows : Finset H) (q f : H → ℂ) :
    0 ≤ ∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2 :=
  Finset.sum_nonneg fun h _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- Weighted finite L2 Minkowski, with the actual common row measure. -/
theorem sqrt_row_energy_add (rows : Finset H) (q f g : H → ℂ) :
    Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖f h + g h‖ ^ 2) ≤
      Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2) +
        Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2) := by
  have hf : (∑ h ∈ rows, (Real.sqrt ‖q h‖ * ‖f h‖) ^ 2) =
      ∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hg : (∑ h ∈ rows, (Real.sqrt ‖q h‖ * ‖g h‖) ^ 2) =
      ∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro h _
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hcross := Real.sum_mul_le_sqrt_mul_sqrt rows
    (fun h => Real.sqrt ‖q h‖ * ‖f h‖)
    (fun h => Real.sqrt ‖q h‖ * ‖g h‖)
  rw [hf, hg] at hcross
  have hsum : (∑ h ∈ rows, ‖q h‖ * ‖f h + g h‖ ^ 2) ≤
      (∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2) +
        (∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2) +
          2 * ∑ h ∈ rows,
            (Real.sqrt ‖q h‖ * ‖f h‖) * (Real.sqrt ‖q h‖ * ‖g h‖) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    have hn := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (norm_add_le (f h) (g h))) (norm_nonneg (q h))
    have hterm : (Real.sqrt ‖q h‖ * ‖f h‖) * (Real.sqrt ‖q h‖ * ‖g h‖) =
        ‖q h‖ * ‖f h‖ * ‖g h‖ := by
      calc
        _ = (Real.sqrt ‖q h‖ * Real.sqrt ‖q h‖) * ‖f h‖ * ‖g h‖ := by ring
        _ = _ := by rw [Real.mul_self_sqrt (norm_nonneg _)]
    calc
      _ ≤ ‖q h‖ * (‖f h‖ + ‖g h‖) ^ 2 := hn
      _ = _ := by rw [hterm]; ring
  have h0 := Real.sqrt_nonneg (∑ h ∈ rows, ‖q h‖ * ‖f h + g h‖ ^ 2)
  have h1 := Real.sqrt_nonneg (∑ h ∈ rows, ‖q h‖ * ‖f h‖ ^ 2)
  have h2 := Real.sqrt_nonneg (∑ h ∈ rows, ‖q h‖ * ‖g h‖ ^ 2)
  have hs0 := Real.sq_sqrt (allocation_energy_nonneg rows q (fun h => f h + g h))
  have hs1 := Real.sq_sqrt (allocation_energy_nonneg rows q f)
  have hs2 := Real.sq_sqrt (allocation_energy_nonneg rows q g)
  nlinarith

/-- No allocation-cardinality factor is introduced at this stage. -/
theorem sqrt_row_energy_sum (rows : Finset H) (labels : Finset β)
    (q : H → ℂ) (f : β → H → ℂ) :
    Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖∑ b ∈ labels, f b h‖ ^ 2) ≤
      ∑ b ∈ labels, Real.sqrt (∑ h ∈ rows, ‖q h‖ * ‖f b h‖ ^ 2) := by
  induction labels using Finset.induction_on with
  | empty => simp
  | @insert b labels hb ih =>
    simp only [Finset.sum_insert hb]
    exact (sqrt_row_energy_add rows q (f b) (fun h => ∑ a ∈ labels, f a h)).trans
      (add_le_add le_rfl ih)

end Minkowski

section Allocation

variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {X Y P H : Type*} {k : ℕ}

/-- Fourier insertion does not change the exact whole-coefficient
divisor allocation. -/
theorem joint_divisor_allocation (D : Ideal (𝓞 K)) (hD : Squarefree D)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (c : (X × Y) × (Fin k → P) → ℂ)
    (x : (X × Y) × (Fin k → P) → V) (ξ : V) :
    jointFourierColumn ((childCartesianColumns S₁ S₂ S).filter
      (fun v => D ∣ I v.1.1 * J v.1.2 * ∏ i, A (v.2 i))) c x ξ =
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2),
        AllocationMass.sign (primeSupport D) a *
          jointFourierColumn (pairedAllocatedColumns D a S₁ S₂ S I J A) c x ξ :=
  whole_paired_divisor_allocation D hD S₁ S₂ S I J A
    (fun v => c v * jointPhase ξ (x v))

/-- All actual signs have norm one, and the complete centered
coefficient is still unchanged in every allocation. -/
theorem sqrt_joint_energy_divisor_allocation
    (D : Ideal (𝓞 K)) (hD : Squarefree D) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (q : H → ℂ) (c : H → (X × Y) × (Fin k → P) → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows
      ((childCartesianColumns S₁ S₂ S).filter
        (fun v => D ∣ I v.1.1 * J v.1.2 * ∏ i, A (v.2 i))) q c x ξ) ≤
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2),
        Real.sqrt (jointColumnEnergy rows
          (pairedAllocatedColumns D a S₁ S₂ S I J A) q c x ξ) := by
  unfold jointColumnEnergy
  simp_rw [joint_divisor_allocation D hD]
  simpa only [norm_mul, AllocationMass.norm_sign, one_mul] using
    sqrt_row_energy_sum rows (AllocationMass.idealAllocations D (k + 2)) q
      (fun a h => AllocationMass.sign (primeSupport D) a *
        jointFourierColumn (pairedAllocatedColumns D a S₁ S₂ S I J A) (c h) (x h) ξ)

/-- The if-valued source coefficient equals its literal support filter. -/
theorem joint_energy_divisor_filter {ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (D : Ideal (𝓞 K)) (I : ι → Ideal (𝓞 K))
    (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    jointColumnEnergy rows columns q
      (fun h i => if D ∣ I i then c h i else 0) x ξ =
      jointColumnEnergy rows (columns.filter (fun i => D ∣ I i)) q c x ξ := by
  simp only [jointColumnEnergy, jointFourierColumn, Finset.sum_filter,
    ite_mul, zero_mul]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {X' Y' P' : Type*} {l : ℕ}

/-- The two actual allocation families remain under one common Fourier
measure, with every square root taken before the finite allocation sum. -/
theorem allocated_joint_kernel_bound (F : 𝓢(V, ℂ))
    (D : Ideal (𝓞 K)) (hD : Squarefree D) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (T₁ : Finset X') (T₂ : Finset Y') (T : Fin l → Finset P')
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (I' : X' → Ideal (𝓞 K)) (J' : Y' → Ideal (𝓞 K)) (A' : P' → Ideal (𝓞 K))
    (q : H → ℂ)
    (c : H → (X × Y) × (Fin k → P) → ℂ)
    (f : H → (X' × Y') × (Fin l → P') → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V)
    (y : H → (X' × Y') × (Fin l → P') → V) :
    (∫ ξ : V, ‖(𝓕 F) ξ‖ *
      (Real.sqrt (jointColumnEnergy rows
        ((childCartesianColumns S₁ S₂ S).filter
          (fun v => D ∣ I v.1.1 * J v.1.2 * ∏ i, A (v.2 i))) q c x ξ) *
       Real.sqrt (jointColumnEnergy rows
        ((childCartesianColumns T₁ T₂ T).filter
          (fun v => D ∣ I' v.1.1 * J' v.1.2 * ∏ i, A' (v.2 i))) q f y ξ))) ≤
      ∑ a ∈ AllocationMass.idealAllocations D (k + 2),
        ∑ b ∈ AllocationMass.idealAllocations D (l + 2),
          ∫ ξ : V, ‖(𝓕 F) ξ‖ *
            (Real.sqrt (jointColumnEnergy rows
              (pairedAllocatedColumns D a S₁ S₂ S I J A) q c x ξ) *
             Real.sqrt (jointColumnEnergy rows
              (pairedAllocatedColumns D b T₁ T₂ T I' J' A') q f y ξ)) := by
  let L := AllocationMass.idealAllocations D (k + 2)
  let R := AllocationMass.idealAllocations D (l + 2)
  let integrand := fun a b ξ => ‖(𝓕 F) ξ‖ *
    (Real.sqrt (jointColumnEnergy rows (pairedAllocatedColumns D a S₁ S₂ S I J A) q c x ξ) *
      Real.sqrt (jointColumnEnergy rows (pairedAllocatedColumns D b T₁ T₂ T I' J' A') q f y ξ))
  have hint (a) (b) : Integrable (integrand a b) :=
    joint_kernel_energy_integrable F rows _ _ q c f x y
  calc
    _ ≤ ∫ ξ : V, ∑ a ∈ L, ∑ b ∈ R, integrand a b ξ := by
      apply integral_mono (joint_kernel_energy_integrable F rows _ _ q c f x y)
        (integrable_finsetSum L (fun a _ => integrable_finsetSum R (fun b _ => hint a b)))
      intro ξ
      have hL := sqrt_joint_energy_divisor_allocation D hD rows S₁ S₂ S I J A q c x ξ
      have hR := sqrt_joint_energy_divisor_allocation D hD rows T₁ T₂ T I' J' A' q f y ξ
      calc
        _ ≤ ‖(𝓕 F) ξ‖ *
            ((∑ a ∈ L, Real.sqrt (jointColumnEnergy rows
                (pairedAllocatedColumns D a S₁ S₂ S I J A) q c x ξ)) *
             (∑ b ∈ R, Real.sqrt (jointColumnEnergy rows
                (pairedAllocatedColumns D b T₁ T₂ T I' J' A') q f y ξ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hL hR (Real.sqrt_nonneg _)
              (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)) (norm_nonneg _)
        _ = _ := by
          simp only [Finset.sum_mul_sum, Finset.mul_sum, integrand, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum L
        (fun a _ => integrable_finsetSum R (fun b _ => hint a b))]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum R (fun b _ => hint a b)

end Allocation

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sqrt_joint_energy_divisor_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.allocated_joint_kernel_bound
