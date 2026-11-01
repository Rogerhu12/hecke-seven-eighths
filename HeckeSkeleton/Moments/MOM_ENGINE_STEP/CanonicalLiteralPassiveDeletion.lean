import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel
import HeckePort.CenteredMoment.Mask

/-!
# Finite deletion after the two actual Gauss transforms

A coprimality mask is expanded on the complete finite paired polynomial,
before any norm is taken. Every divisor is allocated to all original
occurrences: the two plain ideals and all prime slots. In particular,
the two rectangles of a centered coefficient are never separated here.

The resulting nonempty branches are actual `ActualColumnAllocation`s.
They retain the original coefficient, frequency and Fourier variable;
their quotient supports and frozen factors are computed by the existing
allocation API. No support-norm or source-energy estimate is an input.

The finite carriers in this file may be the full smooth-profile carriers.
Applying the identity only to a carrier already filtered by the same
mask is valid but does not enlarge that carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalOriginalPhaseCalibration WholeAllocation

namespace CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K]
variable {X Y P : Type*} {k : ℕ}

/-- The finite mask identity holds for the complete complex summand. -/
theorem finite_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (columns : Finset X) (I : X → Ideal (𝓞 K)) (C : X → ℂ) :
    (∑ x ∈ columns, (if IsCoprime (I x) M then (1 : ℂ) else 0) * C x) =
      ∑ D ∈ idealDivisors M, (moebius D : ℂ) *
        ∑ x ∈ columns with D ∣ I x, C x := by
  have hterm (x : X) :
      (if IsCoprime (I x) M then (1 : ℂ) else 0) * C x =
        ∑ D ∈ idealDivisors M,
          (moebius D : ℂ) * (if D ∣ I x then C x else 0) := by
    rw [HeckePort.CenteredMomentMask.ideal_coprime_mobius (I x) M hM,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    by_cases hD : D ∣ I x <;>
      simp only [hD, if_true, if_false, zero_mul, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  simp only [Finset.sum_filter, Finset.mul_sum]

/-- All divisor allocations act on the same whole coefficient. A
nonsquarefree divisor disappears by its actual Möbius coefficient. -/
theorem paired_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S,
      (if IsCoprime (I x.1.1 * J x.1.2 * ∏ i, A (x.2 i)) M then (1 : ℂ) else 0) *
        C x) =
      ∑ D ∈ idealDivisors M, (moebius D : ℂ) *
        ∑ v ∈ AllocationMass.idealAllocations D (k + 2),
          AllocationMass.sign (primeSupport D) v *
            ∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S I J A, C x := by
  rw [finite_mask M hM]
  apply Finset.sum_congr rfl
  intro D _
  exact moebius_paired_divisor_allocation D S₁ S₂ S I J A C

/-- The label stores the actual divisor and its occurrence allocation. -/
abbrev Label (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  Σ D : Ideal (𝓞 K), primeSupport D → Finset (Fin (k + 2))

def labels (M : Ideal (𝓞 K)) (k : ℕ) : Finset (Label K k) :=
  (idealDivisors M).sigma (fun D => AllocationMass.idealAllocations D (k + 2))

def sign (a : Label K k) : ℂ :=
  (moebius a.1 : ℂ) * AllocationMass.sign (primeSupport a.1) a.2

def columns (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (a : Label K k) : Finset ((X × Y) × (Fin k → P)) :=
  pairedAllocatedColumns a.1 a.2 S₁ S₂ S I J A

/-- Empty allocated carriers are removed by their exact zero sum. -/
def liveLabels (M : Ideal (𝓞 K))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    Finset (Label K k) :=
  (labels M k).filter (fun a => (columns S₁ S₂ S I J A a).Nonempty)

theorem liveLabels_subset (M : Ideal (𝓞 K))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    liveLabels M S₁ S₂ S I J A ⊆ labels M k := Finset.filter_subset _ _

/-- The divisor is an actual divisor of the original finite mask. -/
theorem divisor_dvd_of_mem_liveLabels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (a : Label K k) (ha : a ∈ liveLabels M S₁ S₂ S I J A) : a.1 ∣ M := by
  have hl := liveLabels_subset M S₁ S₂ S I J A ha
  exact (mem_idealDivisors hM).mp (Finset.mem_sigma.mp hl).1

/-- The witness is chosen from the computed allocated finite carrier;
no nonempty-source hypothesis is added to the original polynomial. -/
def allocation (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal}) :
    ActualColumnAllocation K k where
  divisor := a.val.1
  selection := a.val.2
  plain₁ := S₁
  plain₂ := S₂
  slots := S
  plain₁_nonzero := hS₁
  plain₂_nonzero := hS₂
  witness := (Finset.mem_filter.mp a.property).2.choose
  witness_mem := (Finset.mem_filter.mp a.property).2.choose_spec

@[simp] theorem allocation_columns (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal}) :
    (allocation M S₁ S₂ S hS₁ hS₂ a).columns =
      columns S₁ S₂ S id id HeightOneSpectrum.asIdeal a.val := rfl

@[simp] theorem norm_sign_le_one (a : Label K k) : ‖sign a‖ ≤ 1 := by
  rw [sign, norm_mul, AllocationMass.norm_sign, mul_one]
  exact norm_ideal_moebius_le_one a.1

theorem paired_mask_labels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S,
      (if IsCoprime (I x.1.1 * J x.1.2 * ∏ i, A (x.2 i)) M then (1 : ℂ) else 0) *
        C x) =
      ∑ a ∈ labels M k, sign a * ∑ x ∈ columns S₁ S₂ S I J A a, C x := by
  simpa only [labels, Finset.sum_sigma, sign, columns, Finset.mul_sum, mul_assoc] using
    paired_mask M hM S₁ S₂ S I J A C

section Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Fourier parameter and every original location remain unchanged
throughout the finite mask expansion. -/
theorem joint_mask_labels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ)
    (x : (X × Y) × (Fin k → P) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C v) x ξ =
      ∑ a ∈ labels M k, sign a *
        jointFourierColumn (columns S₁ S₂ S I J A a) C x ξ := by
  simpa only [jointFourierColumn, mul_assoc] using
    paired_mask_labels M hM S₁ S₂ S I J A (fun v => C v * jointPhase ξ (x v))

theorem joint_mask_liveLabels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ)
    (x : (X × Y) × (Fin k → P) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C v) x ξ =
      ∑ a ∈ liveLabels M S₁ S₂ S I J A, sign a *
        jointFourierColumn (columns S₁ S₂ S I J A a) C x ξ := by
  rw [joint_mask_labels M hM]
  symm
  apply Finset.sum_subset (liveLabels_subset M S₁ S₂ S I J A)
  intro a ha hn
  have hempty : columns S₁ S₂ S I J A a = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro he
    exact hn (Finset.mem_filter.mpr ⟨ha, he⟩)
  simp only [hempty, jointFourierColumn, Finset.sum_empty, mul_zero]

/-- Every surviving summand has the genuine quotient and frozen-slot
data required by `ActualColumnAllocation.centered_joint_polynomial`. -/
theorem joint_mask_allocations (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (C : AllocationColumn K k → ℂ) (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (allocationColumnIdeal v) M then (1 : ℂ) else 0) * C v)
      x ξ =
      ∑ a ∈ (liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val *
          jointFourierColumn (allocation M S₁ S₂ S hS₁ hS₂ a).columns C x ξ := by
  simpa only [allocation_columns, Finset.sum_attach] using
    joint_mask_liveLabels M hM S₁ S₂ S id id HeightOneSpectrum.asIdeal C x ξ

/-- Literal deletion of a whole two-rectangle table is the preceding
finite expansion, with the original normalizer and subtraction. -/
theorem atoms_deleteMask_joint
    (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns d.plain₁ d.plain₂ d.slots)
      (d.deleteMask M).whole x ξ =
      ∑ a ∈ labels M.val k, sign a *
        jointFourierColumn
          (columns d.plain₁ d.plain₂ d.slots id id HeightOneSpectrum.asIdeal a)
          d.whole x ξ := by
  calc
    _ = jointFourierColumn (childCartesianColumns d.plain₁ d.plain₂ d.slots)
        (fun i => (if IsCoprime (allocationColumnIdeal i) M.val then (1 : ℂ) else 0) *
          d.whole i) x ξ := by
      unfold jointFourierColumn
      apply Finset.sum_congr rfl
      intro i hi
      rw [d.deleteMask_whole M i hi]
      change (d.whole i * (if IsCoprime (allocationColumnIdeal i) M.val then 1 else 0)) *
        jointPhase ξ (x i) = _
      ring
    _ = _ := joint_mask_labels M.val (nonZeroDivisors.coe_ne_zero M)
      d.plain₁ d.plain₂ d.slots id id HeightOneSpectrum.asIdeal d.whole x ξ

theorem atoms_deleteMask_allocations
    (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns d.plain₁ d.plain₂ d.slots)
      (d.deleteMask M).whole x ξ =
      ∑ a ∈ (liveLabels M.val d.plain₁ d.plain₂ d.slots
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val d.plain₁ d.plain₂ d.slots
            d.plain₁_nonzero d.plain₂_nonzero a).columns d.whole x ξ := by
  rw [atoms_deleteMask_joint]
  simp only [allocation_columns, Finset.sum_attach]
  symm
  apply Finset.sum_subset
    (liveLabels_subset M.val d.plain₁ d.plain₂ d.slots id id HeightOneSpectrum.asIdeal)
  intro a ha hn
  have hempty : columns d.plain₁ d.plain₂ d.slots id id HeightOneSpectrum.asIdeal a = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro he
    exact hn (Finset.mem_filter.mpr ⟨ha, he⟩)
  simp only [hempty, jointFourierColumn, Finset.sum_empty, mul_zero]

/-- Weighted finite Minkowski separates the computed labels without
introducing a cardinality factor or changing the original row weight. -/
theorem sqrt_joint_energy_mask_le {H : Type*}
    (M : Ideal (𝓞 K)) (hM : M ≠ 0) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (q : H → ℂ) (C : H → (X × Y) × (Fin k → P) → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
      (fun h v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C h v) x ξ) ≤
      ∑ a ∈ labels M k,
        Real.sqrt (jointColumnEnergy rows (columns S₁ S₂ S I J A a) q C x ξ) := by
  unfold jointColumnEnergy
  simp_rw [joint_mask_labels M hM]
  refine (sqrt_row_energy_sum rows (labels M k) q
    (fun a h => sign a * jointFourierColumn (columns S₁ S₂ S I J A a)
      (C h) (x h) ξ)).trans ?_
  apply Finset.sum_le_sum
  intro a _
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro h _
  have hn : ‖sign a * jointFourierColumn (columns S₁ S₂ S I J A a) (C h) (x h) ξ‖ ≤
      ‖jointFourierColumn (columns S₁ S₂ S I J A a) (C h) (x h) ξ‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_sign_le_one a) (norm_nonneg _)).trans_eq
      (one_mul _)
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn) (norm_nonneg _)

/-- Both independent deletion families stay under the same kernel.
This pointwise form applies directly to the original product of the
two nonnegative Fourier kernels, without substituting a measure. -/
theorem joint_integrand_mask_le {H X' Y' P' : Type*} {l : ℕ}
    (M N : Ideal (𝓞 K)) (hM : M ≠ 0) (hN : N ≠ 0) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (T₁ : Finset X') (T₂ : Finset Y') (T : Fin l → Finset P')
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (I' : X' → Ideal (𝓞 K)) (J' : Y' → Ideal (𝓞 K)) (A' : P' → Ideal (𝓞 K))
    (q : H → ℂ) (C : H → (X × Y) × (Fin k → P) → ℂ)
    (E : H → (X' × Y') × (Fin l → P') → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V)
    (y : H → (X' × Y') × (Fin l → P') → V)
    (ξ : V) (kernel : ℝ) (hkernel : 0 ≤ kernel) :
    kernel *
      (Real.sqrt (jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
        (fun h v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
          then (1 : ℂ) else 0) * C h v) x ξ) *
       Real.sqrt (jointColumnEnergy rows (childCartesianColumns T₁ T₂ T) q
        (fun h v => (if IsCoprime (I' v.1.1 * J' v.1.2 * ∏ i, A' (v.2 i)) N
          then (1 : ℂ) else 0) * E h v) y ξ)) ≤
      ∑ a ∈ labels M k, ∑ b ∈ labels N l, kernel *
        (Real.sqrt (jointColumnEnergy rows (columns S₁ S₂ S I J A a) q C x ξ) *
         Real.sqrt (jointColumnEnergy rows (columns T₁ T₂ T I' J' A' b) q E y ξ)) := by
  have hleft := sqrt_joint_energy_mask_le M hM rows S₁ S₂ S I J A q C x ξ
  have hright := sqrt_joint_energy_mask_le N hN rows T₁ T₂ T I' J' A' q E y ξ
  calc
    _ ≤ kernel *
        ((∑ a ∈ labels M k,
          Real.sqrt (jointColumnEnergy rows (columns S₁ S₂ S I J A a) q C x ξ)) *
         (∑ b ∈ labels N l,
          Real.sqrt (jointColumnEnergy rows (columns T₁ T₂ T I' J' A' b) q E y ξ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hleft hright (Real.sqrt_nonneg _)
          (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)) hkernel
    _ = _ := by rw [Finset.sum_mul_sum]; simp only [Finset.mul_sum]

end Fourier
end CanonicalLiteralPassiveDeletion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.finite_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.paired_mask_labels
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.atoms_deleteMask_joint
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.joint_mask_allocations
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.atoms_deleteMask_allocations
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.sqrt_joint_energy_mask_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.joint_integrand_mask_le
