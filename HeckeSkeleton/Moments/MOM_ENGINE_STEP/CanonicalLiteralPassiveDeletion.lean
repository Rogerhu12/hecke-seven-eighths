import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel
import HeckePort.CenteredMoment.Mask

set_option linter.unusedSectionVars false

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
open DedekindZetaZeroFree.LargeSieve

namespace CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K]
variable {X Y P : Type*} {k : ℕ}

/-- The finite mask identity holds for the complete complex summand. -/
theorem finite_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (columns : Finset X) (I : X → Ideal (𝓞 K)) (C : X → ℂ) :
    (∑ x ∈ columns, (if IsCoprime (I x) M then (1 : ℂ) else 0) * C x) =
      ∑ D ∈ idealDivisors M, (moebius D : ℂ) *
        ∑ x ∈ columns with D ∣ I x, C x := by
  sorry

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
  sorry

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
    liveLabels M S₁ S₂ S I J A ⊆ labels M k := by
  sorry

/-- The divisor is an actual divisor of the original finite mask. -/
theorem divisor_dvd_of_mem_liveLabels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (a : Label K k) (ha : a ∈ liveLabels M S₁ S₂ S I J A) : a.1 ∣ M := by
  sorry

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
  sorry

theorem paired_mask_labels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S,
      (if IsCoprime (I x.1.1 * J x.1.2 * ∏ i, A (x.2 i)) M then (1 : ℂ) else 0) *
        C x) =
      ∑ a ∈ labels M k, sign a * ∑ x ∈ columns S₁ S₂ S I J A a, C x := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
