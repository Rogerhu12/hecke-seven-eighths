module

public import HeckeSkeleton.Moments.MOM_INV_STEP.CubeAlgebra

/-!
# The first conductor is the two residual supports times the cube part

This is a finite support calculation for the actual digit. A positive
source-support condition excludes unused primes from the complementary
mask. Applied to actual ideal multiplicities it yields the manuscript's
`u₁ u₂ R₁` and `C · rad(b₁ b₂)/R₁` prime products.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SupportPartition

open CubeAlgebra
open scoped BigOperators Classical

variable {ι : Type*}

def leftResidual (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  Q.filter (fun p => v p = 0 ∧ ε₁ p = true ∧ ε₂ p = false)

def rightResidual (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  Q.filter (fun p => v p = 0 ∧ ε₁ p = false ∧ ε₂ p = true)

def commonResidual (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  Q.filter (fun p => v p = 0 ∧ ε₁ p = true ∧ ε₂ p = true)

def cubeActive (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  Q.filter (fun p => 0 < v p ∧ conductorExponent (parity (v p)) (ε₁ p) (ε₂ p) ≠ 0)

def cubePrincipal (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  Q.filter (fun p => 0 < v p ∧ conductorExponent (parity (v p)) (ε₁ p) (ε₂ p) = 0)

theorem active_partition (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Q.filter (fun p => conductorExponent (parity (v p)) (ε₁ p) (ε₂ p) ≠ 0) =
      (leftResidual Q v ε₁ ε₂ ∪ rightResidual Q v ε₁ ε₂) ∪ cubeActive Q v ε₁ ε₂ := by
  have hone : (1 : ZMod 6) ≠ 0 := by decide
  ext p
  by_cases hv : v p = 0
  · cases h₁ : ε₁ p <;> cases h₂ : ε₂ p <;>
      simp_all [leftResidual, rightResidual, cubeActive,
        conductorExponent, parity, bit]
  · have hp : 0 < v p := Nat.pos_of_ne_zero hv
    simp [leftResidual, rightResidual, cubeActive, hv, hp]

theorem principal_partition (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hsupport : ∀ p ∈ Q, 0 < bit (ε₁ p) + bit (ε₂ p) + v p) :
    Q.filter (fun p => conductorExponent (parity (v p)) (ε₁ p) (ε₂ p) = 0) =
      commonResidual Q v ε₁ ε₂ ∪ cubePrincipal Q v ε₁ ε₂ := by
  have hone : (1 : ZMod 6) ≠ 0 := by decide
  ext p
  by_cases hq : p ∈ Q
  · have hpositive := hsupport p hq
    by_cases hv : v p = 0
    · cases h₁ : ε₁ p <;> cases h₂ : ε₂ p <;>
        simp_all [commonResidual, cubePrincipal, conductorExponent, parity, bit]
    · have hp : 0 < v p := Nat.pos_of_ne_zero hv
      simp [commonResidual, cubePrincipal, hv, hp]
  · simp [commonResidual, cubePrincipal, hq]

theorem residuals_disjoint (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Disjoint (leftResidual Q v ε₁ ε₂) (rightResidual Q v ε₁ ε₂) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hl := (Finset.mem_filter.mp hp).2.2.1
  have hr := (Finset.mem_filter.mp hq).2.2.1
  simp_all

theorem residuals_disjoint_cubeActive
    (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Disjoint (leftResidual Q v ε₁ ε₂ ∪ rightResidual Q v ε₁ ε₂)
      (cubeActive Q v ε₁ ε₂) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpos := (Finset.mem_filter.mp hq).2.1
  rcases Finset.mem_union.mp hp with hp | hp
  · have hz := (Finset.mem_filter.mp hp).2.1
    omega
  · have hz := (Finset.mem_filter.mp hp).2.1
    omega

theorem common_disjoint_cubePrincipal
    (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Disjoint (commonResidual Q v ε₁ ε₂) (cubePrincipal Q v ε₁ ε₂) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hz := (Finset.mem_filter.mp hp).2.1
  have hpos := (Finset.mem_filter.mp hq).2.1
  omega

theorem primitive_product {M : Type*} [CommMonoid M] (p : ι → M)
    (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i ∈ Q.filter (fun i => conductorExponent (parity (v i)) (ε₁ i) (ε₂ i) ≠ 0), p i) =
      (∏ i ∈ leftResidual Q v ε₁ ε₂, p i) *
      (∏ i ∈ rightResidual Q v ε₁ ε₂, p i) *
      ∏ i ∈ cubeActive Q v ε₁ ε₂, p i := by
  rw [active_partition, Finset.prod_union (residuals_disjoint_cubeActive Q v ε₁ ε₂),
    Finset.prod_union (residuals_disjoint Q v ε₁ ε₂)]

theorem principal_product {M : Type*} [CommMonoid M] (p : ι → M)
    (Q : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hsupport : ∀ i ∈ Q, 0 < bit (ε₁ i) + bit (ε₂ i) + v i) :
    (∏ i ∈ Q.filter (fun i => conductorExponent (parity (v i)) (ε₁ i) (ε₂ i) = 0), p i) =
      (∏ i ∈ commonResidual Q v ε₁ ε₂, p i) *
        ∏ i ∈ cubePrincipal Q v ε₁ ε₂, p i := by
  rw [principal_partition Q v ε₁ ε₂ hsupport,
    Finset.prod_union (common_disjoint_cubePrincipal Q v ε₁ ε₂)]

end HeckeSkeleton.Moments.MOM_INV_STEP.SupportPartition

end
