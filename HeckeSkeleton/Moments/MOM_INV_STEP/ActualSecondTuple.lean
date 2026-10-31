import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition
import HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers

/-!
# Arithmetic reconstruction from the original source indices

The original squarefree columns determine `A₁,A₂,C` and the second common
factor. The two divisor indices are subsets of their actual principal
Poisson masks. The cube factors are the proved factors of `b₁ b₂`.
Every field of the reconstruction relation is then proved from those data.

The two slot-choice families are restricted on the original extracted
ideals, before the new row or label is formed. The final source zeros are
retained and imply squarefreeness of the new label. This constructs the
arithmetic reconstruction; reindexing an entire signed source sum also
requires collecting its residual column variables and coefficients.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualSecondTuple

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open IdealMobiusMask FirstSourceDecomposition
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

@[ext] structure Source (Sector : Type*) where
  b₁ : (Ideal (𝓞 K))⁰
  b₂ : (Ideal (𝓞 K))⁰
  n₁ : (Ideal (𝓞 K))⁰
  n₂ : (Ideal (𝓞 K))⁰
  x₁ : (Ideal (𝓞 K))⁰
  x₂ : (Ideal (𝓞 K))⁰
  quotient : (Ideal (𝓞 K))⁰
  n₁_squarefree : Squarefree n₁.val
  n₂_squarefree : Squarefree n₂.val
  x₁_squarefree : Squarefree x₁.val
  x₂_squarefree : Squarefree x₂.val
  overlap : Finset (HeightOneSpectrum (𝓞 K))
  frequency : Ideal (𝓞 K) × Sector

variable {K} {Sector : Type*}

namespace Source

def epsilon (n : (Ideal (𝓞 K))⁰) (p : HeightOneSpectrum (𝓞 K)) : Bool :=
  decide (p.asIdeal ∣ n.val)

def cubeQ (B : Source K Sector) : Ideal (𝓞 K) :=
  CubeLabels.q0 B.b₁ B.b₂ (epsilon B.n₁) (epsilon B.n₂)
def cubeJ (B : Source K Sector) : Ideal (𝓞 K) :=
  CubeLabels.J B.b₁ B.b₂ (epsilon B.n₁) (epsilon B.n₂)
def cubeJ2 (B : Source K Sector) : Ideal (𝓞 K) :=
  CubeLabels.J2 B.b₁ B.b₂ (epsilon B.n₁) (epsilon B.n₂)
def cubeS (B : Source K Sector) : Ideal (𝓞 K) := CubeLabels.s B.b₁ B.b₂
def firstCommon (B : Source K Sector) : Ideal (𝓞 K) :=
  C B.n₁ B.n₂ B.b₁ B.b₂
def secondCommonSupport (B : Source K Sector) : Finset (HeightOneSpectrum (𝓞 K)) :=
  primeSupport B.x₁ ∩ primeSupport B.x₂
def secondCommon (B : Source K Sector) : Ideal (𝓞 K) :=
  primeProduct B.secondCommonSupport
def overlapIdeal (B : Source K Sector) : Ideal (𝓞 K) := primeProduct B.overlap

def cubePrincipalSupport (B : Source K Sector) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (primeSupport (B.b₁ * B.b₂)).filter fun p =>
    CubeAlgebra.conductorExponent (CubeAlgebra.parity (primeExponents (B.b₁ * B.b₂) p))
      (epsilon B.n₁ p) (epsilon B.n₂ p) = 0

def firstMaskSupport (B : Source K Sector) : Finset (HeightOneSpectrum (𝓞 K)) :=
  commonSupport B.n₁ B.n₂ B.b₁ B.b₂ ∪ B.cubePrincipalSupport

def oldExtracted (B : Source K Sector) : Ideal (𝓞 K) :=
  B.firstCommon * (B.b₁.val * B.b₂.val).radical * B.quotient.val
def newExtracted (B : Source K Sector) : Ideal (𝓞 K) :=
  B.secondCommon * B.overlapIdeal

theorem secondCommon_eq_gcd (B : Source K Sector) :
    B.secondCommon = gcd B.x₁.val B.x₂.val :=
  pairCommon_eq_gcd B.x₁ B.x₂ B.x₁_squarefree B.x₂_squarefree

theorem cubeQ_ne_zero (B : Source K Sector) : B.cubeQ ≠ 0 := by
  unfold cubeQ CubeLabels.q0 CubeAlgebra.b0Label CubeAlgebra.primeProduct
  exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.ne_bot

theorem cubeJ_ne_zero (B : Source K Sector) : B.cubeJ ≠ 0 := by
  unfold cubeJ CubeLabels.J CubeAlgebra.jLabel CubeAlgebra.primeProduct
  exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.ne_bot

theorem cube_radical_dvd (B : Source K Sector) :
    (B.b₁.val * B.b₂.val).radical ∣ B.cubeQ * B.cubeJ := by
  have hd : B.b₁.val * B.b₂.val ∣ (B.cubeQ * B.cubeJ) ^ 2 := by
    refine ⟨B.cubeS, ?_⟩
    change (CubeLabels.q0 B.b₁ B.b₂ (epsilon B.n₁) (epsilon B.n₂) *
      CubeLabels.J B.b₁ B.b₂ (epsilon B.n₁) (epsilon B.n₂)) ^ 2 =
        B.b₁.val * B.b₂.val * CubeLabels.s B.b₁ B.b₂
    rw [CubeLabels.J_eq_s_mul_J2, CubeLabels.actual_cube_decomposition]
    ring
  apply Ideal.dvd_iff_le.mpr
  have hh := Ideal.radical_mono (Ideal.dvd_iff_le.mp hd)
  rw [Ideal.radical_pow _ (by decide : (2 : ℕ) ≠ 0)] at hh
  exact Ideal.le_radical.trans hh

theorem A_dvd_cube_radical (B : Source K Sector) (n : (Ideal (𝓞 K))⁰) :
    A n B.b₁ B.b₂ ∣ (B.b₁.val * B.b₂.val).radical := by
  rw [show (B.b₁.val * B.b₂.val).radical = primeProduct (primeSupport (B.b₁ * B.b₂)) from
    radical_eq_primeProduct (B.b₁ * B.b₂)]
  exact Finset.prod_dvd_prod_of_subset Finset.inter_subset_right

end Source

/-- Prime choices are restricted at their original extracted factors.
The new child divisibility conditions are not part of this source data. -/
@[ext] structure Choices {Jo Jn : ℕ} (B : Source K Sector)
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))) where
  firstDivisor : {T : Finset (HeightOneSpectrum (𝓞 K)) // T ⊆ B.firstMaskSupport}
  secondDivisor : {T : Finset (HeightOneSpectrum (𝓞 K)) // T ⊆ B.secondCommonSupport}
  oldAssigned : (i : Fin Jo) →
    {p : HeightOneSpectrum (𝓞 K) // p ∈ oldLists i ∧ p.asIdeal ∣ B.oldExtracted}
  newAssigned : (i : Fin Jn) →
    {p : HeightOneSpectrum (𝓞 K) // p ∈ newLists i ∧ p.asIdeal ∣ B.newExtracted}

namespace Choices

variable {Jo Jn : ℕ} {B : Source K Sector}
variable {oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K))}
variable {newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))}

def dk (a : Choices B oldLists newLists) : Ideal (𝓞 K) := primeProduct a.firstDivisor.val
def d2 (a : Choices B oldLists newLists) : Ideal (𝓞 K) := primeProduct a.secondDivisor.val
def residual (a : Choices B oldLists newLists) : Ideal (𝓞 K) :=
  primeProduct (B.secondCommonSupport \ a.secondDivisor.val)

theorem d2_mul_residual (a : Choices B oldLists newLists) :
    a.d2 * a.residual = B.secondCommon := by
  have hh := primeProduct_split B.secondCommonSupport a.secondDivisor.val
  rw [Finset.inter_eq_right.mpr a.secondDivisor.property] at hh
  exact hh.symm

theorem dk_dvd_original_mask (a : Choices B oldLists newLists) :
    a.dk ∣ B.firstCommon * (B.b₁.val * B.b₂.val).radical := by
  have hsub : a.firstDivisor.val ⊆
      commonSupport B.n₁ B.n₂ B.b₁ B.b₂ ∪ primeSupport (B.b₁ * B.b₂) := by
    intro p hp
    rcases Finset.mem_union.mp (a.firstDivisor.property hp) with hc | hb
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (Finset.mem_filter.mp hb).1
  have hdis : Disjoint (commonSupport B.n₁ B.n₂ B.b₁ B.b₂)
      (primeSupport (B.b₁ * B.b₂)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 hq
  have hh : a.dk ∣ primeProduct
      (commonSupport B.n₁ B.n₂ B.b₁ B.b₂ ∪ primeSupport (B.b₁ * B.b₂)) :=
    Finset.prod_dvd_prod_of_subset hsub
  have he : primeProduct
      (commonSupport B.n₁ B.n₂ B.b₁ B.b₂ ∪ primeSupport (B.b₁ * B.b₂)) =
      B.firstCommon * (B.b₁.val * B.b₂.val).radical := by
    rw [show (B.b₁.val * B.b₂.val).radical = primeProduct (primeSupport (B.b₁ * B.b₂)) from
      radical_eq_primeProduct (B.b₁ * B.b₂)]
    exact Finset.prod_union hdis
  rw [he] at hh
  exact hh

def outer (a : Choices B oldLists newLists) : OuterTriple K :=
  ⟨B.cubeQ, B.quotient.val, a.residual⟩

def newLabel (a : Choices B oldLists newLists) : Ideal (𝓞 K) :=
  B.cubeJ * B.firstCommon * a.d2 * B.overlapIdeal

def newRow (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (a : Choices B oldLists newLists) : Ideal (𝓞 K) × Sector :=
  (a.dk * a.d2 * B.frequency.1, sectorTransport a.dk a.d2 B.frequency.2)

def tuple (a : Choices B oldLists newLists) : SecondTuple K Sector Jo Jn where
  outer := a.outer
  core := ![B.cubeJ, B.firstCommon, a.d2, B.cubeS, B.b₁.val,
    A B.n₁ B.b₁ B.b₂, A B.n₂ B.b₁ B.b₂, a.dk]
  commonResidual := B.overlapIdeal
  cubeResidual := B.cubeJ2
  secondCube := B.b₂.val
  extractedCommon := B.secondCommon
  frequency := B.frequency
  oldAssigned := fun i => (a.oldAssigned i).val
  newAssigned := fun i => (a.newAssigned i).val

theorem oldExtracted_dvd (a : Choices B oldLists newLists) :
    B.oldExtracted ∣ a.outer.q0 * a.newLabel * a.outer.quotient := by
  calc
    _ ∣ (B.firstCommon * (B.cubeQ * B.cubeJ)) * B.quotient.val :=
      mul_dvd_mul_right _ (mul_dvd_mul_left _ B.cube_radical_dvd)
    _ ∣ _ := by
      refine ⟨a.d2 * B.overlapIdeal, ?_⟩
      change B.cubeQ * (B.cubeJ * B.firstCommon * a.d2 * B.overlapIdeal) * B.quotient.val = _
      ring

theorem newExtracted_dvd (a : Choices B oldLists newLists) :
    B.newExtracted ∣ a.newLabel * a.outer.residual := by
  refine ⟨B.cubeJ * B.firstCommon, ?_⟩
  change (B.cubeJ * B.firstCommon * a.d2 * B.overlapIdeal) * a.residual =
    (B.secondCommon * B.overlapIdeal) * (B.cubeJ * B.firstCommon)
  rw [← a.d2_mul_residual]
  ring

/-- Every reconstruction field follows from actual source arithmetic,
including both families of assigned original prime choices. -/
theorem valid (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (a : Choices B oldLists newLists) :
    Valid sectorTransport a.tuple a.outer a.newLabel (a.newRow sectorTransport) := by
  refine {
    outer_eq := rfl
    label := rfl
    j_split := ?_
    b_split := ?_
    a1 := ?_
    a2 := ?_
    d := ?_
    extracted_eq := a.d2_mul_residual
    row_eq := rfl
    sector_eq := rfl
    old_dvd := ?_
    new_dvd := ?_ }
  · exact (CubeLabels.J_eq_s_mul_J2 B.b₁ B.b₂ (Source.epsilon B.n₁) (Source.epsilon B.n₂)).symm
  · exact CubeLabels.actual_cube_decomposition B.b₁ B.b₂ (Source.epsilon B.n₁) (Source.epsilon B.n₂)
  · exact B.A_dvd_cube_radical B.n₁
  · exact B.A_dvd_cube_radical B.n₂
  · exact a.dk_dvd_original_mask
  · intro i
    exact (a.oldAssigned i).property.2.trans a.oldExtracted_dvd
  · intro i
    exact (a.newAssigned i).property.2.trans a.newExtracted_dvd

theorem original_slot_lists (a : Choices B oldLists newLists) :
    (∀ i, a.tuple.oldAssigned i ∈ oldLists i) ∧
      (∀ i, a.tuple.newAssigned i ∈ newLists i) :=
  ⟨fun i => (a.oldAssigned i).property.1, fun i => (a.newAssigned i).property.1⟩

theorem outer_nonzero (a : Choices B oldLists newLists) :
    a.outer.q0 ≠ 0 ∧ a.outer.quotient ≠ 0 ∧ a.outer.residual ≠ 0 :=
  ⟨B.cubeQ_ne_zero, nonZeroDivisors.coe_ne_zero B.quotient, primeProduct_ne_bot _⟩

theorem newLabel_ne_zero (a : Choices B oldLists newLists) : a.newLabel ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero B.cubeJ_ne_zero (primeProduct_ne_bot _))
    (primeProduct_ne_bot _)) (primeProduct_ne_bot _)

theorem newRow_ne_zero
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (a : Choices B oldLists newLists) (hk : B.frequency.1 ≠ 0) :
    (a.newRow sectorTransport).1 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (primeProduct_ne_bot _) (primeProduct_ne_bot _)) hk

/-- The retained signed zeros force the actual constructed child label
to be squarefree; no squarefreeness of that label is assumed. -/
theorem newLabel_squarefree_of_live
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (a : Choices B oldLists newLists) (scalar : ℂ)
    (hlive : scalar * labelZero a.tuple ≠ 0) : Squarefree a.newLabel := by
  apply valid_label_squarefree_of_scalar_ne_zero (a.valid sectorTransport)
    (CubeLabels.J_squarefree B.b₁ B.b₂ (Source.epsilon B.n₁) (Source.epsilon B.n₂))
    (squarefree_primeProduct _) (squarefree_primeProduct _) (squarefree_primeProduct _)
    scalar hlive

end Choices

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualSecondTuple

end
