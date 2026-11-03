import CubicSieve.AnalyticRowDecomposition
import CubicSieve.ExteriorSieve

/-!
Finite cubic extraction bounds for the actual ideal kernel. Completing the
injective (first,second,cube) parameterization to a product costs only the
number of cube parts and the smaller of the two squarefree row bounds.
The sieve operator on the right is the actual exterior operator, not a new
independent estimate. This is the finite extraction step in the analytic bootstrap.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.AnalyticExtraction

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticFactorization
open CubicSieve.AnalyticRowDecomposition
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def firstImage (R : Finset (ExteriorIdeal K S)) := R.image (exteriorFirst K S)
def secondImage (R : Finset (ExteriorIdeal K S)) := R.image (exteriorSecond K S)
def cubeImage (R : Finset (ExteriorIdeal K S)) := R.image (exteriorCube K S)

def tripleEnergy (A B C T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C,
    ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S a b c) j‖ ^ 2

theorem energy_le_product_completion (R T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    energy K S D 2 R T z ≤
      tripleEnergy K S D (firstImage K S R) (secondImage K S R) (cubeImage K S R) T z := by
  let pieces := fun I : ExteriorIdeal K S =>
    (exteriorFirst K S I, exteriorSecond K S I, exteriorCube K S I)
  let f := fun t : ExteriorIdeal K S × ExteriorIdeal K S × ExteriorIdeal K S =>
    ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S t.1 t.2.1 t.2.2) j‖ ^ 2
  have hsub : R.image pieces ⊆
      (firstImage K S R).product ((secondImage K S R).product (cubeImage K S R)) := by
    intro t ht
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨I, hI, rfl⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨I, hI, rfl⟩, Finset.mem_image.mpr ⟨I, hI, rfl⟩⟩⟩
  calc
    _ = ∑ t ∈ R.image pieces, f t := by
      rw [Finset.sum_image (fun I _ J _ h => exterior_extraction_injective K S h)]
      simp only [f, pieces, exterior_factorization, energy, rowSum]
    _ ≤ ∑ t ∈ (firstImage K S R).product
        ((secondImage K S R).product (cubeImage K S R)), f t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      unfold tripleEnergy
      apply (Finset.sum_product (firstImage K S R)
        ((secondImage K S R).product (cubeImage K S R)) f).trans
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_product (secondImage K S R) (cubeImage K S R)
        (fun bc => f (a, bc))

private theorem restricted_operator_bound (A T : Finset (ExteriorIdeal K S)) (X N : ℝ)
    (hA : ∀ a ∈ A, Squarefree a.val.val ∧ exteriorNorm K S a ≤ X)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N) :
    FiniteKernel.HasBound A T (positiveKernel K S D) (ExteriorSieve.B K S D X N) :=
  FiniteKernel.restrict_bound (ExteriorSieve.cutoff K S X) A (ExteriorSieve.cutoff K S N) T
    (fun a ha => (ExteriorSieve.mem_cutoff K S X a).mpr (hA a ha))
    (fun j hj => (ExteriorSieve.mem_cutoff K S N j).mpr (hT j hj))
    (positiveKernel K S D) (ExteriorSieve.B K S D X N) (ExteriorSieve.B_nonneg K S D X N)
    (ExteriorSieve.cutoff_bound K S D X N)

theorem first_block_bound (hD : AllowedGeneratorInput K S D)
    (A T : Finset (ExteriorIdeal K S)) (X N : ℝ)
    (hA : ∀ a ∈ A, Squarefree a.val.val ∧ exteriorNorm K S a ≤ X)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (b c : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ) :
    (∑ a ∈ A, ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S a b c) j‖ ^ 2) ≤
      ExteriorSieve.B K S D X N * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  have hb := restricted_operator_bound K S D A T X N hA hT
    (descendedCoefficient K S D b c z)
  have hb' : (∑ a ∈ A, ‖∑ j ∈ T, descendedCoefficient K S D b c z j *
      positiveKernel K S D a j‖ ^ 2) ≤
      ExteriorSieve.B K S D X N * ∑ j ∈ T, ‖descendedCoefficient K S D b c z j‖ ^ 2 := by
    simpa only [FiniteKernel.form, FiniteKernel.energy, mul_comm] using hb
  simp_rw [extracted_row_sum K S D hD]
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (descendedCoefficient_energy_le K S D b c T z) (ExteriorSieve.B_nonneg K S D X N))

theorem second_block_bound (hD : AllowedGeneratorInput K S D)
    (B T : Finset (ExteriorIdeal K S)) (Y N : ℝ)
    (hB : ∀ b ∈ B, Squarefree b.val.val ∧ exteriorNorm K S b ≤ Y)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (a c : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ) :
    (∑ b ∈ B, ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S a b c) j‖ ^ 2) ≤
      ExteriorSieve.B K S D Y N * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  have hb := restricted_operator_bound K S D B T Y N hB hT
    (descendedCoefficient K S D a c (fun j => conj (z j)))
  have hb' : (∑ b ∈ B, ‖∑ j ∈ T,
      descendedCoefficient K S D a c (fun j => conj (z j)) j *
        positiveKernel K S D b j‖ ^ 2) ≤
      ExteriorSieve.B K S D Y N *
        ∑ j ∈ T, ‖descendedCoefficient K S D a c (fun j => conj (z j)) j‖ ^ 2 := by
    simpa only [FiniteKernel.form, FiniteKernel.energy, mul_comm] using hb
  simp_rw [extracted_row_sum_second K S D hD, Complex.norm_conj]
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Complex.norm_conj] using
      descendedCoefficient_energy_le K S D a c T (fun j => conj (z j)))
    (ExteriorSieve.B_nonneg K S D Y N))

theorem tripleEnergy_le_first (hD : AllowedGeneratorInput K S D)
    (A B C T : Finset (ExteriorIdeal K S)) (X N : ℝ)
    (hA : ∀ a ∈ A, Squarefree a.val.val ∧ exteriorNorm K S a ≤ X)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (z : ExteriorIdeal K S → ℂ) :
    tripleEnergy K S D A B C T z ≤
      (C.card : ℝ) * (B.card : ℝ) * ExteriorSieve.B K S D X N * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  unfold tripleEnergy
  calc
    _ = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A,
        ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S a b c) j‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ ≤ ∑ _b ∈ B, ∑ _c ∈ C,
        ExteriorSieve.B K S D X N * ∑ j ∈ T, ‖z j‖ ^ 2 :=
      Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
        first_block_bound K S D hD A T X N hA hT b c z
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem tripleEnergy_le_second (hD : AllowedGeneratorInput K S D)
    (A B C T : Finset (ExteriorIdeal K S)) (Y N : ℝ)
    (hB : ∀ b ∈ B, Squarefree b.val.val ∧ exteriorNorm K S b ≤ Y)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (z : ExteriorIdeal K S → ℂ) :
    tripleEnergy K S D A B C T z ≤
      (C.card : ℝ) * (A.card : ℝ) * ExteriorSieve.B K S D Y N * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  unfold tripleEnergy
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B,
        ‖∑ j ∈ T, z j * positiveKernel K S D (compose K S a b c) j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ ≤ ∑ _a ∈ A, ∑ _c ∈ C,
        ExteriorSieve.B K S D Y N * ∑ j ∈ T, ‖z j‖ ^ 2 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
        second_block_bound K S D hD B T Y N hB hT a c z
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Completion to actual cubic parts gives the smaller of the two squarefree sieve costs. -/
theorem extraction_image_bound (hD : AllowedGeneratorInput K S D)
    (R T : Finset (ExteriorIdeal K S)) (X Y N : ℝ)
    (hfirst : ∀ I ∈ R, exteriorNorm K S (exteriorFirst K S I) ≤ X)
    (hsecond : ∀ I ∈ R, exteriorNorm K S (exteriorSecond K S I) ≤ Y)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (z : ExteriorIdeal K S → ℂ) :
    energy K S D 2 R T z ≤ min
      (((cubeImage K S R).card : ℝ) * ((secondImage K S R).card : ℝ) *
        ExteriorSieve.B K S D X N * ∑ j ∈ T, ‖z j‖ ^ 2)
      (((cubeImage K S R).card : ℝ) * ((firstImage K S R).card : ℝ) *
        ExteriorSieve.B K S D Y N * ∑ j ∈ T, ‖z j‖ ^ 2) := by
  apply (energy_le_product_completion K S D R T z).trans
  apply le_min
  · apply tripleEnergy_le_first K S D hD _ _ _ T X N _ hT z
    intro a ha
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨exteriorFirst_squarefree K S I, hfirst I hI⟩
  · apply tripleEnergy_le_second K S D hD _ _ _ T Y N _ hT z
    intro b hb
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨exteriorSecond_squarefree K S I, hsecond I hI⟩

private theorem card_le_ideal_count (R : Finset (ExteriorIdeal K S)) (X : ℝ)
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ X) :
    R.card ≤ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals K X).card := by
  have hsub : R.image (ExteriorSieve.underlyingIdeal K S) ⊆
      DedekindZetaZeroFree.LargeSieve.boundedNormIdeals K X := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr (hR J hJ)
  simpa only [Finset.card_image_of_injective _ (ExteriorSieve.underlyingIdeal_injective K S)]
    using Finset.card_le_card hsub

/-- The full unrestricted cube part costs its actual linear ideal count.
No cancellation estimate is assumed: the squarefree norms on the right are the
defined operators of this same actual kernel. -/
theorem exists_fixed_extraction_block_bound (hD : AllowedGeneratorInput K S D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R T : Finset (ExteriorIdeal K S)) (X Y H N : ℝ),
      1 ≤ X → 1 ≤ Y → 1 ≤ H →
      (∀ I ∈ R, exteriorNorm K S (exteriorFirst K S I) ≤ X) →
      (∀ I ∈ R, exteriorNorm K S (exteriorSecond K S I) ≤ Y) →
      (∀ I ∈ R, exteriorNorm K S (exteriorCube K S I) ≤ H) →
      (∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N) →
      ∀ z : ExteriorIdeal K S → ℂ,
        energy K S D 2 R T z ≤
          C * H * min (Y * ExteriorSieve.B K S D X N)
            (X * ExteriorSieve.B K S D Y N) * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound K
  have hApos : 0 < A := by linarith
  refine ⟨A ^ 2, by positivity, ?_⟩
  intro R T X Y H N hX hY hH hfirst hsecond hcube hT z
  have hca : ((firstImage K S R).card : ℝ) ≤ A * X := by
    apply (Nat.cast_le.mpr (card_le_ideal_count K S (firstImage K S R) X ?_)).trans
      (hcount X hX)
    intro a ha
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
    exact hfirst I hI
  have hcb : ((secondImage K S R).card : ℝ) ≤ A * Y := by
    apply (Nat.cast_le.mpr (card_le_ideal_count K S (secondImage K S R) Y ?_)).trans
      (hcount Y hY)
    intro b hb
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hb
    exact hsecond I hI
  have hcc : ((cubeImage K S R).card : ℝ) ≤ A * H := by
    apply (Nat.cast_le.mpr (card_le_ideal_count K S (cubeImage K S R) H ?_)).trans
      (hcount H hH)
    intro c hc
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hc
    exact hcube I hI
  have hE : 0 ≤ ∑ j ∈ T, ‖z j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfirstBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hcc hcb (Nat.cast_nonneg _) (by positivity))
      (ExteriorSieve.B_nonneg K S D X N)) hE
  have hsecondBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hcc hca (Nat.cast_nonneg _) (by positivity))
      (ExteriorSieve.B_nonneg K S D Y N)) hE
  apply (extraction_image_bound K S D hD R T X Y N hfirst hsecond hT z).trans
  apply (min_le_min hfirstBound hsecondBound).trans_eq
  have hP : 0 ≤ A ^ 2 * H * (∑ j ∈ T, ‖z j‖ ^ 2) := by positivity
  rw [show (A * H) * (A * Y) * ExteriorSieve.B K S D X N * (∑ j ∈ T, ‖z j‖ ^ 2) =
      (A ^ 2 * H * (∑ j ∈ T, ‖z j‖ ^ 2)) * (Y * ExteriorSieve.B K S D X N) by ring,
    show (A * H) * (A * X) * ExteriorSieve.B K S D Y N * (∑ j ∈ T, ‖z j‖ ^ 2) =
      (A ^ 2 * H * (∑ j ∈ T, ‖z j‖ ^ 2)) * (X * ExteriorSieve.B K S D Y N) by ring,
    ← mul_min_of_nonneg _ _ hP]
  ring

end CubicSieve.AnalyticExtraction
