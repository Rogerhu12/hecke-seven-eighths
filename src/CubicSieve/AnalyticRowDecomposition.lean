import CubicSieve.AnalyticFactorization
import CubicSieve.ExteriorKernel
import CubicSieve.Algebra

/-!
Literal cubic extraction of the actual exterior residue rows. The cube part
keeps the full common-prime zero mask. Extracted coefficient energy can only
decrease. These are the arithmetic identities used before applying the
squarefree sieve norm to the dual-frequency rows of a Poisson transform.
-/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.AnalyticRowDecomposition

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticFactorization
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem symbol_row_mul (hD : AllowedGeneratorInput K S D) (A B J : ExteriorIdeal K S) :
    symbol K S D (exteriorMul K S A B) J = symbol K S D A J * symbol K S D B J := by
  obtain ⟨u, hu⟩ := hD.multiplicative A B
  dsimp only [symbol, idealSymbol]
  rw [hu, mul_assoc, sIntegerSexticIdealEvaluation_mul_sixth_power_unit,
    sIntegerSexticIdealEvaluation_mul]

theorem positiveKernel_row_mul (hD : AllowedGeneratorInput K S D)
    (A B J : ExteriorIdeal K S) :
    positiveKernel K S D (exteriorMul K S A B) J =
      positiveKernel K S D A J * positiveKernel K S D B J := by
  simp only [positiveKernel, kernel, zpow_ofNat,
    symbol_row_mul K S D hD, mul_pow]

theorem positiveKernel_square_eq_conj (A J : ExteriorIdeal K S) :
    positiveKernel K S D A J ^ 2 = conj (positiveKernel K S D A J) := by
  exact Algebra.square_eq_star_of_fourth_eq _ (positiveKernel_pow_four K S D A J)

/-- All three extracted parts remain in the original S-exterior ideal type. -/
theorem composed_kernel (hD : AllowedGeneratorInput K S D) (A B C J : ExteriorIdeal K S) :
    positiveKernel K S D (compose K S A B C) J =
      positiveKernel K S D A J * conj (positiveKernel K S D B J) *
        (if IsCoprime C.val.val J.val.val then 1 else 0) := by
  calc
    _ = positiveKernel K S D A J * positiveKernel K S D B J ^ 2 *
        positiveKernel K S D C J ^ 3 := by
      simp only [compose, positiveKernel_row_mul K S D hD]
      ring
    _ = _ := by
      rw [positiveKernel_square_eq_conj, positiveKernel_cube_coprime_mask]

theorem extracted_kernel (hD : AllowedGeneratorInput K S D) (I J : ExteriorIdeal K S) :
    positiveKernel K S D I J =
      positiveKernel K S D (exteriorFirst K S I) J *
        conj (positiveKernel K S D (exteriorSecond K S I) J) *
          (if IsCoprime (exteriorCube K S I).val.val J.val.val then 1 else 0) := by
  simpa only [exterior_factorization] using composed_kernel K S D hD
    (exteriorFirst K S I) (exteriorSecond K S I) (exteriorCube K S I) J

def descendedCoefficient (B C : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) (J : ExteriorIdeal K S) : ℂ :=
  z J * conj (positiveKernel K S D B J) *
    (if IsCoprime C.val.val J.val.val then 1 else 0)

/-- Exact finite row sum identity, including every common-prime zero. -/
theorem extracted_row_sum (hD : AllowedGeneratorInput K S D)
    (A B C : ExteriorIdeal K S) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    (∑ J ∈ T, z J * positiveKernel K S D (compose K S A B C) J) =
      ∑ J ∈ T, descendedCoefficient K S D B C z J * positiveKernel K S D A J := by
  apply Finset.sum_congr rfl
  intro J _
  rw [composed_kernel K S D hD]
  dsimp only [descendedCoefficient]
  ring

/-- The second squarefree part supplies the other orientation of the extraction minimum. -/
theorem extracted_row_sum_second (hD : AllowedGeneratorInput K S D)
    (A B C : ExteriorIdeal K S) (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    (∑ J ∈ T, z J * positiveKernel K S D (compose K S A B C) J) =
      conj (∑ J ∈ T,
        descendedCoefficient K S D A C (fun J => conj (z J)) J *
          positiveKernel K S D B J) := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [composed_kernel K S D hD]
  dsimp only [descendedCoefficient]
  by_cases h : IsCoprime C.val.val J.val.val <;>
    simp only [h, ite_true, ite_false, map_mul, map_zero,
      Complex.conj_conj, mul_one, mul_zero, zero_mul]
  ring

theorem norm_descendedCoefficient_le (B C : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) (J : ExteriorIdeal K S) :
    ‖descendedCoefficient K S D B C z J‖ ≤ ‖z J‖ := by
  unfold descendedCoefficient
  by_cases h : IsCoprime C.val.val J.val.val
  · rw [ite_eq_left h, mul_one, norm_mul, Complex.norm_conj]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_kernel_le_one K S D 2 (Or.inl rfl) B J)
  · rw [ite_eq_right h, mul_zero, norm_zero]
    exact norm_nonneg _

theorem descendedCoefficient_energy_le (B C : ExteriorIdeal K S)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ) :
    (∑ J ∈ T, ‖descendedCoefficient K S D B C z J‖ ^ 2) ≤ ∑ J ∈ T, ‖z J‖ ^ 2 := by
  exact Finset.sum_le_sum fun J _ => pow_le_pow_left₀ (norm_nonneg _)
    (norm_descendedCoefficient_le K S D B C z J) 2

end CubicSieve.AnalyticRowDecomposition
