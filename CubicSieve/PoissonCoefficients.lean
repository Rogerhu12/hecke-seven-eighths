import CubicSieve.GaussPair

/-! Separate the actual Gauss phase and inverse square-root ideal norms into
the two column coefficients. The annular energy loss is exactly 2/N. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonCoefficients

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.GaussPair
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def dual (z : ExteriorIdeal K S → ℂ) (I : ExteriorIdeal K S) : ℂ :=
  star (z I * thetaGamma K S D I 2) * normalizer K S I

theorem dual_norm_sq (z : ExteriorIdeal K S → ℂ) (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) :
    ‖dual K S D z I‖ ^ 2 = ‖z I‖ ^ 2 / exteriorNorm K S I := by
  have hNI : 0 ≤ exteriorNorm K S I := by unfold exteriorNorm; positivity
  rw [dual, norm_mul, norm_star, norm_mul,
    GaussSquarefree.thetaGamma_norm K S D I hI 2 (Or.inl rfl), mul_one]
  simp only [normalizer, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hNI,
    div_eq_mul_inv]

theorem pair_scalar (z : ExteriorIdeal K S → ℂ) (I J : ExteriorIdeal K S) :
    star (z I) * z J * (Real.sqrt (exteriorNorm K S I * exteriorNorm K S J) : ℂ)⁻¹ *
      (star (thetaGamma K S D I 2) * thetaGamma K S D J 2) =
        dual K S D z I * star (dual K S D z J) := by
  have hNI : 0 ≤ exteriorNorm K S I := by unfold exteriorNorm; positivity
  rw [Real.sqrt_mul hNI, Complex.ofReal_mul, mul_inv]
  simp only [dual, normalizer, map_mul, star_star, map_inv₀,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem annular_energy (T : Finset (ExteriorIdeal K S)) (N : ℝ) (hN : 0 < N)
    (hT : ∀ I ∈ T, Squarefree I.val.val ∧ N / 2 ≤ exteriorNorm K S I)
    (z : ExteriorIdeal K S → ℂ) :
    (∑ I ∈ T, ‖dual K S D z I‖ ^ 2) ≤ (2 / N) * ∑ I ∈ T, ‖z I‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  rw [dual_norm_sq K S D z I (hT I hI).1]
  calc
    _ ≤ ‖z I‖ ^ 2 / (N / 2) := div_le_div_of_nonneg_left
      (sq_nonneg _) (by linarith) (hT I hI).2
    _ = (2 / N) * ‖z I‖ ^ 2 := by ring

end CubicSieve.PoissonCoefficients
