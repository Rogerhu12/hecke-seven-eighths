import Expansion.IdealDyadicExtraction
import ExpansionDetector.IdealZeroSource

/-! Coefficient mass of the literal terminal detector.  The two finite
polynomials keep their complete ideal coefficient homomorphism.  The only
counting input is the convergent ideal norm-zeta sum at exponent two. -/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open scoped NumberField Classical BigOperators
open ExpansionDetector.Fourier ExpansionDetector.IdealCutoff

variable {K : Type*} [Field K] [NumberField K]

theorem terminal_norm_le_three_mul {H : ℝ} (hH : 1 ≤ H)
    (I : Ideal (𝓞 K)) (hI : I ∈ nonzeroTerminalSet H) : idealNorm I ≤ 3 * H := by
  have hcap := ((mem_nonzeroTerminalSet H I).mp hI).1
  have hn : idealNorm I ≤ (⌈2 * H⌉₊ : ℝ) := by
    unfold idealNorm
    exact_mod_cast hcap
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * H)
  linarith

theorem sourceCoefficient_mass_le {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (N : ι → ℝ) (B C D : ℝ)
    (hN : ∀ i ∈ S, 1 ≤ N i ∧ N i ≤ B)
    (hc : ∀ i ∈ S, ‖c i‖ ≤ 1)
    (hC : (∑ i ∈ S, N i ^ (-2 : ℝ)) ≤ C)
    (s : ℂ) (hs : 0 ≤ s.re) :
    (∑ i ∈ S, ‖sourceCoefficient c N annularProfile D s i‖) ≤ B ^ 2 * C := by
  have hterm (i : ι) (hi : i ∈ S) :
      ‖sourceCoefficient c N annularProfile D s i‖ ≤ B ^ 2 * N i ^ (-2 : ℝ) := by
    have hNi : 0 < N i := zero_lt_one.trans_le (hN i hi).1
    have hpow : ‖(N i : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNi, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hN i hi).1 (neg_nonpos.mpr hs)
    have hnorm : ‖sourceCoefficient c N annularProfile D s i‖ ≤ 1 := by
      simp only [sourceCoefficient, norm_mul]
      calc
        _ ≤ (1 * 1) * 1 :=
          mul_le_mul (mul_le_mul (hc i hi) hpow (norm_nonneg _) zero_le_one)
            (annularProfile_norm_le _) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    apply hnorm.trans
    rw [Real.rpow_neg hNi.le, Real.rpow_two]
    have hB : 0 ≤ B := hNi.le.trans (hN i hi).2
    have hsq : N i ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hNi.le hB).mpr (hN i hi).2
    calc
      (1 : ℝ) = N i ^ 2 * (N i ^ 2)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hNi.ne')).symm
      _ ≤ B ^ 2 * (N i ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (sq_nonneg _))
  calc
    _ ≤ ∑ i ∈ S, B ^ 2 * N i ^ (-2 : ℝ) := Finset.sum_le_sum hterm
    _ = B ^ 2 * ∑ i ∈ S, N i ^ (-2 : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ B ^ 2 * C := mul_le_mul_of_nonneg_left hC (sq_nonneg _)

theorem inverseRawCoefficient_norm_le_one (w : Ideal (𝓞 K) →*₀ ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (D : ℝ) (I : Ideal (𝓞 K)) : ‖inverseRawCoefficient w V D I‖ ≤ 1 := by
  simp only [inverseRawCoefficient, norm_mul]
  calc
    _ ≤ (1 * 1) * 1 :=
      mul_le_mul (mul_le_mul (norm_ideal_moebius_le_one I) (hV _)
        (norm_nonneg _) zero_le_one) (hw I) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- This is uniform in the annular scale, the real and imaginary parts of
the zero, and the deleted coefficient homomorphism. -/
theorem actual_terminal_coefficient_mass (w : Ideal (𝓞 K) →*₀ ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (D H A : ℝ) (hH : 1 ≤ H) (s : ℂ) (hs : 0 ≤ s.re) (CZ : ℝ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZ : (∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    (∑ I ∈ nonzeroTerminalSet H,
      ‖sourceCoefficient (inverseRawCoefficient w V D) idealNorm annularProfile A s I‖)
        ≤ (3 * H) ^ 2 * CZ ∧
    (∑ I ∈ nonzeroTerminalSet H,
      ‖sourceCoefficient w idealNorm annularProfile A s I‖) ≤ (3 * H) ^ 2 * CZ := by
  have hN (I : Ideal (𝓞 K)) (hI : I ∈ nonzeroTerminalSet H) :
      1 ≤ idealNorm I ∧ idealNorm I ≤ 3 * H :=
    ⟨(nonzeroTerminalSet_norm_bounds hH I hI).1, terminal_norm_le_three_mul hH I hI⟩
  have hz : (∑ I ∈ nonzeroTerminalSet H, idealNorm I ^ (-2 : ℝ)) ≤ CZ :=
    (finite_ideal_zeta_two_le (nonzeroTerminalSet H) hzeta).trans hCZ
  constructor
  · exact sourceCoefficient_mass_le _ _ _ (3 * H) CZ A hN
      (fun I _ => inverseRawCoefficient_norm_le_one w hw V hV D I) hz s hs
  · exact sourceCoefficient_mass_le _ _ _ (3 * H) CZ A hN (fun I _ => hw I) hz s hs

end Expansion.Dyadic
