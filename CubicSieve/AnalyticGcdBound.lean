import CubicSieve.AnalyticGcdGram
import CubicSieve.AnalyticDecay

/-!
Triangle and divisor-energy assembly after the exact gcd/Möbius identity.
The per-descendant coprime Poisson estimate is kept as the explicit analytic
input; it is not supplied or identified with the final sieve estimate here.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcd

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def descendantGram (A T : Finset (ExteriorIdeal K S)) (w : ExteriorIdeal K S → ℝ)
    (z : ExteriorIdeal K S → ℂ) (d e : ExteriorIdeal K S) : ℂ :=
  ∑ R ∈ dividedSet K S A e, (w (exteriorMul K S e R) : ℂ) *
    coprimeGram K S D (dividedSet K S T d) R (pulledCoefficient K S D d e z)

theorem weighted_triangle_descent (hD : AllowedGeneratorInput K S D)
    (A T : Finset (ExteriorIdeal K S)) (w : ExteriorIdeal K S → ℝ)
    (hw : ∀ R ∈ A, 0 ≤ w R) (z : ExteriorIdeal K S → ℂ) :
    (∑ R ∈ A, w R * ‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2) ≤
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        ‖descendantGram K S D A T w z d e‖ := by
  have hs : 0 ≤ ∑ R ∈ A, w R * ‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 :=
    Finset.sum_nonneg (fun R hR => mul_nonneg (hw R hR) (sq_nonneg _))
  have he := weighted_gram_descent K S D hD A T (fun R => (w R : ℂ)) z
  have he' : ((∑ R ∈ A, w R * ‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (UniqueFactorizationMonoid.moebius e.val.val : ℂ) *
          descendantGram K S D A T w z d e := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, descendantGram] using he
  calc
    _ = ‖((∑ R ∈ A, w R * ‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    _ = _ := congrArg norm he'
    _ ≤ ∑ d ∈ gcdImage K S T, ‖∑ e ∈ divisors K S d,
        (UniqueFactorizationMonoid.moebius e.val.val : ℂ) *
          descendantGram K S D A T w z d e‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        ‖descendantGram K S D A T w z d e‖ := by
      apply Finset.sum_le_sum
      intro d hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (moebius_norm_le_one K S e) (norm_nonneg (descendantGram K S D A T w z d e))

def poissonEnvelope (M N δ ξ P Q : ℝ) : ℝ :=
  N ^ (3 * δ) * M ^ (-δ) *
    (P * (M * N) ^ (2 / 3 : ℝ) + Q * M ^ (1 - ξ) * N ^ (2 * ξ - 1))

theorem poissonEnvelope_nonneg (M N δ ξ P Q : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ poissonEnvelope M N δ ξ P Q := by
  unfold poissonEnvelope
  positivity

theorem actual_envelope_descendant_le (M N δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (d e : ExteriorIdeal K S) (he : e ∈ divisors K S d) :
    poissonEnvelope (M / exteriorNorm K S e) (N / exteriorNorm K S d) δ ξ P Q ≤
      poissonEnvelope M N δ ξ P Q := by
  exact AnalyticDecay.poisson_envelope_descendant_le M N
    (exteriorNorm K S e) (exteriorNorm K S d) δ ξ P Q hM hN
    (AnalyticDyadic.one_le_norm K S e)
    (norm_le_of_dvd K S e d ((mem_divisors K S d e).mp he)) hδ hξ hP hQ

/-- Numerical closure of all gcd descendants after a genuine coprime estimate. -/
theorem weighted_bound_of_descendant_bounds
    (hD : AllowedGeneratorInput K S D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N δ ξ P Q A₀ : ℝ,
      0 < M → 1 ≤ N → 0 ≤ δ → 1 ≤ ξ → 0 ≤ P → 0 ≤ Q → 0 ≤ A₀ →
      ∀ A T : Finset (ExteriorIdeal K S),
        (∀ J ∈ T, exteriorNorm K S J ≤ N) →
      ∀ w : ExteriorIdeal K S → ℝ, (∀ R ∈ A, 0 ≤ w R) →
      ∀ z : ExteriorIdeal K S → ℂ,
        (∀ d ∈ gcdImage K S T, ∀ e ∈ divisors K S d,
          ‖descendantGram K S D A T w z d e‖ ≤
            A₀ * (M / exteriorNorm K S e +
              poissonEnvelope (M / exteriorNorm K S e) (N / exteriorNorm K S d) δ ξ P Q) *
              ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2) →
        (∑ R ∈ A, w R * ‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2) ≤
          A₀ * C * N ^ ε * (M + poissonEnvelope M N δ ξ P Q) *
            ∑ J ∈ T, ‖z J‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := pulledCoefficient_epsilon_budget K S D ε hε
  refine ⟨C, hC, ?_⟩
  intro M N δ ξ P Q A₀ hM hN hδ hξ hP hQ hA₀ A T hT w hw z hdesc
  have hF : 0 ≤ M + poissonEnvelope M N δ ξ P Q :=
    add_nonneg hM.le (poissonEnvelope_nonneg M N δ ξ P Q hM.le (by linarith) hP hQ)
  have hpoint (d : ExteriorIdeal K S) (hd : d ∈ gcdImage K S T)
      (e : ExteriorIdeal K S) (he : e ∈ divisors K S d) :
      ‖descendantGram K S D A T w z d e‖ ≤
        (A₀ * (M + poissonEnvelope M N δ ξ P Q)) *
          ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2 := by
    apply (hdesc d hd e he).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun a ha => sq_nonneg _))
    apply mul_le_mul_of_nonneg_left _ hA₀
    apply add_le_add
    · exact (div_le_self hM.le (AnalyticDyadic.one_le_norm K S e))
    · exact actual_envelope_descendant_le K S M N δ ξ P Q hM (by linarith)
        hδ hξ hP hQ d e he
  calc
    _ ≤ ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        ‖descendantGram K S D A T w z d e‖ :=
      weighted_triangle_descent K S D hD A T w hw z
    _ ≤ ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (A₀ * (M + poissonEnvelope M N δ ξ P Q)) *
          ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2 := by
      exact Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hpoint d hd e he))
    _ = (A₀ * (M + poissonEnvelope M N δ ξ P Q)) *
        (∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
          ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2) := by
      simp only [Finset.mul_sum]
    _ ≤ (A₀ * (M + poissonEnvelope M N δ ξ P Q)) *
        (C * N ^ ε * ∑ J ∈ T, ‖z J‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hb N hN _ T hT z) (mul_nonneg hA₀ hF)
    _ = _ := by ring

end CubicSieve.AnalyticGcd
