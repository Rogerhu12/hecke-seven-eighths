import CubicSieve.PoissonEstimate
import CubicSieve.AnalyticGcdSeries
import CubicSieve.AnalyticGcdBound

/-! The proved coprime Poisson estimate supplies every genuine gcd descendant.
The infinite row descent, exact scales, signed Möbius terms and coefficient
divisor budget are retained through the actual annular smooth-energy bound. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GcdPoissonAssembly

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open CubicSieve.AnalyticGcd CubicSieve.AnalyticSmoothing
open CubicSieve.OrbitRows CubicSieve.OrbitKernel
open DedekindZetaZeroFree.AbelianQuotient.Theta
open scoped Classical BigOperators ComplexConjugate

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
local instance : MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance : BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩

theorem descendantSeries_eq_sourceSeries (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K S)) (z : ExteriorIdeal K S → ℂ)
    (d e : ExteriorIdeal K S) :
    AnalyticGcdSeries.descendantSeries K S D (traceGaussianSchwartz K)
      (Profile.finiteTest A) M hM T z d e =
      PoissonSmoothed.sourceSeries A D (M / exteriorNorm K S e)
        (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e]))
        (dividedSet K S T d) (pulledCoefficient K S D d e z) := by
  rw [PoissonSmoothed.sourceSeries_eq_tsum]
  unfold AnalyticGcdSeries.descendantSeries
  apply tsum_congr
  intro q
  have hp : AnalyticGcdSeries.profile K S (traceGaussianSchwartz K) (Profile.finiteTest A)
      (M / exteriorNorm K S e) (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q =
      PoissonSmoothed.sourceProfile A (M / exteriorNorm K S e)
        (div_pos hM (by linarith [AnalyticDyadic.one_le_norm K S e])) q := rfl
  rw [hp]
  congr 1
  unfold AnalyticGcdSeries.coprimeGram PoissonSmoothed.coprimeGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hc : IsCoprime a.val.val b.val.val
  · rw [ite_eq_left hc, ite_eq_left hc]
    simp only [AnalyticGcdSeries.pair, map_mul, star_mul, Complex.star_def]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem dividedSet_annular (T : Finset (ExteriorIdeal K S)) (N : ℝ)
    (hT : ∀ I ∈ T, Squarefree I.val.val ∧ N / 2 ≤ exteriorNorm K S I ∧ exteriorNorm K S I ≤ N)
    (d : ExteriorIdeal K S) :
    ∀ a ∈ dividedSet K S T d, Squarefree a.val.val ∧
      (N / exteriorNorm K S d) / 2 ≤ exteriorNorm K S a ∧
      exteriorNorm K S a ≤ N / exteriorNorm K S d := by
  intro a ha
  have hda := hT _ ((mem_dividedSet K S T d a).mp ha)
  have hd0 : 0 < exteriorNorm K S d := by linarith [AnalyticDyadic.one_le_norm K S d]
  have hmul : exteriorNorm K S (exteriorMul K S d a) =
      exteriorNorm K S d * exteriorNorm K S a := by
    simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  refine ⟨dividedSet_squarefree K S T d (fun I hI => (hT I hI).1) a ha, ?_,
    dividedSet_norm K S T d N (fun I hI => (hT I hI).2.2) a ha⟩
  have hh : (N / 2) / exteriorNorm K S d ≤ exteriorNorm K S a :=
    (div_le_iff₀ hd0).mpr (by rw [hmul] at hda; nlinarith [hda.2.1])
  simpa only [div_div, mul_comm] using hh

theorem annular_smoothEnergy_bound (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (ε ρ δ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, ∀ hM : 0 < M, 1 ≤ N →
      ∀ T : Finset (ExteriorIdeal K S),
        (∀ I ∈ T, Squarefree I.val.val ∧ N / 2 ≤ exteriorNorm K S I ∧ exteriorNorm K S I ≤ N) →
        ∀ z : ExteriorIdeal K S → ℂ,
        smoothEnergy K S D (traceGaussianSchwartz K) (Profile.finiteTest A) M hM T z ≤
          C * N ^ ρ * (M + N ^ (ε + 3 * δ) * M ^ (-δ) *
            ((M * N) ^ (2 / 3 : ℝ) + M ^ (1 - ξ) * N ^ (2 * ξ - 1))) *
              ∑ I ∈ T, ‖z I‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ := PoissonEstimate.actual_annular_bound A D hD h hξ hξ2 ε δ hε hδ hδsmall
  obtain ⟨Cρ, hCρ, hbudget⟩ := pulledCoefficient_epsilon_budget K S D ρ hρ
  refine ⟨C₀ * Cρ, mul_pos hC₀ hCρ, ?_⟩
  intro M N hM hN T hT z
  have hN0 : 0 < N := by linarith
  let F := M + N ^ ε * poissonEnvelope M N δ ξ 1 1
  have hF : 0 ≤ F := add_nonneg hM.le (mul_nonneg (by positivity)
    (poissonEnvelope_nonneg M N δ ξ 1 1 hM.le hN0.le zero_le_one zero_le_one))
  have hshape : F = M + N ^ (ε + 3 * δ) * M ^ (-δ) *
      ((M * N) ^ (2 / 3 : ℝ) + M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
    dsimp only [F, poissonEnvelope]
    rw [Real.rpow_add hN0 ε (3 * δ)]
    simp only [one_mul]
    ring
  let E := fun d e : ExteriorIdeal K S =>
    ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2
  let V := fun d e : ExteriorIdeal K S => AnalyticGcdSeries.descendantSeries K S D
    (traceGaussianSchwartz K) (Profile.finiteTest A) M hM T z d e
  have hpoint (d : ExteriorIdeal K S) (hd : d ∈ gcdImage K S T)
      (e : ExteriorIdeal K S) (he : e ∈ divisors K S d) : ‖V d e‖ ≤ C₀ * F * E d e := by
    have hd0 : 0 < exteriorNorm K S d := by linarith [AnalyticDyadic.one_le_norm K S d]
    have he0 : 0 < exteriorNorm K S e := by linarith [AnalyticDyadic.one_le_norm K S e]
    have hNd : 1 ≤ N / exteriorNorm K S d :=
      (descendant_scales K S T N (fun I hI => (hT I hI).2.2) d hd e he).1
    have hMd : 0 < M / exteriorNorm K S e := div_pos hM he0
    have hNd0 : 0 < N / exteriorNorm K S d := by linarith
    have hp := hb (M / exteriorNorm K S e) (N / exteriorNorm K S d) hMd hNd
      (dividedSet K S T d) (dividedSet_annular A T N hT d) (pulledCoefficient K S D d e z)
    rw [← descendantSeries_eq_sourceSeries A D M hM T z d e] at hp
    have henv := actual_envelope_descendant_le K S M N δ ξ 1 1 hM hN0 hδ.le
      (by linarith) zero_le_one zero_le_one d e he
    have henv0 : 0 ≤ poissonEnvelope (M / exteriorNorm K S e) (N / exteriorNorm K S d) δ ξ 1 1 :=
      poissonEnvelope_nonneg _ _ _ _ _ _ hMd.le hNd0.le zero_le_one zero_le_one
    have hpow : (N / exteriorNorm K S d) ^ ε ≤ N ^ ε :=
      Real.rpow_le_rpow hNd0.le (div_le_self hN0.le (AnalyticDyadic.one_le_norm K S d)) hε.le
    have hcost : M / exteriorNorm K S e +
        (N / exteriorNorm K S d) ^ (ε + 3 * δ) * (M / exteriorNorm K S e) ^ (-δ) *
          (((M / exteriorNorm K S e) * (N / exteriorNorm K S d)) ^ (2 / 3 : ℝ) +
            (M / exteriorNorm K S e) ^ (1 - ξ) * (N / exteriorNorm K S d) ^ (2 * ξ - 1)) ≤ F := by
      calc
        _ = M / exteriorNorm K S e + (N / exteriorNorm K S d) ^ ε *
            poissonEnvelope (M / exteriorNorm K S e) (N / exteriorNorm K S d) δ ξ 1 1 := by
          rw [Real.rpow_add hNd0 ε (3 * δ)]
          dsimp only [poissonEnvelope]
          simp only [one_mul]
          ring
        _ ≤ F := add_le_add (div_le_self hM.le (AnalyticDyadic.one_le_norm K S e))
          (mul_le_mul hpow henv henv0 (by positivity))
    apply hp.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hC₀.le)
      (Finset.sum_nonneg (fun a ha => sq_nonneg _))
  have hsum : (∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
      ‖(UniqueFactorizationMonoid.moebius e.val.val : ℂ) * V d e‖) ≤
      C₀ * F * (Cρ * N ^ ρ * ∑ I ∈ T, ‖z I‖ ^ 2) := by
    calc
      _ ≤ ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d, C₀ * F * E d e := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        rw [norm_mul]
        have hm := mul_le_mul_of_nonneg_right (moebius_norm_le_one K S e) (norm_nonneg (V d e))
        have hm' : ‖(UniqueFactorizationMonoid.moebius e.val.val : ℂ)‖ * ‖V d e‖ ≤ ‖V d e‖ := by
          simpa only [one_mul] using hm
        exact hm'.trans (hpoint d hd e he)
      _ = C₀ * F * (∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d, E d e) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hbudget N hN (gcdImage K S T) T (fun I hI => (hT I hI).2.2) z) (mul_nonneg hC₀.le hF)
  calc
    _ = (∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (UniqueFactorizationMonoid.moebius e.val.val : ℂ) * V d e).re :=
      AnalyticGcdSeries.gaussian_smoothEnergy_eq_descent_re K A D M hM T z
    _ ≤ ‖∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        (UniqueFactorizationMonoid.moebius e.val.val : ℂ) * V d e‖ := Complex.re_le_norm _
    _ ≤ ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d,
        ‖(UniqueFactorizationMonoid.moebius e.val.val : ℂ) * V d e‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => norm_sum_le _ _))
    _ ≤ C₀ * F * (Cρ * N ^ ρ * ∑ I ∈ T, ‖z I‖ ^ 2) := hsum
    _ = _ := by rw [hshape]; ring

end CubicSieve.GcdPoissonAssembly
