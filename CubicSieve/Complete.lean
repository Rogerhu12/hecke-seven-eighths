import CubicSieve.GcdPoissonAssembly
import CubicSieve.GaussianColumnBlocks
import CubicSieve.Initial
import CubicSieve.Endpoint

/-! Assembly of the actual Poisson improvement and the original exterior
ideal target. This file is a candidate until its dependency closure compiles
and its endpoint passes the recursive axiom guard. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Complete

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.AnalyticSmoothing CubicSieve.GaussianColumnBlocks
open DedekindZetaZeroFree.AbelianQuotient.Theta
open DedekindZetaZeroFree.LargeSieve.Vendor
open scoped Classical BigOperators

private def tail (M N ξ : ℝ) : ℝ :=
  (M * N) ^ (2 / 3 : ℝ) + M ^ (1 - ξ) * N ^ (2 * ξ - 1)

private theorem tail_nonneg (M N ξ : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    0 ≤ tail M N ξ := by unfold tail; positivity

private theorem tail_mono (M x N ξ : ℝ) (hM : 0 ≤ M) (hx : 0 ≤ x)
    (hxN : x ≤ N) (hξ : 1 ≤ ξ) : tail M x ξ ≤ tail M N ξ := by
  unfold tail
  apply add_le_add
  · exact Real.rpow_le_rpow (mul_nonneg hM hx)
      (mul_le_mul_of_nonneg_left hxN hM) (by norm_num)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx hxN (by linarith)) (Real.rpow_nonneg hM _)

private def budget (M N ξ a : ℝ) : ℝ :=
  N ^ a * (M + N ^ (4 * a) * M ^ (-a) * tail M N ξ)

private theorem budget_le (M x N ξ a : ℝ) (hM : 1 ≤ M) (hx : 1 ≤ x)
    (hxN : x ≤ N) (hξ : 1 ≤ ξ) (ha : 0 < a) :
    budget M x ξ a ≤ N ^ (5 * a) * (M + tail M N ξ) := by
  have hM0 : 0 < M := by linarith
  have hx0 : 0 < x := by linarith
  have hN : 1 ≤ N := hx.trans hxN
  have hN0 : 0 < N := by linarith
  have htx : 0 ≤ tail M x ξ := tail_nonneg M x ξ hM0.le hx0.le
  have hp := Real.rpow_le_rpow hx0.le hxN ha.le
  have hp4 := Real.rpow_le_rpow hx0.le hxN (by linarith : 0 ≤ 4 * a)
  have hm : M ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hn4 : 1 ≤ N ^ (4 * a) := Real.one_le_rpow hN (by linarith)
  have hprod : x ^ (4 * a) * M ^ (-a) ≤ N ^ (4 * a) := by
    simpa only [mul_one] using mul_le_mul hp4 hm
      (Real.rpow_nonneg hM0.le _) (Real.rpow_nonneg hN0.le _)
  have ht := mul_le_mul hprod (tail_mono M x N ξ hM0.le hx0.le hxN hξ)
    htx (Real.rpow_nonneg hN0.le _)
  have hi : M + x ^ (4 * a) * M ^ (-a) * tail M x ξ ≤
      N ^ (4 * a) * (M + tail M N ξ) := by
    have hm' : M ≤ N ^ (4 * a) * M := le_mul_of_one_le_left hM0.le hn4
    nlinarith
  have hh := mul_le_mul hp hi (by positivity :
    0 ≤ M + x ^ (4 * a) * M ^ (-a) * tail M x ξ) (Real.rpow_nonneg hN0.le _)
  unfold budget
  apply hh.trans_eq
  rw [show 5 * a = a + 4 * a by ring, Real.rpow_add hN0]
  ring

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
local instance normOneMeasurable : MeasurableSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance normOneBorel : BorelSpace
    (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩

theorem full_smooth_bound (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, ∀ hM : 1 ≤ M, 1 ≤ N →
      ∀ T : Finset (ExteriorIdeal K S),
        (∀ I ∈ T, Squarefree I.val.val ∧ exteriorNorm K S I ≤ N) →
      ∀ z : ExteriorIdeal K S → ℂ,
        smoothEnergy K S D (traceGaussianSchwartz K) (Profile.finiteTest A)
          M (by linarith) T z ≤ C * N ^ (7 * θ) * (M + tail M N ξ) * ∑ I ∈ T, ‖z I‖ ^ 2 := by
  let a := θ / 4
  have ha : 0 < a := by dsimp [a]; linarith
  have hasmall : a < 1 / 2 := by dsimp [a]; linarith
  obtain ⟨C₀, hC₀, hb⟩ := GcdPoissonAssembly.annular_smoothEnergy_bound A D hD h hξ hξ2
    a a a ha ha ha hasmall
  let L := 2 + 1 / (a * Real.log 2)
  have hL : 0 < L := dyadicLength_small_power_constant_pos ha
  refine ⟨C₀ * L, mul_pos hC₀ hL, ?_⟩
  intro M N hM hN T hT z
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have htail : 0 ≤ tail M N ξ := tail_nonneg M N ξ hM0.le hN0.le
  let J := indices K S T
  let E := fun j => ∑ I ∈ block K S T j, ‖z I‖ ^ 2
  let F := C₀ * N ^ (5 * a) * (M + tail M N ξ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hblock (j : ℕ) : smoothEnergy K S D (traceGaussianSchwartz K)
      (Profile.finiteTest A) M hM0 (block K S T j) z ≤ F * E j := by
    have hs := scale_bounds N hN j
    have hh := hb M (scale N j) hM0 hs.1 (block K S T j) (fun I hI =>
      ⟨block_squarefree K S T (fun I hI => (hT I hI).1) j I hI,
        block_norm_bounds K S T N (fun I hI => (hT I hI).2) j I hI⟩) z
    rw [show a + 3 * a = 4 * a by ring] at hh
    have hnum := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (budget_le M (scale N j) N ξ a hM hs.1 hs.2
        (by linarith) ha) hC₀.le)
      (Finset.sum_nonneg (s := block K S T j) (fun I hI => sq_nonneg (‖z I‖)))
    apply hh.trans
    convert hnum using 1 <;> dsimp only [budget, tail, F, E] <;> ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ J) => hblock j)
  rw [← Finset.mul_sum, coefficient_energy_partition K S T z] at hsum
  have hc := indices_card_small_power K S T N a hN ha (fun I hI => (hT I hI).2)
  have hp : N ^ (6 * a) ≤ N ^ (7 * θ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [a]; linarith)
  calc
    _ ≤ (J.card : ℝ) * ∑ j ∈ J,
        smoothEnergy K S D (traceGaussianSchwartz K) (Profile.finiteTest A)
          M hM0 (block K S T j) z := gaussian_smoothEnergy_le_blocks A D M hM0 T z
    _ ≤ (J.card : ℝ) * (F * ∑ I ∈ T, ‖z I‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ (L * N ^ a) * (F * ∑ I ∈ T, ‖z I‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hF (Finset.sum_nonneg (fun I hI => sq_nonneg _)))
    _ = (C₀ * L) * N ^ (6 * a) * (M + tail M N ξ) * ∑ I ∈ T, ‖z I‖ ^ 2 := by
      rw [show 6 * a = a + 5 * a by ring, Real.rpow_add hN0]
      dsimp [F]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (mul_pos hC₀ hL).le)
        (by positivity)) (Finset.sum_nonneg (fun I hI => sq_nonneg _))

theorem fullEstimate (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) :
    Improvement.FullEstimate (ExteriorSieve.B K S D) ξ := by
  intro θ hθ hθsmall
  obtain ⟨C, hC, hb⟩ := full_smooth_bound A D hD h hξ hξ2 θ hθ hθsmall
  obtain ⟨c, hc, hlower⟩ := gaussian_uniform_ball_lower A
  refine ⟨c⁻¹ * C, mul_pos (inv_pos.mpr hc) hC, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have htail : 0 ≤ tail M N ξ := tail_nonneg M N ξ hM0.le hN0.le
  have hh := B_le_of_smoothEnergy_bound K S D (traceGaussianSchwartz K) (Profile.finiteTest A)
    (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A)
    (gaussianProfile_re_nonneg A) c hc hlower M N (C * N ^ (7 * θ) * (M + tail M N ξ))
    hM (by positivity) (fun z => hb M N hM hN (ExteriorSieve.cutoff K S N)
      (fun I hI => (ExteriorSieve.mem_cutoff K S N I).mp hI) z)
  convert hh using 1 <;> dsimp only [tail] <;> ring

theorem targetBound (hD : AllowedGeneratorInput K S D) : ExteriorSieve.TargetBound K S D := by
  apply Endpoint.target_of_analytic_estimates K S D hD
    (Initial.hasCubicExponent_two K S D hD)
  intro ξ hξ hξ2 h
  exact fullEstimate A D hD h hξ.le hξ2

end CubicSieve.Complete
