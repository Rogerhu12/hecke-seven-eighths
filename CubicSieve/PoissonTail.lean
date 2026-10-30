import CubicSieve.PoissonBlocks
import CubicSieve.OrbitDyadic

/-! Absolute convergence and the actual nonzero-orbit Poisson tail. Both
column norms stay inside the common Gaussian profile until Mellin transfer. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonTail

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows CubicSieve.OrbitKernel
open CubicSieve.AnalyticDualNorm
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

def row (T : Finset (ExteriorIdeal K S)) (M : ℝ) (z : ↥T → ℂ)
    (q : Orbits K S) : ℂ :=
  ∑ I : T, ∑ J : T, if IsCoprime I.val.val.val J.val.val.val then
    (coefficient K S D I.val q * z I) * star (coefficient K S D J.val q * z J) *
      Profile.Gaussian.rawEnvelope A
        (M * (sIntegerOrbitNorm K S (Γ K S) q).val /
          (exteriorNorm K S I.val * exteriorNorm K S J.val)) else 0

theorem series_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 0 < M → 1 ≤ N →
      Summable (AnalyticDecay.weightedTerm (fun H => U K S D H N) (M / N ^ 2) (1 / 6)) →
      ∀ T : Finset (ExteriorIdeal K S),
        (∀ I ∈ T, Squarefree I.val.val ∧ exteriorNorm K S I ≤ N) → ∀ z : ↥T → ℂ,
        Summable (fun q => ‖row A D T M z q‖) ∧
          (∑' q, ‖row A D T M z q‖) ≤
            C * N ^ ε * (∑ I : T, ‖z I‖ ^ 2) *
              ∑' j : ℕ, AnalyticDecay.weightedTerm (fun H => U K S D H N) (M / N ^ 2) (1 / 6) j := by
  obtain ⟨C, hC, hb⟩ := PoissonBlocks.actual_profile_block_bound A D ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN hs T hT z
  let L : ℝ := C * N ^ ε * ∑ I : T, ‖z I‖ ^ 2
  let w := AnalyticDecay.weightedTerm (fun H => U K S D H N) (M / N ^ 2) (1 / 6)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hw (j : ℕ) : 0 ≤ w j := by
    dsimp [w, AnalyticDecay.weightedTerm]
    exact div_nonneg (mul_nonneg (U_nonneg K S D _ _) (Real.rpow_nonneg (by positivity) _))
      (by positivity)
  have hblocks (j : ℕ) (R : Finset (Orbits K S))
      (hR : ∀ q ∈ R, (2 : ℝ) ^ j ≤ (sIntegerOrbitNorm K S (Γ K S) q).val ∧
        (sIntegerOrbitNorm K S (Γ K S) q).val ≤ (2 : ℝ) ^ (j + 1)) :
      (∑ q ∈ R, ‖row A D T M z q‖) ≤ L * w (j + 1) := by
    have hr : ∀ q ∈ R, (2 : ℝ) ^ (j + 1) / 2 ≤
        (sIntegerOrbitNorm K S (Γ K S) q).val ∧
        (sIntegerOrbitNorm K S (Γ K S) q).val ≤ (2 : ℝ) ^ (j + 1) := by
      intro q hq
      have he : (2 : ℝ) ^ (j + 1) / 2 = (2 : ℝ) ^ j := by rw [pow_succ]; ring
      rw [he]
      exact hR q hq
    have hh := hb ((2 : ℝ) ^ (j + 1)) N M (one_le_pow₀ (by norm_num)) hN hM R T hr hT z
    rw [← Finset.sum_coe_sort R (fun q => ‖row A D T M z q‖)]
    change (∑ q : R, ‖PoissonBlocks.blockRow A D R T M z q‖) ≤ _
    convert hh using 1
    dsimp only [L, w, AnalyticDecay.weightedTerm]
    rw [show M / N ^ 2 * (2 : ℝ) ^ (j + 1) = M * (2 : ℝ) ^ (j + 1) / N ^ 2 by ring]
    ring
  have hh := OrbitDyadic.tsum_le_of_blocks K S D (fun q => ‖row A D T M z q‖)
    (fun q => norm_nonneg _) (fun j => L * w j) (fun j => mul_nonneg hL (hw j))
    (hs.mul_left L) hblocks
  refine ⟨hh.1, ?_⟩
  simpa only [tsum_mul_left] using hh.2

theorem actual_tail (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 0 < M → 1 ≤ N →
      ∀ T : Finset (ExteriorIdeal K S),
        (∀ I ∈ T, Squarefree I.val.val ∧ exteriorNorm K S I ≤ N) → ∀ z : ↥T → ℂ,
        Summable (fun q => ‖row A D T M z q‖) ∧
          (M / N) * (∑' q, ‖row A D T M z q‖) ≤
            C * N ^ (ε + 3 * δ) * M ^ (-δ) *
              (AnalyticDecay.decayConstant (1 / 3 + δ - 1 / 6) * (M * N) ^ (2 / 3 : ℝ) +
                AnalyticDecay.decayConstant (ξ + δ - 1 / 6) * M ^ (1 - ξ) * N ^ (2 * ξ - 1)) *
                  ∑ I : T, ‖z I‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ := series_bound A D ε hε
  obtain ⟨C₁, hC₁, ht⟩ := weighted_poisson_tail K S D hD h hξ hξ2 δ hδ hδsmall
  obtain ⟨C₂, hC₂, hs⟩ := weighted_dual_growth K S D hD h hξ hξ2 δ hδ hδsmall
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro M N hM hN T hT z
  have hN0 : 0 < N := by linarith
  have hweighted := (hs N (M / N ^ 2) hN (by positivity)).1
  obtain ⟨hrow, hsum⟩ := hb M N hM hN hweighted T hT z
  refine ⟨hrow, ?_⟩
  have hE : 0 ≤ C₀ * N ^ ε * ∑ I : T, ‖z I‖ ^ 2 := by positivity
  have ht' := mul_le_mul_of_nonneg_left (ht M N hM hN) hE
  have hsum' := mul_le_mul_of_nonneg_left hsum (div_nonneg hM.le hN0.le)
  have hr : N ^ (ε + 3 * δ) = N ^ ε * N ^ (3 * δ) := Real.rpow_add hN0 _ _
  rw [hr]
  apply hsum'.trans
  convert ht' using 1 <;> ring

end CubicSieve.PoissonTail
