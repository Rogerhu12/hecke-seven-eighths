import CubicSieve.AnalyticDyadic
import CubicSieve.AnalyticSmoothingGaussian
import Mathlib.Algebra.Order.Chebyshev

/-! Exact finite column partition and its Cauchy cost in the genuine Gaussian
orbital smooth energy. Every original sixth-unit sector remains in each tsum. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussianColumnBlocks

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open CubicSieve.AnalyticDyadic CubicSieve.AnalyticSmoothing
open CubicSieve.OrbitRows CubicSieve.OrbitKernel
open DedekindZetaZeroFree.LargeSieve.Vendor
open DedekindZetaZeroFree.AbelianQuotient.Theta
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def indices (T : Finset (ExteriorIdeal K S)) : Finset ℕ := T.image (normBin K S)
def block (T : Finset (ExteriorIdeal K S)) (j : ℕ) : Finset (ExteriorIdeal K S) :=
  T.filter (fun I => normBin K S I = j)
def scale (N : ℝ) (j : ℕ) : ℝ := min N ((2 : ℝ) ^ (j + 1))

theorem scale_bounds (N : ℝ) (hN : 1 ≤ N) (j : ℕ) : 1 ≤ scale N j ∧ scale N j ≤ N :=
  ⟨le_min hN (one_le_pow₀ (by norm_num)), min_le_left _ _⟩

theorem block_norm_bounds (T : Finset (ExteriorIdeal K S)) (N : ℝ)
    (hT : ∀ I ∈ T, exteriorNorm K S I ≤ N) (j : ℕ)
    (I : ExteriorIdeal K S) (hI : I ∈ block K S T j) :
    scale N j / 2 ≤ exteriorNorm K S I ∧ exteriorNorm K S I ≤ scale N j := by
  obtain ⟨hIT, hbin⟩ := Finset.mem_filter.mp hI
  have hb := normBin_bounds K S I
  rw [hbin] at hb
  have hs : scale N j ≤ 2 * (2 : ℝ) ^ j := by
    simpa only [scale, pow_succ, mul_comm] using
      (min_le_right N ((2 : ℝ) ^ (j + 1)))
  constructor
  · linarith [hb.1]
  · exact le_min (hT I hIT) (by simpa only [pow_succ, mul_comm] using hb.2)

theorem block_squarefree (T : Finset (ExteriorIdeal K S))
    (hT : ∀ I ∈ T, Squarefree I.val.val) (j : ℕ) :
    ∀ I ∈ block K S T j, Squarefree I.val.val :=
  fun I hI => hT I (Finset.mem_filter.mp hI).1

theorem indices_card_le (T : Finset (ExteriorIdeal K S)) (N : ℝ)
    (hT : ∀ I ∈ T, exteriorNorm K S I ≤ N) :
    (indices K S T).card ≤ dyadicLength N + 1 := by
  have hs : indices K S T ⊆ Finset.range (dyadicLength N + 1) := by
    intro j hj
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hj
    exact normBin_mem_range K S I N (hT I hI)
  simpa only [Finset.card_range] using Finset.card_le_card hs

theorem indices_card_small_power (T : Finset (ExteriorIdeal K S)) (N ε : ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε) (hT : ∀ I ∈ T, exteriorNorm K S I ≤ N) :
    ((indices K S T).card : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hc : ((indices K S T).card : ℝ) ≤ (dyadicLength N + 1 : ℝ) := by
    exact_mod_cast indices_card_le K S T N hT
  exact hc.trans (dyadicLength_small_power hε hN)

theorem coefficient_energy_partition (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    (∑ j ∈ indices K S T, ∑ I ∈ block K S T j, ‖z I‖ ^ 2) =
      ∑ I ∈ T, ‖z I‖ ^ 2 := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun I hI => Finset.mem_image.mpr ⟨I, hI, rfl⟩) (fun I => ‖z I‖ ^ 2)

variable (D : ThetaArithmeticData K S)

theorem rowSum_partition (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) (q : Orbits K S) :
    (∑ j ∈ indices K S T, ∑ I ∈ block K S T j, coefficient K S D I q * z I) =
      ∑ I ∈ T, coefficient K S D I q * z I := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun I hI => Finset.mem_image.mpr ⟨I, hI, rfl⟩)
    (fun I => coefficient K S D I q * z I)

theorem orbitEnergy_le_blocks (T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) (q : Orbits K S) :
    orbitEnergy K S D T z q ≤ ((indices K S T).card : ℝ) *
      ∑ j ∈ indices K S T, orbitEnergy K S D (block K S T j) z q := by
  unfold orbitEnergy
  rw [← rowSum_partition K S D T z q]
  have hn := norm_sum_le (indices K S T)
    (fun j => ∑ I ∈ block K S T j, coefficient K S D I q * z I)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (sq_sum_le_card_mul_sum_sq (s := indices K S T)
      (f := fun j => ‖∑ I ∈ block K S T j, coefficient K S D I q * z I‖))

section Gaussian

variable {K} (A : SArithmeticData K)
local instance : MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
local instance : BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩

theorem gaussian_smoothEnergy_le_blocks
    (D₀ : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (M : ℝ) (hM : 0 < M)
    (T : Finset (ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))))
    (z : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) → ℂ) :
    smoothEnergy K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D₀
      (traceGaussianSchwartz K) (Profile.finiteTest A) M hM T z ≤
      ((indices K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) T).card : ℝ) *
        ∑ j ∈ indices K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) T,
          smoothEnergy K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D₀
            (traceGaussianSchwartz K) (Profile.finiteTest A) M hM
            (block K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) T j) z := by
  let S₀ : Set (HeightOneSpectrum (𝓞 K)) := (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  let J := indices K S₀ T
  let p := fun q : Orbits K S₀ =>
    (sUnitOrbitalProfile K S₀ (sLocalTensorTestFunction K S₀
      (traceGaussianSchwartz K) (Profile.finiteTest A)) (orbitRadius K S₀ M hM q)).re
  have hp : ∀ q, 0 ≤ p q := fun q => gaussianProfile_re_nonneg A _
  have hs (j : ℕ) : Summable (fun q : Orbits K S₀ =>
      p q * orbitEnergy K S₀ D₀ (block K S₀ T j) z q) :=
    smoothEnergy_summable K S₀ D₀ (traceGaussianSchwartz K) (Profile.finiteTest A)
      (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A) M hM _ z
  have ht : Summable (fun q : Orbits K S₀ => p q * orbitEnergy K S₀ D₀ T z q) :=
    smoothEnergy_summable K S₀ D₀ (traceGaussianSchwartz K) (Profile.finiteTest A)
      (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A) M hM T z
  have hsum : Summable (fun q : Orbits K S₀ =>
      ∑ j ∈ J, p q * orbitEnergy K S₀ D₀ (block K S₀ T j) z q) :=
    summable_sum (fun j hj => hs j)
  have hpoint (q : Orbits K S₀) :
      p q * orbitEnergy K S₀ D₀ T z q ≤ (J.card : ℝ) *
        ∑ j ∈ J, p q * orbitEnergy K S₀ D₀ (block K S₀ T j) z q := by
    calc
      _ ≤ p q * ((J.card : ℝ) * ∑ j ∈ J, orbitEnergy K S₀ D₀ (block K S₀ T j) z q) :=
        mul_le_mul_of_nonneg_left (orbitEnergy_le_blocks K S₀ D₀ T z q) (hp q)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ = ∑' q : Orbits K S₀, p q * orbitEnergy K S₀ D₀ T z q := rfl
    _ ≤ ∑' q : Orbits K S₀, (J.card : ℝ) *
        ∑ j ∈ J, p q * orbitEnergy K S₀ D₀ (block K S₀ T j) z q :=
      ht.tsum_le_tsum hpoint (hsum.mul_left _)
    _ = (J.card : ℝ) * ∑ j ∈ J,
        smoothEnergy K S₀ D₀ (traceGaussianSchwartz K) (Profile.finiteTest A)
          M hM (block K S₀ T j) z := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun j hj => hs j)]
      rfl

end Gaussian
end CubicSieve.GaussianColumnBlocks
