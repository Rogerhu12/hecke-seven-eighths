import HeckeGeneral.Analysis.GaussianAnnularAssembly

/-!
# Finite compact truncations of the Gaussian annular assembly

The finite sum over `-N ≤ k ≤ N` has actual compact support. Its difference
from the full assembly is exactly the smooth infinite tail whose derivatives
were estimated earlier. This transfers those estimates to finite approximants.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped BigOperators ContDiff

def gaussianAnnularTruncation (a : ℤ → ℝ) (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) N, a k * gaussianAnnulusPiece f k x

theorem mem_gaussianAnnularRange (N : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (-(N : ℤ)) N ↔ |(k : ℝ)| ≤ N := by
  rw [Finset.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> norm_cast at *

theorem contDiff_gaussianAnnularTruncation (a : ℤ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) : ContDiff ℝ ∞ (gaussianAnnularTruncation a f N) := by
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (contDiff_gaussianAnnulusPiece hf k)

theorem gaussianAnnularTruncation_zero_outside (a : ℤ → ℝ) (f : ℝ → ℝ)
    (C : ℝ) (hsupp : tsupport f ⊆ Set.Icc (-C) C) (N : ℕ) (x : ℝ)
    (hx : (N : ℝ) + C < |x|) : gaussianAnnularTruncation a f N x = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [gaussianAnnulusPiece_eq]
  have hk' := (mem_gaussianAnnularRange N k).mp hk
  have hxk : C < |x - k| := by
    have h := abs_add_le (x - k) (k : ℝ)
    simp only [sub_add_cancel] at h
    linarith
  have hf : f (x - k) = 0 := by
    apply Function.notMem_support.mp
    intro h
    have hb := hsupp (subset_tsupport f h)
    exact (not_lt_of_ge (abs_le.mpr hb)) hxk
  rw [hf, mul_zero, mul_zero]

theorem tsupport_gaussianAnnularTruncation (a : ℤ → ℝ) (f : ℝ → ℝ)
    (C : ℝ) (hsupp : tsupport f ⊆ Set.Icc (-C) C) (N : ℕ) :
    tsupport (gaussianAnnularTruncation a f N) ⊆ Set.Icc (-(N : ℝ) - C) (N + C) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hb : |x| ≤ (N : ℝ) + C := by
    by_contra h
    exact hx (gaussianAnnularTruncation_zero_outside a f C hsupp N x (lt_of_not_ge h))
  have hp := abs_le.mp hb
  constructor <;> linarith

theorem hasCompactSupport_gaussianAnnularTruncation (a : ℤ → ℝ) (f : ℝ → ℝ)
    (C : ℝ) (hsupp : tsupport f ⊆ Set.Icc (-C) C) (N : ℕ) :
    HasCompactSupport (gaussianAnnularTruncation a f N) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_gaussianAnnularTruncation a f C hsupp N)

section Approximation

variable (a : ℤ → ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
  (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j)
  (C A D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
  (hsupp : tsupport f ⊆ Set.Icc (-C) C)
  (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|))

include hf hB hb hC hD hsupp ha

/-- Exact finite/infinite splitting with absolute convergence already proved. -/
theorem gaussianAnnularAssembly_sub_tail (N : ℕ) (x : ℝ) :
    gaussianAnnularAssembly a f x -
      gaussianAnnularAssembly (gaussianTailCoefficients a N) f x =
        gaussianAnnularTruncation a f N x := by
  have hs : Summable (fun k => a k * gaussianAnnulusPiece f k x) := by
    simpa using summable_weightedGaussianAnnulus_derivatives
      a f hf B hB hb C A D hC hD hsupp ha 0 x
  have ht : Summable (fun k => gaussianTailCoefficients a N k * gaussianAnnulusPiece f k x) := by
    simpa using summable_weightedGaussianAnnulus_derivatives
      (gaussianTailCoefficients a N) f hf B hB hb C A D hC hD hsupp
      (by simpa using gaussianTailCoefficients_bound a A D N 0 hD (le_refl _) ha) 0 x
  unfold gaussianAnnularAssembly gaussianAnnularTruncation
  rw [← hs.tsum_sub ht, tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [gaussianTailCoefficients, not_lt.mpr ((mem_gaussianAnnularRange N k).mp hk)]
  · intro k hk
    have hk' : (N : ℝ) < |(k : ℝ)| := lt_of_not_ge fun h => hk ((mem_gaussianAnnularRange N k).mpr h)
    simp [gaussianTailCoefficients, hk']

theorem gaussianAnnularAssembly_sub_truncation (N : ℕ) :
    (fun x => gaussianAnnularAssembly a f x - gaussianAnnularTruncation a f N x) =
      gaussianAnnularAssembly (gaussianTailCoefficients a N) f := by
  funext x
  have he := gaussianAnnularAssembly_sub_tail a f hf B hB hb C A D hC hD hsupp ha N x
  linarith

/-- Uniform error in every derivative between the assembly and its actual compact approximant. -/
theorem gaussianAnnularTruncation_derivative_error (N n : ℕ) (x r : ℝ) (hr : 0 ≤ r) :
    |iteratedDeriv n (gaussianAnnularAssembly a f) x -
      iteratedDeriv n (gaussianAnnularTruncation a f N) x| ≤
      (D * Real.exp (-r * N)) *
        ∑' k : ℤ, Real.exp ((A + r) * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k := by
  have hs := contDiff_gaussianAnnularAssembly a f hf B hB hb C A D hC hD hsupp ha
  have ht := contDiff_gaussianAnnularTruncation a hf N
  rw [← iteratedDeriv_fun_sub (hs.of_le (by simp)).contDiffAt (ht.of_le (by simp)).contDiffAt]
  rw [gaussianAnnularAssembly_sub_truncation a f hf B hB hb C A D hC hD hsupp ha]
  exact gaussianAnnularAssembly_tail_derivative_bound a f hf B hB hb C A D N r
    hC hD hr hsupp ha n x

/-- Each derivative of the actual compact approximants converges uniformly on the whole line. -/
theorem tendstoUniformly_gaussianAnnularTruncation_deriv (n : ℕ) :
    TendstoUniformly (fun N : ℕ => iteratedDeriv n (gaussianAnnularTruncation a f N))
      (iteratedDeriv n (gaussianAnnularAssembly a f)) Filter.atTop := by
  let Q : ℝ := ∑' k : ℤ, Real.exp ((A + 1) * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k
  have he : Filter.Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlimit : Filter.Tendsto (fun N : ℕ => (D * Real.exp (-(N : ℝ))) * Q)
      Filter.atTop (nhds 0) := by
    simpa using (he.const_mul D).mul_const Q
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hev := hlimit.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with N hN
  intro x
  have hbnd := gaussianAnnularTruncation_derivative_error
    a f hf B hB hb C A D hC hD hsupp ha N n x 1 (by norm_num)
  rw [Real.dist_eq]
  apply lt_of_le_of_lt _ hN
  simpa [Q] using hbnd

/-- A single finite truncation approximates any prescribed finite list of derivative orders. -/
theorem eventually_gaussianAnnularTruncation_all_derivatives (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ n ≤ m, ∀ x : ℝ,
      |iteratedDeriv n (gaussianAnnularAssembly a f) x -
        iteratedDeriv n (gaussianAnnularTruncation a f N) x| < ε := by
  have h (n : ℕ) := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_gaussianAnnularTruncation_deriv
      a f hf B hB hb C A D hC hD hsupp ha n)) ε hε
  have hfin := (Filter.eventually_all_finset (Finset.range (m + 1))).mpr (fun n _ => h n)
  filter_upwards [hfin] with N hN
  intro n hn x
  simpa only [Real.dist_eq] using hN n (Finset.mem_range.mpr (by omega)) x

/-- The approximation is by genuine smooth compactly supported functions. -/
theorem exists_compact_gaussianAnnular_approximation (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      ∀ n ≤ m, ∀ x : ℝ, |iteratedDeriv n (gaussianAnnularAssembly a f) x -
        iteratedDeriv n p x| < ε := by
  obtain ⟨N, hN⟩ := (eventually_gaussianAnnularTruncation_all_derivatives
    a f hf B hB hb C A D hC hD hsupp ha m hε).exists
  exact ⟨gaussianAnnularTruncation a f N, contDiff_gaussianAnnularTruncation a hf N,
    hasCompactSupport_gaussianAnnularTruncation a f C hsupp N, hN⟩

end Approximation

/-- With an actual cutoff partition, the compact approximants converge to the original Gaussian.
The partition existence is an explicit remaining input, not an analytic estimate. -/
theorem exists_compact_realLogGaussian_approximation_of_partition (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (hpartition : ∀ x : ℝ, ∑' k : ℤ, f (x - k) = 1) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      ∀ n ≤ m, ∀ x : ℝ, |iteratedDeriv n realLogGaussian x - iteratedDeriv n p x| < ε := by
  obtain ⟨B, hB, hb⟩ := exists_compact_derivative_bounds hf hc
  have ha : ∀ k : ℤ, |(1 : ℝ)| ≤ 1 * Real.exp (0 * |(k : ℝ)|) := by
    intro k
    simp
  have h := exists_compact_gaussianAnnular_approximation
    (fun _ => 1) f hf B hB hb C 0 1 hC zero_le_one hsupp ha m hε
  rw [gaussianAnnularAssembly_partition f hpartition] at h
  exact h

end HeckeGeneral.Analysis
