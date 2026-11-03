import HeckeGeneral.Analysis.GaussianCutoff
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth assembly of logarithmic Gaussian annuli

Each actual annulus is `g(x) f(x-k)`. Exponentially bounded coefficients are
allowed. The sum is smooth, all derivatives can be summed term by term, and
the derivative tails obey explicit exponential bounds. A partition identity
for translates of the cutoff, when supplied, reconstructs the original
Gaussian; no partition identity is assumed in the convergence results.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open scoped BigOperators ContDiff

def gaussianAnnulusPiece (f : ℝ → ℝ) (k : ℤ) (x : ℝ) : ℝ :=
  cutoffGaussianAnnulus f k (x - k)

theorem gaussianAnnulusPiece_eq (f : ℝ → ℝ) (k : ℤ) (x : ℝ) :
    gaussianAnnulusPiece f k x = realLogGaussian x * f (x - k) := by
  simp [gaussianAnnulusPiece, cutoffGaussianAnnulus]

theorem contDiff_gaussianAnnulusPiece {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℤ) :
    ContDiff ℝ ∞ (gaussianAnnulusPiece f k) := by
  simp only [funext (gaussianAnnulusPiece_eq f k)]
  exact contDiff_realLogGaussian.mul (hf.comp (contDiff_id.sub contDiff_const))

theorem abs_gaussianAnnulusPiece_deriv_le (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (k : ℤ) (x : ℝ) :
    |iteratedDeriv n (gaussianAnnulusPiece f k) x| ≤ cutoffAnnulusMajorant B n C k := by
  unfold gaussianAnnulusPiece
  rw [iteratedDeriv_comp_sub_const]
  exact abs_cutoffGaussianAnnulus_deriv_le f hf B hB hb n C hC hsupp k (x - k)

def gaussianAnnularAssembly (a : ℤ → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℤ, a k * gaussianAnnulusPiece f k x

section Assembly

variable (a : ℤ → ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
  (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j)
  (C A D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
  (hsupp : tsupport f ⊆ Set.Icc (-C) C)
  (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|))

include hf hB hb hC hD hsupp ha

theorem abs_weightedGaussianAnnulus_deriv_le (n : ℕ) (k : ℤ) (x : ℝ) :
    |iteratedDeriv n (fun y => a k * gaussianAnnulusPiece f k y) x| ≤
      D * (Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k) := by
  rw [iteratedDeriv_const_mul_field, abs_mul]
  calc
    _ ≤ (D * Real.exp (A * |(k : ℝ)|)) * cutoffAnnulusMajorant B n C k := by
      apply mul_le_mul (ha k)
        (abs_gaussianAnnulusPiece_deriv_le f hf B hB hb n C hC hsupp k x)
        (abs_nonneg _) (mul_nonneg hD (Real.exp_pos _).le)
    _ = _ := mul_assoc _ _ _

theorem summable_weightedGaussianAnnulus_derivatives (n : ℕ) (x : ℝ) :
    Summable (fun k : ℤ => iteratedDeriv n (fun y => a k * gaussianAnnulusPiece f k y) x) := by
  apply Summable.of_norm_bounded
    ((summable_cutoffAnnulusMajorant B n C A hC).mul_left D)
  intro k
  simpa only [Real.norm_eq_abs] using
    abs_weightedGaussianAnnulus_deriv_le a f hf B hB hb C A D hC hD hsupp ha n k x

theorem contDiff_gaussianAnnularAssembly : ContDiff ℝ ∞ (gaussianAnnularAssembly a f) := by
  apply contDiff_tsum (𝕜 := ℝ) (N := ⊤) (f := fun (k : ℤ) y => a k * gaussianAnnulusPiece f k y)
    (v := fun n (k : ℤ) =>
    D * (Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k))
  · intro k
    exact contDiff_const.mul (contDiff_gaussianAnnulusPiece hf k)
  · intro n _
    exact (summable_cutoffAnnulusMajorant B n C A hC).mul_left D
  · intro n k x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact abs_weightedGaussianAnnulus_deriv_le a f hf B hB hb C A D hC hD hsupp ha n k x

/-- Every derivative is the sum of actual differentiated annulus pieces. -/
theorem iteratedDeriv_gaussianAnnularAssembly (n : ℕ) (x : ℝ) :
    iteratedDeriv n (gaussianAnnularAssembly a f) x =
      ∑' k : ℤ, iteratedDeriv n (fun y => a k * gaussianAnnulusPiece f k y) x := by
  have h := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := ⊤)
    (f := fun k y => a k * gaussianAnnulusPiece f k y)
    (v := fun n k => D * (Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k))
    (fun k => contDiff_const.mul (contDiff_gaussianAnnulusPiece hf k))
    (fun n _ => (summable_cutoffAnnulusMajorant B n C A hC).mul_left D)
    (fun n k y _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact abs_weightedGaussianAnnulus_deriv_le a f hf B hB hb C A D hC hD hsupp ha n k y)
    (k := n) (by simp) x
  rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
  change (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm
    (iteratedFDeriv ℝ n (fun y => ∑' k : ℤ, a k * gaussianAnnulusPiece f k y) x) = _
  rw [h]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm.toContinuousLinearEquiv.map_tsum

theorem abs_iteratedDeriv_gaussianAnnularAssembly_le (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (gaussianAnnularAssembly a f) x| ≤
      D * ∑' k : ℤ, Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k := by
  rw [iteratedDeriv_gaussianAnnularAssembly a f hf B hB hb C A D hC hD hsupp ha]
  have hmajor := (summable_cutoffAnnulusMajorant B n C A hC).mul_left D
  have hbound (k : ℤ) :
      ‖iteratedDeriv n (fun y => a k * gaussianAnnulusPiece f k y) x‖ ≤
        D * (Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k) := by
    simpa only [Real.norm_eq_abs] using
      abs_weightedGaussianAnnulus_deriv_le a f hf B hB hb C A D hC hD hsupp ha n k x
  have hnorm := hmajor.of_nonneg_of_le (fun k => norm_nonneg _) hbound
  calc
    _ ≤ ∑' k : ℤ, ‖iteratedDeriv n (fun y => a k * gaussianAnnulusPiece f k y) x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℤ, D * (Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k) :=
      hnorm.tsum_le_tsum hbound hmajor
    _ = _ := tsum_mul_left

end Assembly

def gaussianTailCoefficients (a : ℤ → ℝ) (T : ℝ) (k : ℤ) : ℝ :=
  if T < |(k : ℝ)| then a k else 0

/-- Moving the tail threshold trades a larger fixed exponential weight for an explicit loss. -/
theorem gaussianTailCoefficients_bound (a : ℤ → ℝ) (A D T r : ℝ) (hD : 0 ≤ D)
    (hr : 0 ≤ r) (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|)) (k : ℤ) :
    |gaussianTailCoefficients a T k| ≤
      (D * Real.exp (-r * T)) * Real.exp ((A + r) * |(k : ℝ)|) := by
  unfold gaussianTailCoefficients
  split_ifs with hk
  · apply (ha k).trans
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [abs_zero]
    positivity

/-- The infinite tail remains smooth; its entire derivative, not just its terms, is bounded. -/
theorem gaussianAnnularAssembly_tail_derivative_bound (a : ℤ → ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j) (C A D T r : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|)) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (gaussianAnnularAssembly (gaussianTailCoefficients a T) f) x| ≤
      (D * Real.exp (-r * T)) *
        ∑' k : ℤ, Real.exp ((A + r) * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k := by
  exact abs_iteratedDeriv_gaussianAnnularAssembly_le _ f hf B hB hb C (A + r)
    (D * Real.exp (-r * T)) hC (mul_nonneg hD (Real.exp_pos _).le) hsupp
    (gaussianTailCoefficients_bound a A D T r hD hr ha) n x

/-- Choosing `r` before the height yields an arbitrarily prescribed power saving. -/
theorem gaussianAnnularAssembly_logarithmic_tail_bound (a : ℤ → ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j) (C A D C₀ b M κ Z : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb₀ : 0 ≤ b) (hM : 0 ≤ M)
    (hκ : 0 < κ) (hZ : 0 < Z) (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|)) (n : ℕ) (x : ℝ) :
    Z ^ b * |iteratedDeriv n
      (gaussianAnnularAssembly (gaussianTailCoefficients a (κ * Real.log Z - C₀)) f) x| ≤
      (D * Real.exp (((b + M) / κ) * C₀) *
        ∑' k : ℤ, Real.exp ((A + (b + M) / κ) * |(k : ℝ)|) *
          cutoffAnnulusMajorant B n C k) * Z ^ (-M) := by
  let r := (b + M) / κ
  have hr : 0 ≤ r := div_nonneg (add_nonneg hb₀ hM) hκ.le
  have ht := gaussianAnnularAssembly_tail_derivative_bound a f hf B hB hb C A D
    (κ * Real.log Z - C₀) r hC hD hr hsupp ha n x
  have he : Z ^ b * Real.exp (-r * (κ * Real.log Z - C₀)) =
      Real.exp (r * C₀) * Z ^ (-M) := by
    rw [Real.rpow_def_of_pos hZ, Real.rpow_def_of_pos hZ, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [r]
    field_simp
    ring
  apply (mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hZ b).le).trans_eq
  calc
    _ = D * (Z ^ b * Real.exp (-r * (κ * Real.log Z - C₀))) *
        ∑' k : ℤ, Real.exp ((A + r) * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k := by ring
    _ = _ := by rw [he]; ring

/-- Smoothness of the cutoff supplies its derivative constants automatically. -/
theorem contDiff_gaussianAnnularAssembly_of_compact {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (a : ℤ → ℝ) (C A D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (ha : ∀ k : ℤ, |a k| ≤ D * Real.exp (A * |(k : ℝ)|)) :
    ContDiff ℝ ∞ (gaussianAnnularAssembly a f) := by
  obtain ⟨B, hB, hb⟩ := exists_compact_derivative_bounds hf hc
  exact contDiff_gaussianAnnularAssembly a f hf B hB hb C A D hC hD hsupp ha

/-- This is the exact assembly identity if translates of the cutoff form a partition. -/
theorem gaussianAnnularAssembly_partition (f : ℝ → ℝ)
    (hpartition : ∀ x : ℝ, ∑' k : ℤ, f (x - k) = 1) :
    gaussianAnnularAssembly (fun _ => 1) f = realLogGaussian := by
  funext x
  simp only [gaussianAnnularAssembly, one_mul, gaussianAnnulusPiece_eq]
  rw [tsum_mul_left, hpartition, mul_one]

end HeckeGeneral.Analysis
