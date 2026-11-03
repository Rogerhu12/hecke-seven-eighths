import CubicSieve.AnalyticExtraction
import CubicSieve.AnalyticDyadic
import CubicSieve.AnalyticOptimization

/-!
Growth of unrestricted actual ideal rows from the squarefree cubic sieve norm.
The hypothesis is the current bootstrap exponent, not a Poisson/improvement
estimate. The proof extracts cubes, counts their ideals, and optimizes both
squarefree orientations before absorbing the two dyadic logarithms.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGrowth

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticFactorization
open CubicSieve.AnalyticExtraction CubicSieve.AnalyticDyadic
open DedekindZetaZeroFree.LargeSieve.Vendor
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem swapped_bound (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ExteriorSieve.B K S D M N ≤
        C * (M * N) ^ ε * (M ^ ξ + N + (M * N) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  rw [ExteriorSieve.B_reciprocity K S D hD]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

theorem doubled_bound (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
      ExteriorSieve.B K S D (2 * X) N ≤
        C * (X * N) ^ ε * (X ^ ξ + N + (X * N) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := swapped_bound K S D hD h ε hε
  let A : ℝ := 1 + (2 : ℝ) ^ ξ + (2 : ℝ) ^ (2 / 3 : ℝ)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨C * (2 : ℝ) ^ ε * A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2 / 3 : ℝ)
  have hshape : (2 * X) ^ ξ + N + ((2 * X) * N) ^ (2 / 3 : ℝ) ≤
      A * (X ^ ξ + N + (X * N) ^ (2 / 3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2 * X) * N = 2 * (X * N) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 / 3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 / 3 : ℝ)) hxξ]
  calc
    _ ≤ C * ((2 * X) * N) ^ ε * ((2 * X) ^ ξ + N + ((2 * X) * N) ^ (2 / 3 : ℝ)) :=
      hb (2 * X) N (by linarith) hN
    _ ≤ C * ((2 * X) * N) ^ ε * (A * (X ^ ξ + N + (X * N) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2 * X) * N = 2 * (X * N) by ring,
        Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

/-- An actual dyadic extraction block has the two-power growth forced by the current exponent. -/
theorem block_growth (hD : AllowedGeneratorInput K S D) (C A ξ ε M N : ℝ)
    (hC : 0 < C) (hA : 0 < A) (hξ : (4 / 3 : ℝ) ≤ ξ) (hε : 0 ≤ ε)
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hcost : ∀ (R T : Finset (ExteriorIdeal K S)) (X Y H N : ℝ),
      1 ≤ X → 1 ≤ Y → 1 ≤ H →
      (∀ I ∈ R, exteriorNorm K S (exteriorFirst K S I) ≤ X) →
      (∀ I ∈ R, exteriorNorm K S (exteriorSecond K S I) ≤ Y) →
      (∀ I ∈ R, exteriorNorm K S (exteriorCube K S I) ≤ H) →
      (∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N) →
      ∀ z : ExteriorIdeal K S → ℂ,
        energy K S D 2 R T z ≤ C * H *
          min (Y * ExteriorSieve.B K S D X N) (X * ExteriorSieve.B K S D Y N) *
            ∑ j ∈ T, ‖z j‖ ^ 2)
    (hB : ∀ U : ℝ, 1 ≤ U → U ≤ M →
      ExteriorSieve.B K S D (2 * U) N ≤
        A * (M * N) ^ ε * (U ^ ξ + N + (U * N) ^ (2 / 3 : ℝ)))
    (R T : Finset (ExteriorIdeal K S))
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ M)
    (hT : ∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N)
    (z : ExteriorIdeal K S → ℂ) (i j : ℕ) :
    energy K S D 2 (block K S R i j) T z ≤
      4 * C * A * (M * N) ^ ε * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) *
        ∑ k ∈ T, ‖z k‖ ^ 2 := by
  by_cases hempty : block K S R i j = ∅
  · simp only [hempty, energy, Finset.sum_empty]
    positivity
  obtain ⟨I₀, hI₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let X : ℝ := (2 : ℝ) ^ i
  let Y : ℝ := (2 : ℝ) ^ j
  let H : ℝ := (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)
  have hX : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hY : 1 ≤ Y := one_le_pow₀ (by norm_num)
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have h₀ := block_bounds K S R i j I₀ hI₀
  have hI₀R := (Finset.mem_filter.mp hI₀).1
  have hXM : X ≤ M := h₀.1.trans ((first_norm_le K S I₀).trans (hR I₀ hI₀R))
  have hYM : Y ≤ M := h₀.2.2.1.trans ((second_norm_le K S I₀).trans (hR I₀ hI₀R))
  have hA1 := one_le_norm K S (exteriorFirst K S I₀)
  have hB1 := one_le_norm K S (exteriorSecond K S I₀)
  have hXY : X * Y ^ 2 ≤ M := by
    have hAB := mul_le_mul h₀.1 (pow_le_pow_left₀ hY0.le h₀.2.2.1 2)
      (sq_nonneg _) (by positivity)
    have hC3 := one_le_pow₀ (one_le_norm K S (exteriorCube K S I₀)) (n := 3)
    have hABnonneg : 0 ≤ exteriorNorm K S (exteriorFirst K S I₀) *
        exteriorNorm K S (exteriorSecond K S I₀) ^ 2 := by positivity
    exact hAB.trans ((le_mul_of_one_le_right hABnonneg hC3).trans
      ((exterior_norm_factorization K S I₀).symm.le.trans (hR I₀ hI₀R)))
  have hH : 1 ≤ H := Real.one_le_rpow
    ((one_le_div (mul_pos hX0 (sq_pos_of_pos hY0))).mpr hXY) (by norm_num)
  have hblock := hcost (block K S R i j) T (2 * X) (2 * Y) H N
    (by linarith) (by linarith) hH
    (fun I hI => (block_bounds K S R i j I hI).2.1)
    (fun I hI => (block_bounds K S R i j I hI).2.2.2)
    (fun I hI => cube_norm_le K S I M X Y hX0 hY0
      (block_bounds K S R i j I hI).1 (block_bounds K S R i j I hI).2.2.1
      (hR I (Finset.mem_filter.mp hI).1)) hT z
  let B0 : ℝ := A * (M * N) ^ ε
  have hB0 : 0 ≤ B0 := by dsimp only [B0]; positivity
  have hmin : min (Y * ExteriorSieve.B K S D (2 * X) N)
      (X * ExteriorSieve.B K S D (2 * Y) N) ≤
      B0 * min (Y * (X ^ ξ + N + (X * N) ^ (2 / 3 : ℝ)))
        (X * (Y ^ ξ + N + (Y * N) ^ (2 / 3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB0]
    apply min_le_min
    · convert mul_le_mul_of_nonneg_left (hB X hX hXM) hY0.le using 1 <;> dsimp only [B0] <;> ring
    · convert mul_le_mul_of_nonneg_left (hB Y hY hYM) hX0.le using 1 <;> dsimp only [B0] <;> ring
  have hopt := AnalyticOptimization.extraction_min_two_power M N X Y ξ hM
    (by linarith) hX hY hXY hξ
  have hE : 0 ≤ ∑ k ∈ T, ‖z k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hH0 : 0 ≤ H := by linarith
  have hmin2 : min ((2 * Y) * ExteriorSieve.B K S D (2 * X) N)
      ((2 * X) * ExteriorSieve.B K S D (2 * Y) N) =
      2 * min (Y * ExteriorSieve.B K S D (2 * X) N)
        (X * ExteriorSieve.B K S D (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hmin2] at hblock
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ C * H * 2 by positivity)) hE
  have ho := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ 2 * C * B0 by positivity)) hE
  let V : ℝ := min (Y * (X ^ ξ + N + (X * N) ^ (2 / 3 : ℝ)))
    (X * (Y ^ ξ + N + (Y * N) ^ (2 / 3 : ℝ)))
  let W : ℝ := min (Y * ExteriorSieve.B K S D (2 * X) N)
    (X * ExteriorSieve.B K S D (2 * Y) N)
  have hs₁ : C * H * (2 * W) * (∑ k ∈ T, ‖z k‖ ^ 2) ≤
      C * H * 2 * (B0 * V) * (∑ k ∈ T, ‖z k‖ ^ 2) := by
    convert he using 1 <;> dsimp only [V, W] <;> ring
  have hs₂ : C * H * 2 * (B0 * V) * (∑ k ∈ T, ‖z k‖ ^ 2) ≤
      4 * C * A * (M * N) ^ ε * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) *
        (∑ k ∈ T, ‖z k‖ ^ 2) := by
    convert ho using 1 <;> dsimp only [V, H, B0] <;> ring
  exact hblock.trans (hs₁.trans hs₂)

/-- The true current sieve exponent controls all exterior ideal rows, including cubes. -/
theorem full_ideal_growth (hD : AllowedGeneratorInput K S D) {ξ : ℝ}
    (h : Bootstrap.HasCubicExponent (ExteriorSieve.B K S D) ξ)
    (hξ : (4 / 3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ R T : Finset (ExteriorIdeal K S),
      (∀ I ∈ R, exteriorNorm K S I ≤ M) →
      (∀ j ∈ T, Squarefree j.val.val ∧ exteriorNorm K S j ≤ N) →
      ∀ z : ExteriorIdeal K S → ℂ,
        energy K S D 2 R T z ≤
          C * (M * N) ^ ε * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) * ∑ j ∈ T, ‖z j‖ ^ 2 := by
  obtain ⟨C0, hC0, hcost⟩ := exists_fixed_extraction_block_bound K S D hD
  obtain ⟨A, hA, hb⟩ := doubled_bound K S D hD h (ε / 2) (by positivity)
  let L : ℝ := 2 + 1 / ((ε / 4) * Real.log 2)
  have hL : 0 < L := dyadicLength_small_power_constant_pos (by positivity : 0 < ε / 4)
  refine ⟨4 * C0 * A * L ^ 2, by positivity, ?_⟩
  intro M N hM hN R T hR hT z
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hB : ∀ U : ℝ, 1 ≤ U → U ≤ M →
      ExteriorSieve.B K S D (2 * U) N ≤
        A * (M * N) ^ (ε / 2) * (U ^ ξ + N + (U * N) ^ (2 / 3 : ℝ)) := by
    intro U hU hUM
    apply (hb U N hU hN).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hUM hN0.le)
        (by positivity)) hA.le
  have hsum := Finset.sum_le_sum (s := Finset.range (dyadicLength M + 1))
    (fun i _ => Finset.sum_le_sum (s := Finset.range (dyadicLength M + 1))
      (fun j _ => block_growth K S D hD C0 A ξ (ε / 2) M N hC0 hA hξ
        (by positivity) hM hN hcost hB R T hR hT z i j))
  rw [energy_partition K S D R T M hR z] at hsum
  have hlog := dyadicLength_small_power (X := M) (by positivity : 0 < ε / 4) hM
  have hLP : (dyadicLength M + 1 : ℝ) ^ 2 ≤ L ^ 2 * M ^ (ε / 2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε / 4) * (2 : ℕ) = ε / 2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M ^ (ε / 2) ≤ (M * N) ^ (ε / 2) :=
    Real.rpow_le_rpow hM0.le (by nlinarith) (by positivity)
  have hprod : (dyadicLength M + 1 : ℝ) ^ 2 * (M * N) ^ (ε / 2) ≤
      L ^ 2 * (M * N) ^ ε := by
    calc
      _ ≤ (L ^ 2 * M ^ (ε / 2)) * (M * N) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hLP (by positivity)
      _ ≤ (L ^ 2 * (M * N) ^ (ε / 2)) * (M * N) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _)) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]; congr 2; ring
  have hE : 0 ≤ ∑ j ∈ T, ‖z j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ ≤ (dyadicLength M + 1 : ℝ) ^ 2 *
        (4 * C0 * A * (M * N) ^ (ε / 2) * (M ^ (1 / 3 : ℝ) * N + M ^ ξ) *
          ∑ j ∈ T, ‖z j‖ ^ 2) := by
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, pow_two, mul_assoc] using hsum
    _ = (4 * C0 * A) * ((dyadicLength M + 1 : ℝ) ^ 2 * (M * N) ^ (ε / 2)) *
        (M ^ (1 / 3 : ℝ) * N + M ^ ξ) * ∑ j ∈ T, ‖z j‖ ^ 2 := by ring
    _ ≤ (4 * C0 * A) * (L ^ 2 * (M * N) ^ ε) *
        (M ^ (1 / 3 : ℝ) * N + M ^ ξ) * ∑ j ∈ T, ‖z j‖ ^ 2 := by
      gcongr
    _ = _ := by ring

end CubicSieve.AnalyticGrowth
