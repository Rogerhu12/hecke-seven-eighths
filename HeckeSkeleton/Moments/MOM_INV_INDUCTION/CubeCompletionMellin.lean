import HeckeSkeleton.Moments.MOM_INV_STEP.MellinSeparation
import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

/-!
# Exact common-profile separation of a reopened cube block

On one cube annulus `H ≤ b ≤ 2H`, write `X = H^3 U`. The original
profile is still `W(b^3 u/X)`. Its genuine logarithmic Fourier inversion
separates the cube phase from a common Schwartz test in `u/U`.
A fixed finite smooth partition then gives tests supported in `[1,2]`.
The profile, Fourier density, and seminorm choices are shared by every
cube and every arithmetic coefficient in the block.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionMellin

open MeasureTheory
open HeckeSkeleton.Moments.MOM_INV_STEP
open CommonKernel MellinSeparation
open scoped Classical BigOperators

/-- On the genuine source support the complete squarefree column lies
inside one fixed wide window; this uses the cube annulus, not a guessed
replacement for the original joint profile. -/
theorem cube_source_window (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (b u H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hu : 0 < u)
    (hb : H ≤ b) (hb2 : b ≤ 2 * H) (hX : X = H ^ 3 * U)
    (hne : W (b ^ 3 * u / X) ≠ 0) :
    1 / 64 ≤ u / U ∧ u / U ≤ 3 := by
  have hq : 0 ≤ u / U := (div_pos hu hU).le
  have hv1 : 1 ≤ b / H := (one_le_div hH).mpr hb
  have hv2 : b / H ≤ 2 := (div_le_iff₀ hH).mpr (by simpa only [mul_comm 2 H] using hb2)
  have hv0 : 0 ≤ b / H := zero_le_one.trans hv1
  have hv3lo : 1 ≤ (b / H) ^ 3 := one_le_pow₀ hv1
  have hv3hi : (b / H) ^ 3 ≤ 8 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num] using pow_le_pow_left₀ hv0 hv2 3
  have heq : b ^ 3 * u / X = (b / H) ^ 3 * (u / U) := by
    rw [hX]
    field_simp [hH.ne', hU.ne'] <;> ring
  have hs := hW (subset_closure (Function.mem_support.mpr hne))
  rw [heq] at hs
  have hlo := mul_le_mul_of_nonneg_right hv3hi hq
  have hhi := mul_le_mul_of_nonneg_right hv3lo hq
  constructor <;> nlinarith [hs.1, hs.2]

theorem cutoff_cube_source (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (b u H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hu : 0 < u)
    (hb : H ≤ b) (hb2 : b ≤ 2 * H) (hX : X = H ^ 3 * U) :
    FinalMellinTests.cutoff (u / U) * W (b ^ 3 * u / X) =
      W (b ^ 3 * u / X) := by
  by_cases hz : W (b ^ 3 * u / X) = 0
  · rw [hz, mul_zero]
  · have hs := cube_source_window W hW b u H U X hH hU hu hb hb2 hX hz
    rw [FinalMellinTests.cutoff_one hs.1 hs.2, one_mul]

theorem column_phase_window (t u U : ℝ) (hu : 0 < u) (hU : 0 < U) :
    columnPhase t (Real.log U) * FinalMellinTests.weightedTest 0 t (u / U) =
      FinalMellinTests.cutoff (u / U) * columnPhase t (Real.log u) := by
  simpa only [Real.rpow_zero, Complex.ofReal_one, one_mul, mul_one] using
    FinalMellinTests.scaled_weighted_phase_all 0 t u U hu hU

/-- A single Fourier density separates all cubes in the block. The
cutoff is inserted only after proving equality for the whole integral,
including points where the original profile vanishes. -/
theorem cube_profile_inverse (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (b u H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hu : 0 < u)
    (hb : H ≤ b) (hb2 : b ≤ 2 * H) (hX : X = H ^ 3 * U) :
    W (b ^ 3 * u / X) =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log (b ^ 3)) *
        columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
          FinalMellinTests.weightedTest 0 t (u / U) := by
  have hb0 : 0 < b := hH.trans_le hb
  have hX0 : 0 < X := by rw [hX]; positivity
  calc
    _ = FinalMellinTests.cutoff (u / U) * W (b ^ 3 * u / X) :=
      (cutoff_cube_source W hW b u H U X hH hU hu hb hb2 hX).symm
    _ = ∫ t : ℝ, FinalMellinTests.cutoff (u / U) *
        (density W hW t * columnPhase t (Real.log (b ^ 3)) *
          columnPhase t (Real.log u) * columnPhase t (-Real.log X)) := by
      rw [source_inverse W hW (b ^ 3) u X (pow_pos hb0 3) hu hX0,
        integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        have hs := column_phase_window t u U hu hU
        calc
          _ = density W hW t * columnPhase t (Real.log (b ^ 3)) *
              columnPhase t (-Real.log X) *
                (FinalMellinTests.cutoff (u / U) * columnPhase t (Real.log u)) := by ring
          _ = _ := by rw [← hs]; ring

theorem cube_profile_integrable (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (b u U X : ℝ) (hu : 0 < u) (hU : 0 < U) :
    Integrable (fun t : ℝ => density W hW t * columnPhase t (Real.log (b ^ 3)) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        FinalMellinTests.weightedTest 0 t (u / U)) := by
  have hi := (integrable_source W hW (b ^ 3) u X).const_mul
    (FinalMellinTests.cutoff (u / U))
  apply hi.congr
  exact Filter.Eventually.of_forall fun t => by
    have hs := column_phase_window t u U hu hU
    calc
      _ = density W hW t * columnPhase t (Real.log (b ^ 3)) *
          columnPhase t (-Real.log X) *
            (FinalMellinTests.cutoff (u / U) * columnPhase t (Real.log u)) := by ring
      _ = _ := by rw [← hs]; ring

/-- Exact separation for a finite original cube-by-column polynomial.
The coefficient may contain all original product-form marks and masks. -/
theorem finite_cube_profile_inverse {β α : Type*} (B : Finset β) (N : Finset α)
    (bNorm : β → ℝ) (nNorm : α → ℝ) (weight : β → α → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hX : X = H ^ 3 * U)
    (hb : ∀ b ∈ B, H ≤ bNorm b ∧ bNorm b ≤ 2 * H)
    (hn : ∀ n ∈ N, 0 < nNorm n) :
    (∑ b ∈ B, ∑ n ∈ N, weight b n * W (bNorm b ^ 3 * nNorm n / X)) =
      ∫ t : ℝ, density W hW t * columnPhase t (-Real.log X) *
        columnPhase t (Real.log U) *
          ∑ b ∈ B, columnPhase t (Real.log (bNorm b ^ 3)) *
            ∑ n ∈ N, weight b n * FinalMellinTests.weightedTest 0 t (nNorm n / U) := by
  let F : β → α → ℝ → ℂ := fun b n t => weight b n *
    (density W hW t * columnPhase t (Real.log (bNorm b ^ 3)) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        FinalMellinTests.weightedTest 0 t (nNorm n / U))
  have hF (b : β) (n : α) (hnN : n ∈ N) : Integrable (F b n) :=
    (cube_profile_integrable W hW (bNorm b) (nNorm n) U X (hn n hnN) hU).const_mul _
  calc
    _ = ∑ b ∈ B, ∑ n ∈ N, ∫ t : ℝ, F b n t := by
      apply Finset.sum_congr rfl
      intro b hbB
      apply Finset.sum_congr rfl
      intro n hnN
      rw [cube_profile_inverse W hW (bNorm b) (nNorm n) H U X
        hH hU (hn n hnN) (hb b hbB).1 (hb b hbB).2 hX, integral_const_mul]
    _ = ∫ t : ℝ, ∑ b ∈ B, ∑ n ∈ N, F b n t := by
      symm
      rw [integral_finsetSum B (fun b _ => integrable_finsetSum N (fun n hnN => hF b n hnN))]
      apply Finset.sum_congr rfl
      intro b _
      exact integral_finsetSum N (fun n hnN => hF b n hnN)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        dsimp only [F]
        ring

def annularTest (t : ℝ) (i : SchwartzTestPartition.Index) : SchwartzMap ℝ ℂ :=
  SchwartzTestPartition.piece (FinalMellinTests.weightedTest 0 t)
    (SchwartzTestPartition.exponent i)

def partitionScaleCap : ℝ := (3 / 2 : ℝ) ^ (18 : ℕ)

theorem partitionScaleCap_one_le : 1 ≤ partitionScaleCap :=
  one_le_pow₀ (by norm_num)

theorem annular_scale_bounds (i : SchwartzTestPartition.Index) :
    partitionScaleCap⁻¹ ≤ SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) ∧
      SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) ≤ partitionScaleCap := by
  have hbounds := SchwartzTestPartition.exponent_bounds i
  constructor
  · have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hbounds.1
    simpa only [SchwartzTestPartition.scale, partitionScaleCap, zpow_neg, zpow_natCast] using h
  · have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)
      (hbounds.2.trans (by norm_num : (5 : ℤ) ≤ 18))
    simpa only [SchwartzTestPartition.scale, partitionScaleCap, zpow_natCast] using h

theorem annular_scale_le_eight (i : SchwartzTestPartition.Index) :
    SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) ≤ 8 := by
  have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)
    (SchwartzTestPartition.exponent_bounds i).2
  exact h.trans (by norm_num)

theorem wideTest_support (t : ℝ) :
    tsupport (FinalMellinTests.weightedTest 0 t) ⊆ Set.Icc (1 / 512 : ℝ) 4 := by
  intro x hx
  have h := FinalMellinTests.weightedTest_support 0 t hx
  constructor <;> linarith [h.1, h.2]

theorem annularTest_support (t : ℝ) (i : SchwartzTestPartition.Index) :
    tsupport (annularTest t i) ⊆ Set.Icc (1 : ℝ) 2 :=
  SchwartzTestPartition.piece_support _ (wideTest_support t) _

theorem wideTest_eq_sum_annular (t u U : ℝ) :
    FinalMellinTests.weightedTest 0 t (u / U) =
      ∑ i : SchwartzTestPartition.Index, annularTest t i
        (u / (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)) :=
  SchwartzTestPartition.reconstruct_scaled _ (wideTest_support t) u U

/-- All annular Mellin pieces have one polynomial finite-seminorm bound,
chosen before the frequency and the arithmetic source. -/
theorem annularTest_seminorm_bound (q : Finset (ℕ × ℕ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (i : SchwartzTestPartition.Index),
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest t i) ≤
        C * (1 + |t|) ^ m := by
  obtain ⟨s, C₀, hC₀, hpiece⟩ := SchwartzTestPartition.exists_finite_seminorm_bound q
  obtain ⟨m, C₁, hC₁, hwide⟩ := FinalMellinTests.finite_seminorm_polynomial_bound 0 s
  refine ⟨m, C₀ * C₁, mul_nonneg hC₀ hC₁, ?_⟩
  intro t i
  exact (hpiece (FinalMellinTests.weightedTest 0 t) i).trans
    ((mul_le_mul_of_nonneg_left (hwide t) hC₀).trans_eq (by ring))

/-- The actual finite cube polynomial is an integral of a fixed finite
sum of complete annular column polynomials. Every piece retains the
same arithmetic coefficient, including its whole-index decorations. -/
theorem finite_cube_profile_annular_inverse {β α : Type*}
    (B : Finset β) (N : Finset α) (bNorm : β → ℝ) (nNorm : α → ℝ)
    (weight : β → α → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (H U X : ℝ) (hH : 0 < H) (hU : 0 < U) (hX : X = H ^ 3 * U)
    (hb : ∀ b ∈ B, H ≤ bNorm b ∧ bNorm b ≤ 2 * H)
    (hn : ∀ n ∈ N, 0 < nNorm n) :
    (∑ b ∈ B, ∑ n ∈ N, weight b n * W (bNorm b ^ 3 * nNorm n / X)) =
      ∫ t : ℝ, density W hW t * columnPhase t (-Real.log X) *
        columnPhase t (Real.log U) *
          ∑ i : SchwartzTestPartition.Index,
            ∑ b ∈ B, columnPhase t (Real.log (bNorm b ^ 3)) *
              ∑ n ∈ N, weight b n * annularTest t i
                (nNorm n /
                  (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)) := by
  rw [finite_cube_profile_inverse B N bNorm nNorm weight W hW H U X hH hU hX hb hn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    congr 1
    simp_rw [wideTest_eq_sum_annular, Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext b
      rw [Finset.sum_comm]
    exact Finset.sum_comm

/-- The common frequency integration costs finitely many seminorms of
the original profile, uniformly over all 24 annular pieces. The first
Mellin mass is exactly the additional factor from integral Cauchy. -/
theorem annularTest_cauchy_budget (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (i : SchwartzTestPartition.Index),
      (∫ t : ℝ, ‖density W hW t‖) *
          (∫ t : ℝ, ‖density W hW t‖ *
            (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest t i)) ^ 2) ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 := by
  obtain ⟨m, B, hB, hb⟩ := annularTest_seminorm_bound q
  obtain ⟨s₀, C₀, hC₀, hmass⟩ := density_moment_bound 0
  obtain ⟨s₁, C₁, hC₁, hmoment⟩ := density_moment_bound (2 * m)
  refine ⟨s₀ ∪ s₁, C₀ * B ^ 2 * C₁, by positivity, ?_⟩
  intro W hW i
  have hm : (∫ t : ℝ, ‖density W hW t‖) ≤
      C₀ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    have hm₀ : (∫ t : ℝ, ‖density W hW t‖) ≤
        C₀ * s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa only [pow_zero, one_mul] using hmass W hW
    exact hm₀.trans (mul_le_mul_of_nonneg_left
      (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W) hC₀)
  have hi := (density_moment_integrable W hW (2 * m)).const_mul (B ^ 2)
  have he : (∫ t : ℝ, ‖density W hW t‖ *
        (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest t i)) ^ 2) ≤
      B ^ 2 * C₁ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    calc
      _ ≤ ∫ t : ℝ, B ^ 2 * ((1 + |t|) ^ (2 * m) * ‖density W hW t‖) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (sq_nonneg _))) hi
        exact Filter.Eventually.of_forall fun t => by
          have hs := pow_le_pow_left₀
            (apply_nonneg (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)) _) (hb t i) 2
          have hmul := mul_le_mul_of_nonneg_left hs (norm_nonneg (density W hW t))
          convert hmul using 1 <;> simp only [mul_pow, ← pow_mul, Nat.mul_comm m 2] <;> ring
      _ = B ^ 2 * (∫ t : ℝ, (1 + |t|) ^ (2 * m) * ‖density W hW t‖) :=
        integral_const_mul _ _
      _ ≤ B ^ 2 * (C₁ * s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
        mul_le_mul_of_nonneg_left (hmoment W hW) (sq_nonneg B)
      _ ≤ B ^ 2 * (C₁ * (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W) hC₁)
          (sq_nonneg B)
      _ = _ := by ring
  have hn : 0 ≤ ∫ t : ℝ, ‖density W hW t‖ *
      (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (annularTest t i)) ^ 2 :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  exact (mul_le_mul hm he hn (by positivity)).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionMellin
