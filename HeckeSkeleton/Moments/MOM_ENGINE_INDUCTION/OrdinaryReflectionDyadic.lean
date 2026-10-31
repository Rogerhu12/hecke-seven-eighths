import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionTruncation
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionSmooth

/-!
# A genuine finite smooth dyadic truncation of the reflected series

The actual smooth dyadic partition is used at integral-ideal norms.
The finite sum is a sum of actual compact annular tests, without a hard
cutoff hidden inside any child profile.  Its complement is bounded by the
already proved ideal tail estimate after replacing the coefficients by
the actual partition remainder, whose norm is at most one and which
vanishes below the stated threshold.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators

/-- The literal initial part of the proved smooth dyadic partition. -/
def ordinaryDyadicCutoff (J : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range J, fixedDyadicWeight (q / (2 : ℝ) ^ j)

theorem ordinaryDyadicCutoff_bounds (J : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    0 ≤ ordinaryDyadicCutoff J q ∧ ordinaryDyadicCutoff J q ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => fixedDyadicWeight_nonneg _), ?_⟩
  have h := (fixedDyadicWeight_hasSum hq).summable.sum_le_tsum (Finset.range J)
    (fun j _ => fixedDyadicWeight_nonneg (q / (2 : ℝ) ^ j))
  simpa only [ordinaryDyadicCutoff, fixedDyadicWeight_partition hq] using h

/-- The first J+1 windows already form the exact partition at q≤2^J. -/
theorem ordinaryDyadicCutoff_eq_one (J : ℕ) {q : ℝ}
    (hq : 1 ≤ q) (hupper : q ≤ (2 : ℝ) ^ J) :
    ordinaryDyadicCutoff (J + 1) q = 1 := by
  have hzero : ∀ j ∉ Finset.range (J + 1), fixedDyadicWeight (q / (2 : ℝ) ^ j) = 0 := by
    intro j hj
    have hj' : J + 1 ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
    apply fixedDyadicWeight_zero_of_le
    apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) j)).2
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj'
    rw [pow_succ] at hp
    nlinarith
  exact (tsum_eq_sum hzero).symm.trans (fixedDyadicWeight_partition hq)

variable (K : Type) [Field K] [NumberField K]

private theorem summable_ordinaryReflected_norm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ : ℝ} (hδ : 0 < δ)
    (a : NonzeroIdeal K → ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (V : SmoothAnnularTest) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun I : NonzeroIdeal K =>
      ‖a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)‖) := by
  let A : ℝ := δ + 2
  have hδA : δ ≤ A := by dsimp [A]; linarith
  obtain ⟨J, C, hC, hdecay⟩ := ordinaryReflectedProfile_decay_seminorm K hcomplex β hδ hδA
  let S : ℝ := testSeminorm V.toFun J A
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hbound (I : NonzeroIdeal K) :
      ‖a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)‖ ≤
        (C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(1 + A)) := by
    have hi := hdecay V (idealNorm K I / Y) (div_pos (idealNorm_pos K I) hY)
    calc
      _ = ‖a I‖ * ‖ordinaryReflectedProfile K β V δ (idealNorm K I / Y)‖ := norm_mul _ _
      _ ≤ 1 * (C * S * (idealNorm K I / Y) ^ (-(1 + A))) :=
        mul_le_mul (ha I) hi (norm_nonneg _) (by norm_num)
      _ = _ := by
        rw [one_mul, Real.div_rpow (idealNorm_pos K I).le hY.le,
          Real.rpow_neg hY.le (1 + A), div_inv_eq_mul]
        ring
  exact Summable.of_nonneg_of_le (fun I => norm_nonneg _) hbound
    ((summable_nonzeroIdeal_norm_rpow K (σ := 1 + A) (by dsimp [A]; linarith)).mul_left
      (C * S * Y ^ (1 + A)))

/-- A finite sum of genuine compact smooth annular child polynomials. -/
def ordinaryReflectedDyadicSum
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (a : NonzeroIdeal K → ℂ) (β : HeckeCharacter K) (V : SmoothAnnularTest)
    {δ Y : ℝ} (hδ : 0 < δ) (hY : 0 < Y) (J : ℕ) : ℂ :=
  ∑ j ∈ Finset.range J, annularIdealSum K a
    (ordinaryReflectedWindowTest K hcomplex β V hδ
      (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j) hY)) ((2 : ℝ) ^ j)

/-- Calibration of every finite window identifies the sum with the
actual partial partition in the full ideal sum. -/
theorem ordinaryReflectedDyadicSum_eq_tsum
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (a : NonzeroIdeal K → ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (β : HeckeCharacter K) (V : SmoothAnnularTest)
    {δ Y : ℝ} (hδ : 0 < δ) (hY : 0 < Y) (J : ℕ) :
    ordinaryReflectedDyadicSum K hcomplex a β V hδ hY J =
      ∑' I, (a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)) *
        (ordinaryDyadicCutoff J (idealNorm K I) : ℂ) := by
  let f : NonzeroIdeal K → ℂ := fun I =>
    a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)
  have hf := summable_ordinaryReflected_norm K hcomplex β hδ a ha V hY
  have hs (j : ℕ) : Summable (fun I : NonzeroIdeal K =>
      f I * (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun I => norm_nonneg _) (fun I => ?_) hf
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fixedDyadicWeight_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (fixedDyadicWeight_le_one _)
  have he (j : ℕ) : annularIdealSum K a
      (ordinaryReflectedWindowTest K hcomplex β V hδ
        (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j) hY)) ((2 : ℝ) ^ j) =
      ∑' I, f I * (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ) := by
    rw [annularIdealSum_eq_tsum K a _ (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
    apply tsum_congr
    intro I
    change a I * ordinaryReflectedWindow K β V δ
      ((2 : ℝ) ^ j / Y) (idealNorm K I / (2 : ℝ) ^ j) = _
    rw [ordinaryReflectedWindow_calibration K β V δ ((2 : ℝ) ^ j) Y
      (pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0))]
    dsimp [f]
    ring
  unfold ordinaryReflectedDyadicSum
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun j _ => hs j)]
  apply tsum_congr
  intro I
  simp only [ordinaryDyadicCutoff, Complex.ofReal_sum, Finset.mul_sum, f]

/-- A power-saving actual tail after finitely many smooth windows.
All original-test constants precede the coefficients, test and scale. -/
theorem ordinaryReflectedDyadicSum_tail_seminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : NonzeroIdeal K → ℂ), (∀ I, ‖a I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y) (J : ℕ),
      ‖(∑' I, a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)) -
        ordinaryReflectedDyadicSum K hcomplex a β V hδ hY (J + 1)‖ ≤
        C * testSeminorm V.toFun L A * Y ^ 2 * ((2 : ℝ) ^ J / Y) ^ (1 - A) := by
  obtain ⟨L, C, hC, htail⟩ := ordinaryReflectedFiniteSum_tail_seminorm K hcomplex β hδ hδA hA
  refine ⟨L, C, hC, ?_⟩
  intro a ha V Y hY J
  let f : NonzeroIdeal K → ℂ := fun I =>
    a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)
  let a' : NonzeroIdeal K → ℂ := fun I =>
    a I * ((1 - ordinaryDyadicCutoff (J + 1) (idealNorm K I) : ℝ) : ℂ)
  have ha' (I : NonzeroIdeal K) : ‖a' I‖ ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := ordinaryDyadicCutoff_bounds (J + 1) (one_le_idealNorm K I)
    dsimp [a']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact (mul_le_mul (ha I) (show 1 - ordinaryDyadicCutoff (J + 1) (idealNorm K I) ≤ 1 by linarith)
      (by linarith) (by norm_num)).trans_eq (by norm_num)
  have hfn := summable_ordinaryReflected_norm K hcomplex β hδ a ha V hY
  have hf : Summable f := hfn.of_norm
  have hw : Summable (fun I => f I * (ordinaryDyadicCutoff (J + 1) (idealNorm K I) : ℂ)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun I => norm_nonneg _) (fun I => ?_) hfn
    obtain ⟨hlo, hhi⟩ := ordinaryDyadicCutoff_bounds (J + 1) (one_le_idealNorm K I)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlo]
    exact mul_le_of_le_one_right (norm_nonneg _) hhi
  have heq : (∑' I, f I) - ordinaryReflectedDyadicSum K hcomplex a β V hδ hY (J + 1) =
      ∑' I, a' I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y) := by
    rw [ordinaryReflectedDyadicSum_eq_tsum K hcomplex a ha β V hδ hY, ← hf.tsum_sub hw]
    apply tsum_congr
    intro I
    dsimp [f, a']
    push_cast
    ring
  have hscale : Y * ((2 : ℝ) ^ J / Y) = (2 : ℝ) ^ J := by field_simp [hY.ne']
  have hz : ordinaryReflectedFiniteSum K a' β V δ Y ((2 : ℝ) ^ J / Y) = 0 := by
    unfold ordinaryReflectedFiniteSum
    apply Finset.sum_eq_zero
    intro I hI
    have hnorm : idealNorm K I ≤ (2 : ℝ) ^ J := by
      apply (mem_ordinaryReflectedIdealCutoff K
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) J) I).1
      simpa only [hscale] using hI
    have hwone := ordinaryDyadicCutoff_eq_one J (one_le_idealNorm K I) hnorm
    simp only [a', hwone, sub_self, Complex.ofReal_zero, mul_zero, zero_mul]
  have ht := htail a' ha' V Y ((2 : ℝ) ^ J / Y) hY (div_pos (pow_pos (by norm_num) _) hY)
  rw [hz, sub_zero] at ht
  change ‖(∑' I, f I) - ordinaryReflectedDyadicSum K hcomplex a β V hδ hY (J + 1)‖ ≤ _
  rw [heq]
  exact ht

end HeckeSkeleton.Moments.EngineInduction
