import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDyadic

/-!
# Whole reflected series and normalized finite dyadic tails

The integral-ideal norm is at least one.  Arbitrary decay of the actual
reflected profile therefore bounds the entire normalized dual series
by Y^(A+1/2), including Y below one.  This is the genuine terminal used
when an original zero-slot factor is too long to leave a core child.

The second estimate keeps the same normalization in the genuine smooth
dyadic tail.  Both constants precede all coefficients, original tests,
dual scales and the number of retained windows.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Genuine global decay of the complete normalized reflected series.
Its absolute convergence is part of the conclusion. -/
theorem ordinaryReflectedSeries_normalized_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : NonzeroIdeal K → ℂ), (∀ I, ‖a I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Y : ℝ), 0 < Y →
      Summable (fun I : NonzeroIdeal K =>
        ‖a I * ordinaryReflectedProfile K background V δ (idealNorm K I / Y)‖) ∧
      ‖(Real.sqrt Y : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
        a I * ordinaryReflectedProfile K background V δ (idealNorm K I / Y)‖ ≤
        C * testSeminorm V.toFun L A * Y ^ (A + 1 / 2) := by
  obtain ⟨L, C, hC, hdecay⟩ := ordinaryReflectedProfile_decay_seminorm
    K hcomplex background hδ hδA
  let Z : ℝ := ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(1 + A))
  have hZ : 0 ≤ Z := tsum_nonneg (fun I => Real.rpow_nonneg (idealNorm_pos K I).le _)
  refine ⟨L, C * Z, mul_nonneg hC hZ, ?_⟩
  intro a ha V Y hY
  let S := testSeminorm V.toFun L A
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 L (Nat.zero_le _) A)
  let f : NonzeroIdeal K → ℂ := fun I =>
    a I * ordinaryReflectedProfile K background V δ (idealNorm K I / Y)
  have hpoint (I : NonzeroIdeal K) :
      ‖f I‖ ≤ (C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(1 + A)) := by
    have hi := hdecay V (idealNorm K I / Y) (div_pos (idealNorm_pos K I) hY)
    calc
      _ = ‖a I‖ * ‖ordinaryReflectedProfile K background V δ (idealNorm K I / Y)‖ :=
        norm_mul _ _
      _ ≤ 1 * (C * S * (idealNorm K I / Y) ^ (-(1 + A))) :=
        mul_le_mul (ha I) hi (norm_nonneg _) zero_le_one
      _ = _ := by
        rw [one_mul, Real.div_rpow (idealNorm_pos K I).le hY.le,
          Real.rpow_neg hY.le (1 + A), div_inv_eq_mul]
        ring
  have hmajor := (summable_nonzeroIdeal_norm_rpow K (σ := 1 + A) (by linarith)).mul_left
    (C * S * Y ^ (1 + A))
  have hfn : Summable (fun I => ‖f I‖) :=
    Summable.of_nonneg_of_le (fun I => norm_nonneg _) hpoint hmajor
  refine ⟨hfn, ?_⟩
  have hsum : ‖∑' I, f I‖ ≤ C * S * Y ^ (1 + A) * Z := by
    apply (norm_tsum_le_tsum_norm hfn).trans
    exact (hfn.tsum_le_tsum hpoint hmajor).trans_eq (by rw [tsum_mul_left])
  have hscale : (Real.sqrt Y)⁻¹ * Y ^ (1 + A) = Y ^ (A + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hY.le, ← Real.rpow_add hY]
    congr 1
    ring
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt Y)⁻¹ * (C * S * Y ^ (1 + A) * Z) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (C * Z) * S * ((Real.sqrt Y)⁻¹ * Y ^ (1 + A)) := by ring
    _ = _ := by rw [hscale]

/-- Exact normalization of the smooth dyadic tail.  The power of the
moving dual scale is A+1/2, not the unnormalized A+1 or A+2. -/
theorem ordinaryReflectedDyadic_normalized_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : NonzeroIdeal K → ℂ), (∀ I, ‖a I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y) (J : ℕ),
        ‖(Real.sqrt Y : ℂ)⁻¹ *
          ((∑' I, a I * ordinaryReflectedProfile K background V δ (idealNorm K I / Y)) -
            ordinaryReflectedDyadicSum K hcomplex a background V hδ hY (J + 1))‖ ≤
          C * testSeminorm V.toFun L A * Y ^ (A + 1 / 2) *
            ((2 : ℝ) ^ J) ^ (1 - A) := by
  obtain ⟨L, C, hC, htail⟩ := ordinaryReflectedDyadicSum_tail_seminorm
    K hcomplex background hδ hδA hA
  refine ⟨L, C, hC, ?_⟩
  intro a ha V Y hY J
  have hscale : (Real.sqrt Y)⁻¹ * (Y ^ 2 * ((2 : ℝ) ^ J / Y) ^ (1 - A)) =
      Y ^ (A + 1 / 2) * ((2 : ℝ) ^ J) ^ (1 - A) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hY.le (1 / 2),
      Real.div_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) J) hY.le,
      div_eq_mul_inv (((2 : ℝ) ^ J) ^ (1 - A)) (Y ^ (1 - A)),
      ← Real.rpow_neg hY.le (1 - A), ← Real.rpow_two Y]
    calc
      _ = (Y ^ (-(1 / 2 : ℝ)) * Y ^ (2 : ℝ) * Y ^ (-(1 - A))) *
          ((2 : ℝ) ^ J) ^ (1 - A) := by ring
      _ = _ := by
        rw [← Real.rpow_add hY, ← Real.rpow_add hY]
        congr 2
        ring
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (htail a ha V Y hY J)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
  calc
    _ = (C * testSeminorm V.toFun L A) *
        ((Real.sqrt Y)⁻¹ * (Y ^ 2 * ((2 : ℝ) ^ J / Y) ^ (1 - A))) := by ring
    _ = _ := by rw [hscale]; ring

/-- The same whole-series constant applies before every moving finite
row twist of the fixed background. -/
theorem ordinaryReflectedSeries_finiteRows_normalized_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (row : HeckeCharacter K), FiniteOrder row →
      ∀ (a : NonzeroIdeal K → ℂ), (∀ I, ‖a I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Y : ℝ), 0 < Y →
      ‖(Real.sqrt Y : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
        a I * ordinaryReflectedProfile K (background * row) V δ (idealNorm K I / Y)‖ ≤
        C * testSeminorm V.toFun L A * Y ^ (A + 1 / 2) := by
  obtain ⟨L, C, hC, hbound⟩ := ordinaryReflectedSeries_normalized_bound
    K hcomplex background hδ hδA
  refine ⟨L, C, hC, ?_⟩
  intro row hrow a ha V Y hY
  simp_rw [ordinaryReflectedProfile_mul_finiteOrder K hcomplex background row hrow]
  exact (hbound a ha V Y hY).2

end HeckeSkeleton.Moments.EngineInduction
