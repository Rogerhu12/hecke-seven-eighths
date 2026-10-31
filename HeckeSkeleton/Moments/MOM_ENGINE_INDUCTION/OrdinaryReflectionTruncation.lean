import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionUniformity

/-!
# A genuine finite ideal truncation of the ordinary reflected series

The reflected series is truncated at the actual norm cutoff Y*R.  The
tail is bounded using the already proved reflected-profile Euler bound
and the proved Dedekind ideal majorant at exponent two.  Constants and
Euler orders are chosen before coefficients, original test, scale and
cutoff.  No estimate for the final moment or for an abstract tail is an
input.  A smooth dyadic window decomposition is a subsequent operation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- All actual nonzero integral ideals below the stated real cutoff. -/
def ordinaryReflectedIdealCutoff (H : ℝ) : Finset (NonzeroIdeal K) :=
  (Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 K) ⌊H⌋₊).toFinset

theorem mem_ordinaryReflectedIdealCutoff {H : ℝ} (hH : 0 ≤ H) (I : NonzeroIdeal K) :
    I ∈ ordinaryReflectedIdealCutoff K H ↔ idealNorm K I ≤ H := by
  simp only [ordinaryReflectedIdealCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact Nat.le_floor_iff hH

/-- The literal finite dual ideal polynomial.  Coefficients may retain an
actual bounded mask; proving a reflected masked identity is separate. -/
def ordinaryReflectedFiniteSum (a : NonzeroIdeal K → ℂ) (β : HeckeCharacter K)
    (V : SmoothAnnularTest) (δ Y R : ℝ) : ℂ :=
  ∑ I ∈ ordinaryReflectedIdealCutoff K (Y * R),
    a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)

/-- An arbitrary tail power is obtained with a finite original test
seminorm.  The common constant has no dependence on a moving ideal row,
its conductor, the positive dual scale, or the truncation ratio. -/
theorem ordinaryReflectedFiniteSum_tail_seminorm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : NonzeroIdeal K → ℂ), (∀ I, ‖a I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Y R : ℝ), 0 < Y → 0 < R →
      ‖(∑' I, a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)) -
        ordinaryReflectedFiniteSum K a β V δ Y R‖ ≤
        C * testSeminorm V.toFun J A * Y ^ 2 * R ^ (1 - A) := by
  obtain ⟨J, C, hC, hdecay⟩ := ordinaryReflectedProfile_decay_seminorm K hcomplex β hδ hδA
  let Z : ℝ := ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun I => Real.rpow_nonneg (idealNorm_pos K I).le _)
  refine ⟨J, C * Z, mul_nonneg hC hZ, ?_⟩
  intro a ha V Y R hY hR
  let S : ℝ := testSeminorm V.toFun J A
  let F := ordinaryReflectedIdealCutoff K (Y * R)
  let f : NonzeroIdeal K → ℂ := fun I => a I * ordinaryReflectedProfile K β V δ (idealNorm K I / Y)
  let tail : NonzeroIdeal K → ℂ := fun I => if I ∉ F then f I else 0
  let D : ℝ := C * S * Y ^ (1 + A) * (Y * R) ^ (1 - A)
  have hS : 0 ≤ S := (Iint_nonneg V 0 (-1 / 4)).trans
    (Iint_left_le V 0 J (Nat.zero_le _) A)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfbound (I : NonzeroIdeal K) :
      ‖f I‖ ≤ (C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(1 + A)) := by
    have hi := hdecay V (idealNorm K I / Y) (div_pos (idealNorm_pos K I) hY)
    calc
      ‖f I‖ = ‖a I‖ * ‖ordinaryReflectedProfile K β V δ (idealNorm K I / Y)‖ := norm_mul _ _
      _ ≤ 1 * (C * S * (idealNorm K I / Y) ^ (-(1 + A))) :=
        mul_le_mul (ha I) hi (norm_nonneg _) (by norm_num)
      _ = _ := by
        rw [one_mul, Real.div_rpow (idealNorm_pos K I).le hY.le,
          Real.rpow_neg hY.le (1 + A), div_inv_eq_mul]
        ring
  have hfn : Summable (fun I : NonzeroIdeal K => ‖f I‖) :=
    Summable.of_nonneg_of_le (fun I => norm_nonneg _) hfbound
      ((summable_nonzeroIdeal_norm_rpow K (σ := 1 + A) (by linarith)).mul_left
        (C * S * Y ^ (1 + A)))
  have hf : Summable f := hfn.of_norm
  have htailbound (I : NonzeroIdeal K) : ‖tail I‖ ≤ D * idealNorm K I ^ (-(2 : ℝ)) := by
    by_cases hI : I ∉ F
    · have hnorm : Y * R ≤ idealNorm K I := by
        apply le_of_lt
        apply lt_of_not_ge
        intro h
        exact hI ((mem_ordinaryReflectedIdealCutoff K (mul_pos hY hR).le I).2 h)
      have hp : idealNorm K I ^ (1 - A) ≤ (Y * R) ^ (1 - A) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hY hR) hnorm (by linarith)
      have he : idealNorm K I ^ (-(1 + A)) =
          idealNorm K I ^ (-(2 : ℝ)) * idealNorm K I ^ (1 - A) := by
        rw [← Real.rpow_add (idealNorm_pos K I)]
        congr 1
        ring
      rw [tail, if_pos hI]
      calc
        _ ≤ (C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(1 + A)) := hfbound I
        _ = ((C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(2 : ℝ))) *
            idealNorm K I ^ (1 - A) := by rw [he]; ring
        _ ≤ ((C * S * Y ^ (1 + A)) * idealNorm K I ^ (-(2 : ℝ))) *
            (Y * R) ^ (1 - A) := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by dsimp [D]; ring
    · rw [tail, if_neg hI, norm_zero]
      exact mul_nonneg hD (Real.rpow_nonneg (idealNorm_pos K I).le _)
  have htn : Summable (fun I : NonzeroIdeal K => ‖tail I‖) :=
    Summable.of_nonneg_of_le (fun I => norm_nonneg _) htailbound
      ((summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)).mul_left D)
  have ht : Summable tail := htn.of_norm
  have hsplit : (∑' I, f I) - (∑' I, tail I) = ∑ I ∈ F, f I := by
    rw [← hf.tsum_sub ht, tsum_eq_sum (s := F)]
    · apply Finset.sum_congr rfl
      intro I hI
      simp only [tail, not_not, hI, not_true_eq_false, if_false, sub_zero]
    · intro I hI
      simp only [tail, hI, if_true, sub_self]
  have heq : (∑' I, f I) - (∑ I ∈ F, f I) = ∑' I, tail I := by
    rw [← hsplit]
    ring
  have htail : ‖∑' I, tail I‖ ≤ D * Z := by
    apply (norm_tsum_le_tsum_norm htn).trans
    calc
      _ ≤ ∑' I, D * idealNorm K I ^ (-(2 : ℝ)) :=
        Summable.tsum_le_tsum htailbound htn
          ((summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)).mul_left D)
      _ = _ := by rw [tsum_mul_left]
  have hpY : Y ^ (1 + A) * Y ^ (1 - A) = Y ^ 2 := by
    rw [← Real.rpow_add hY, show (1 + A) + (1 - A) = (2 : ℝ) by ring, Real.rpow_two]
  change ‖(∑' I, f I) - (∑ I ∈ F, f I)‖ ≤ _
  rw [heq]
  apply htail.trans_eq
  dsimp [D]
  rw [Real.mul_rpow hY.le hR.le]
  calc
    _ = (C * Z) * S * (Y ^ (1 + A) * Y ^ (1 - A)) * R ^ (1 - A) := by ring
    _ = _ := by rw [hpY]

/-- The same cutoff and the same pre-row constants work for the actual
dual coefficients of every finite-order row twist of the fixed background. -/
theorem ordinaryReflectedFiniteSum_finiteRows_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (β : HeckeCharacter K) {δ A : ℝ} (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : HeckeCharacter K, FiniteOrder χ →
      ∀ (V : SmoothAnnularTest) (Y R : ℝ), 0 < Y → 0 < R →
      ‖(∑' I, heckeIdealCoefficient K (β * χ)⁻¹ I *
          ordinaryReflectedProfile K (β * χ) V δ (idealNorm K I / Y)) -
        ordinaryReflectedFiniteSum K (heckeIdealCoefficient K (β * χ)⁻¹) (β * χ) V δ Y R‖ ≤
        C * testSeminorm V.toFun J A * Y ^ 2 * R ^ (1 - A) := by
  obtain ⟨J, C, hC, hbound⟩ :=
    ordinaryReflectedFiniteSum_tail_seminorm K hcomplex β hδ hδA hA
  refine ⟨J, C, hC, ?_⟩
  intro χ hχ V Y R hY hR
  have he : ordinaryReflectedProfile K (β * χ) V δ = ordinaryReflectedProfile K β V δ := by
    funext y
    exact ordinaryReflectedProfile_mul_finiteOrder K hcomplex β χ hχ V δ y
  simpa only [ordinaryReflectedFiniteSum, he] using
    hbound (heckeIdealCoefficient K (β * χ)⁻¹)
      (norm_heckeIdealCoefficient_le_one K (β * χ)⁻¹) V Y R hY hR

end HeckeSkeleton.Moments.EngineInduction
