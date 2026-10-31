import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDensity
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryRestorationTail
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryDeletionReflection
import HeckeSkeleton.HeckeConductorNorm

/-!
# The actual ordinary row polynomial as finite common-frequency pieces

This assembles the genuine functional equation, the same finite Euler
deletions and restorations, a common finite smooth dyadic truncation, and
the proved absolute Mellin/restoration Fubini theorem.  Its remainder is
exactly the function whose bound was proved in `OrdinaryRestorationTail`.

The left-hand side is the actual deleted Hecke ideal polynomial.  The
right-hand columns retain that same deleted set and its inverse actual
character.  Passing to the original character by conjugation, and then
to actual child energies, is a separate algebraic operation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.HeckeConductorNorm
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The two nonzero-ideal types encode the identical arithmetic series,
for an arbitrary explicit ideal coefficient including all deleted primes. -/
theorem plainPoly_eq_nonzeroSeries (a : Ideal (𝓞 K) → ℂ) (F : ℝ → ℂ) (Y : ℝ) :
    plainPoly a F Y = (Real.sqrt Y : ℂ)⁻¹ *
      ∑' I : NonzeroIdeal K, a I.val * F (idealNorm K I / Y) := by
  unfold plainPoly
  congr 1
  symm
  have h := (nonzeroIdealDeletionEquiv (K := K)).tsum_eq
    (fun I : HeckePort.Moments.NI K => a I.val * F (inorm I / Y))
  change (∑' I : NonzeroIdeal K, a I.val * F (idealNorm K I / Y)) =
    ∑' I : HeckePort.Moments.NI K, a I.val * F (inorm I / Y) at h
  exact h

private theorem cutoff_tsum_eq_finite
    (f : NonzeroIdeal K → ℂ) {N : ℝ} (hN : 0 < N) :
    (∑' I : NonzeroIdeal K, f I * (fixedDyadicWeight (idealNorm K I / N) : ℂ)) =
      ∑ I ∈ ordinaryPowerWindowSupport K N,
        f I * (fixedDyadicWeight (idealNorm K I / N) : ℂ) := by
  apply tsum_eq_sum
  intro I hI
  have hz : fixedDyadicWeight (idealNorm K I / N) = 0 := by
    by_contra hn
    exact hI ((mem_ordinaryPowerWindowSupport K 1 0 N I).2
      ((ordinaryPowerWindow_ne_zero_iff 1 0 _).2 hn))
  rw [hz, Complex.ofReal_zero, mul_zero]

private theorem cutoff_partial_sum
    {f : NonzeroIdeal K → ℂ} (hf : Summable (fun I => ‖f I‖)) (J : ℕ) :
    (∑' I : NonzeroIdeal K, f I * (ordinaryDyadicCutoff (J + 1) (idealNorm K I) : ℂ)) =
      ∑ j ∈ Finset.range (J + 1), ∑ I ∈ ordinaryPowerWindowSupport K ((2 : ℝ) ^ j),
        f I * (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ) := by
  have hs (j : ℕ) : Summable (fun I : NonzeroIdeal K =>
      f I * (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)) := by
    apply Summable.of_norm
    apply hf.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fixedDyadicWeight_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (fixedDyadicWeight_le_one _)
  simp only [ordinaryDyadicCutoff, Complex.ofReal_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j _ => hs j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact cutoff_tsum_eq_finite K f (pow_pos (by norm_num : (0 : ℝ) < 2) j)

/-- The exact original ordinary polynomial, decomposed into finitely many
shared-scale frequency operators and the genuine restoration remainder.
The chosen line for each dyadic label may be either 1/4 or 3/4 (or any
intermediate line).  A later fixed two-label split places a row-dependent
line choice only in the scalar coefficient. -/
theorem deletedHeckePlainPoly_commonFrequency
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (V : SmoothAnnularTest) {δ X Ymax : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) (hX : 0 < X) (hYmax : 0 < Ymax)
    (hscale : ∀ D ∈ S.powerset, ∀ H : SmoothIdeal S,
      heckeConductorScale K χ * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) /
        (X * inorm H.val) ≤ Ymax)
    (J : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ j ∈ Finset.range (J + 1), 1 / 4 ≤ σ j ∧ σ j ≤ 3 / 4) :
    let a := idealCoefficient (primeCoefficient K χ)
    let ai := idealCoefficient (primeCoefficient K χ⁻¹)
    let b : NonzeroIdeal K → ℂ := fun I => excl S ai I.val
    let Q := heckeConductorScale K χ
    ∃ G : ℂ, ‖G‖ = 1 ∧
      plainPoly (excl S a) V.toFun X =
        G * ordinaryRestorationRemainder K a ai S b χ V δ Q X J +
          G * ∑ j ∈ Finset.range (J + 1), ∫ t : ℝ,
            ordinaryReflectionDensity K χ V a ai S Q X ((2 : ℝ) ^ j) (σ j) t *
              ordinaryPowerColumn K b (σ j) ((2 : ℝ) ^ j) t := by
  dsimp only
  let a := idealCoefficient (primeCoefficient K χ)
  let ai := idealCoefficient (primeCoefficient K χ⁻¹)
  let b : NonzeroIdeal K → ℂ := fun I => excl S ai I.val
  let Q := heckeConductorScale K χ
  have ha : IdealCoeff a := heckeIdealCoeff_for_deletion χ
  have hai : IdealCoeff ai := heckeIdealCoeff_for_deletion χ⁻¹
  have hb (I : NonzeroIdeal K) : ‖b I‖ ≤ 1 := by
    by_cases hI : outside S I.val
    · simpa only [b, excl, if_pos hI] using hai.norm_le_one I.val
    · simp only [b, excl, if_neg hI, norm_zero, zero_le_one]
  have hQ : 0 < Q := conductorScale_pos K χ
  let Y (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℝ :=
    Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
  have hY (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      0 < Y D H :=
    div_pos (mul_pos hQ (subset_product_norm_pos D
      (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)))) (mul_pos hX (inorm_pos H.val))
  let W (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
    (Real.sqrt (Y D H) : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
      b I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y D H)
  let P (j : ℕ) (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
    (Real.sqrt (Y D H) : ℂ)⁻¹ * ∑ I ∈ ordinaryPowerWindowSupport K ((2 : ℝ) ^ j),
      b I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y D H) *
        (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)
  let R (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
    ordinaryReflectedRemainder K b χ V δ (Y D H) J
  obtain ⟨L, Cw, hCw, hwhole⟩ := ordinaryReflectedSeries_normalized_bound K hcomplex χ
    hδ (A := δ + 2) (by linarith)
  have hSV : 0 ≤ testSeminorm V.toFun L (δ + 2) :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 L (Nat.zero_le _) (δ + 2))
  let B := Cw * testSeminorm V.toFun L (δ + 2) * Ymax ^ (δ + 2 + 1 / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpieceBound (j : ℕ) (D : Finset (Ideal (𝓞 K)))
      (hD : D ∈ S.powerset) (H : SmoothIdeal S) : ‖P j D H‖ ≤ B := by
    let bj : NonzeroIdeal K → ℂ := fun I =>
      b I * (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)
    have hbj (I : NonzeroIdeal K) : ‖bj I‖ ≤ 1 := by
      rw [bj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fixedDyadicWeight_nonneg _)]
      exact (mul_le_of_le_one_right (norm_nonneg _) (fixedDyadicWeight_le_one _)).trans (hb I)
    have he : P j D H = (Real.sqrt (Y D H) : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
        bj I * ordinaryReflectedProfile K χ V δ (idealNorm K I / Y D H) := by
      dsimp [P]
      congr 1
      rw [← cutoff_tsum_eq_finite K _ (pow_pos (by norm_num : (0 : ℝ) < 2) j)]
      apply tsum_congr
      intro I
      dsimp [bj]
      ring
    rw [he]
    exact ((hwhole bj hbj V (Y D H) (hY D hD H)).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hY D hD H).le (hscale D hD H) (by linarith))
        (mul_nonneg hCw hSV))
  have hsP (j : ℕ) (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Summable (fun H : SmoothIdeal S => coefficient a ai S D H * P j D H) := by
    apply Summable.of_norm
    apply ((coefficient_summable_norm ha hai S hS D (Finset.mem_powerset.mp hD)).mul_right B).
      of_nonneg_of_le (fun _ => norm_nonneg _) (fun H => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hpieceBound j D hD H) (norm_nonneg _)
  obtain ⟨Lt, Ct, hCt, ht⟩ := ordinaryRestorationRemainder_bound K hcomplex χ hδ
    (A := δ + 2) (by linarith) (by linarith) (ε := 1) zero_lt_one
  have hsR (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Summable (fun H : SmoothIdeal S => coefficient a ai S D H * R D H) :=
    ((ht a ai ha hai S hS b hb V Q X Ymax hQ hX hYmax hscale J).1 D hD).of_norm
  have hsplit (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      W D H = R D H + ∑ j ∈ Finset.range (J + 1), P j D H := by
    have hf := (hwhole b hb V (Y D H) (hY D hD H)).1
    dsimp [W, R, ordinaryReflectedRemainder, P]
    rw [cutoff_partial_sum K hf, mul_sub, Finset.mul_sum]
    ring
  have hDsplit (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, coefficient a ai S D H * W D H) =
        (∑' H : SmoothIdeal S, coefficient a ai S D H * R D H) +
          ∑ j ∈ Finset.range (J + 1), ∑' H : SmoothIdeal S,
            coefficient a ai S D H * P j D H := by
    simp_rw [hsplit D hD, mul_add, Finset.mul_sum]
    rw [(hsR D hD).tsum_add (summable_sum (fun j _ => hsP j D hD)),
      Summable.tsum_finsetSum (fun j _ => hsP j D hD)]
  have hsplitAll :
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient a ai S D H * W D H) =
        ordinaryRestorationRemainder K a ai S b χ V δ Q X J +
          ∑ j ∈ Finset.range (J + 1), ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
            coefficient a ai S D H * P j D H := by
    calc
      _ = ∑ D ∈ S.powerset,
          ((∑' H : SmoothIdeal S, coefficient a ai S D H * R D H) +
            ∑ j ∈ Finset.range (J + 1), ∑' H : SmoothIdeal S,
              coefficient a ai S D H * P j D H) :=
        Finset.sum_congr rfl hDsplit
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]; rfl
  have hop (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient a ai S D H * P j D H) =
        ∫ t : ℝ, ordinaryReflectionDensity K χ V a ai S Q X ((2 : ℝ) ^ j) (σ j) t *
          ordinaryPowerColumn K b (σ j) ((2 : ℝ) ^ j) t := by
    have ho := ordinaryRestoredWindow_operator hcomplex χ V ha hai b S hS hδ hQ hX
      (pow_pos (by norm_num : (0 : ℝ) < 2) j) (hσ j hj).1 (hσ j hj).2
    change (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient a ai S D H * P j D H) = _ at ho
    rw [ho, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [ordinaryReflectionDensity]
    ring
  obtain ⟨G, hG, hFE⟩ := deletedHeckePlainPoly_ordinary_reflection K hcomplex χ hχ S hS V hδ hδsmall
  refine ⟨G, hG, ?_⟩
  have hFEx := (hFE X hX).2
  change plainPoly (excl S a) V.toFun X = G * _ at hFEx
  have heFE : (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
      reflectedTerm a ai S (ordinaryReflectedProfile K χ V δ) X Q D H) =
      ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient a ai S D H * W D H := by
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq_coefficient, plainPoly_eq_nonzeroSeries]
  rw [hFEx, heFE, hsplitAll, mul_add]
  congr 1
  congr 1
  exact Finset.sum_congr rfl hop

end HeckeSkeleton.Moments.EngineInduction
