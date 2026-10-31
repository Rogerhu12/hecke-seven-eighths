import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionWhole
import HeckePort.Moments.ReflectionMass

/-!
# The actual restoration tails at a common finite dyadic cutoff

The tail is the literal complement of the fixed smooth partition in the
complete reflected ideal series.  Its norm is bounded before the
restoration sum is taken.  The genuine Euler coefficient mass then gives
absolute convergence and the required common subpower loss.

The only scale hypothesis is a bound on the actual physical dual scales
Q N(D)/(X N(H)).  It is the arithmetic conductor/deletion calibration,
not any energy or moment bound.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Literal normalized remainder after the first J+1 smooth windows. -/
def ordinaryReflectedRemainder (b : NonzeroIdeal K → ℂ)
    (background : HeckeCharacter K) (V : SmoothAnnularTest) (δ Y : ℝ) (J : ℕ) : ℂ :=
  (Real.sqrt Y : ℂ)⁻¹ *
    ((∑' I : NonzeroIdeal K, b I *
        ordinaryReflectedProfile K background V δ (idealNorm K I / Y)) -
      ∑' I : NonzeroIdeal K,
        (b I * ordinaryReflectedProfile K background V δ (idealNorm K I / Y)) *
          (ordinaryDyadicCutoff (J + 1) (idealNorm K I) : ℂ))

/-- The original finite-deletion/infinite-restoration tail, with its
actual coefficients and each actual reflected physical scale retained. -/
def ordinaryRestorationRemainder (a ai : Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K))) (b : NonzeroIdeal K → ℂ)
    (background : HeckeCharacter K) (V : SmoothAnnularTest)
    (δ Q X : ℝ) (J : ℕ) : ℂ :=
  ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
    coefficient a ai S D H * ordinaryReflectedRemainder K b background V δ
      (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) J

private theorem coefficient_sum_bound
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (F : Finset (Ideal (𝓞 K)) → SmoothIdeal S → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ D ∈ S.powerset, ∀ H, ‖F D H‖ ≤ B) :
    (∀ D ∈ S.powerset, Summable (fun H : SmoothIdeal S =>
      ‖coefficient a ai S D H * F D H‖)) ∧
    ‖∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient a ai S D H * F D H‖ ≤
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient a ai S D H‖) * B := by
  have hpoint (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      ‖coefficient a ai S D H * F D H‖ ≤ ‖coefficient a ai S D H‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hF D hD H) (norm_nonneg _)
  have hs (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Summable (fun H : SmoothIdeal S => ‖coefficient a ai S D H * F D H‖) :=
    ((coefficient_summable_norm ha hai S hS D (Finset.mem_powerset.mp hD)).mul_right B).
      of_nonneg_of_le (fun _ => norm_nonneg _) (hpoint D hD)
  refine ⟨hs, (norm_sum_le _ _).trans ?_⟩
  calc
    _ ≤ ∑ D ∈ S.powerset, (∑' H : SmoothIdeal S, ‖coefficient a ai S D H‖) * B := by
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_tsum_le_tsum_norm (hs D hD)).trans
      exact ((hs D hD).tsum_le_tsum (hpoint D hD)
        ((coefficient_summable_norm ha hai S hS D (Finset.mem_powerset.mp hD)).mul_right B)).
          trans_eq (by rw [tsum_mul_right])
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A common tail estimate for the true restoration expansion.  The
constant and Euler order precede the deleted set, test, conductor, scales
and cutoff.  Actual scale calibration is the only row-dependent input. -/
theorem ordinaryRestorationRemainder_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A ε : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hA : 1 < A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (b : NonzeroIdeal K → ℂ), (∀ I, ‖b I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Q X Ymax : ℝ), 0 < Q → 0 < X → 0 < Ymax →
      (∀ D ∈ S.powerset, ∀ H : SmoothIdeal S,
        Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val) ≤ Ymax) →
      ∀ J : ℕ,
      (∀ D ∈ S.powerset, Summable (fun H : SmoothIdeal S =>
        ‖coefficient a ai S D H * ordinaryReflectedRemainder K b background V δ
          (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) J‖)) ∧
      ‖ordinaryRestorationRemainder K a ai S b background V δ Q X J‖ ≤
        C * testSeminorm V.toFun L A * Ymax ^ (A + 1 / 2) *
          ((2 : ℝ) ^ J) ^ (1 - A) * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨L, Ct, hCt, htail⟩ := ordinaryReflectedDyadic_normalized_tail
    K hcomplex background hδ hδA hA
  obtain ⟨Ce, hCe, heuler⟩ := reflection_mass_subpower (K := K) ε hε
  refine ⟨L, Ct * Ce, mul_nonneg hCt hCe.le, ?_⟩
  intro a ai ha hai S hS b hb V Q X Ymax hQ hX hYmax hscale J
  let B := Ct * testSeminorm V.toFun L A * Ymax ^ (A + 1 / 2) *
    ((2 : ℝ) ^ J) ^ (1 - A)
  have hSnonneg : 0 ≤ testSeminorm V.toFun L A :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 L (Nat.zero_le _) A)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : 0 ≤ A + 1 / 2 := by linarith
  have hbound (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      ‖ordinaryReflectedRemainder K b background V δ
        (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) J‖ ≤ B := by
    let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
    have hY : 0 < Y := div_pos
      (mul_pos hQ (subset_product_norm_pos D
        (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))))
      (mul_pos hX (inorm_pos H.val))
    have ht := htail b hb V Y hY J
    rw [ordinaryReflectedDyadicSum_eq_tsum K hcomplex b hb background V hδ hY] at ht
    change ‖ordinaryReflectedRemainder K b background V δ Y J‖ ≤ _ at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le (hscale D hD H) hp)
        (mul_nonneg hCt hSnonneg)) (Real.rpow_nonneg (by positivity) _))
  obtain ⟨hs, hn⟩ := coefficient_sum_bound K ha hai S hS
    (fun D H => ordinaryReflectedRemainder K b background V δ
      (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) J) hB hbound
  refine ⟨hs, hn.trans ?_⟩
  exact (mul_le_mul_of_nonneg_right (heuler S hS a ai ha hai).2 hB).trans_eq (by
    dsimp [B]
    ring)

/-- If the original polynomial is already very long, the entire true
restoration expansion is a terminal.  No fictitious same-width child is
inserted merely to force it into the core domain. -/
theorem ordinaryRestorationWhole_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A ε : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hε : 0 < ε) :
    ∃ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (b : NonzeroIdeal K → ℂ), (∀ I, ‖b I‖ ≤ 1) →
      ∀ (V : SmoothAnnularTest) (Q X Ymax : ℝ), 0 < Q → 0 < X → 0 < Ymax →
      (∀ D ∈ S.powerset, ∀ H : SmoothIdeal S,
        Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val) ≤ Ymax) →
      ‖∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
        let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
        coefficient a ai S D H * ((Real.sqrt Y : ℂ)⁻¹ *
          ∑' I : NonzeroIdeal K, b I *
            ordinaryReflectedProfile K background V δ (idealNorm K I / Y))‖ ≤
        C * testSeminorm V.toFun L A * Ymax ^ (A + 1 / 2) *
          (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨L, Ct, hCt, hwhole⟩ := ordinaryReflectedSeries_normalized_bound
    K hcomplex background hδ hδA
  obtain ⟨Ce, hCe, heuler⟩ := reflection_mass_subpower (K := K) ε hε
  refine ⟨L, Ct * Ce, mul_nonneg hCt hCe.le, ?_⟩
  intro a ai ha hai S hS b hb V Q X Ymax hQ hX hYmax hscale
  let B := Ct * testSeminorm V.toFun L A * Ymax ^ (A + 1 / 2)
  have hSnonneg : 0 ≤ testSeminorm V.toFun L A :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 L (Nat.zero_le _) A)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let F (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
    let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
    (Real.sqrt Y : ℂ)⁻¹ * ∑' I : NonzeroIdeal K, b I *
      ordinaryReflectedProfile K background V δ (idealNorm K I / Y)
  have hbound (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S) :
      ‖F D H‖ ≤ B := by
    let Y := Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)
    have hY : 0 < Y := div_pos
      (mul_pos hQ (subset_product_norm_pos D
        (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))))
      (mul_pos hX (inorm_pos H.val))
    exact ((hwhole b hb V Y hY).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hY.le (hscale D hD H) (by linarith))
        (mul_nonneg hCt hSnonneg))
  have h := (coefficient_sum_bound K ha hai S hS F hB hbound).2
  exact h.trans ((mul_le_mul_of_nonneg_right (heuler S hS a ai ha hai).2 hB).trans_eq (by
    dsimp [B]
    ring))

end HeckeSkeleton.Moments.EngineInduction
