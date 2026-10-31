import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Complete columns for every actual annular cube piece

The original joint profile is first enlarged to one fixed complete
squarefree pool. After the common Mellin integral, each annular test is
then summed over its entire canonical provider pool. Equality follows
from the genuine test support; no selected subpolynomial is used as an
induction child.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionPools

open NumberField
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalNormPools CommonKernel CubeCompletionMellin CubeCompletionEnergy
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

/-- The support-sized pool sits inside every larger complete pool,
and the added terms vanish for the same common test. -/
theorem squarefree_sum_eq_support_pool (a : Ext → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (U R : ℝ) (hU : 0 < U) (hR : U ≤ R) :
    (∑ n ∈ squarefreePool K S R, a n * W (height K S n / U)) =
      ∑ n ∈ squarefreePool K S U, a n * W (height K S n / U) := by
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hsf, hnorm⟩ := (mem_squarefreePool K S U n).mp hn
    exact (mem_squarefreePool K S R n).mpr ⟨hsf, by linarith⟩
  · intro n hn hnot
    have hz : W (height K S n / U) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupport
      have hh := hW hsupport
      apply hnot
      exact (mem_squarefreePool K S U n).mpr
        ⟨((mem_squarefreePool K S R n).mp hn).1,
          (div_le_iff₀ hU).mp hh.2⟩
    rw [hz, mul_zero]

/-- The provider uses the complete pool at parameter `2U`; its
additional zero terms agree exactly with the complete source pool. -/
theorem squarefree_sum_eq_provider_pool (a : Ext → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (U R : ℝ) (hU : 0 < U) (hR : U ≤ R) :
    (∑ n ∈ squarefreePool K S R, a n * W (height K S n / U)) =
      ∑ n ∈ squarefreePool K S (2 * U), a n * W (height K S n / U) := by
  rw [squarefree_sum_eq_support_pool K S a W hW U R hU hR,
    squarefree_sum_eq_support_pool K S a W hW U (2 * U) hU (by linarith)]

theorem annular_columnScale_le (X H U : ℝ) (hX : 0 < X) (hH : 1 ≤ H)
    (hU : U = X / H ^ 3) (i : SchwartzTestPartition.Index) :
    0 < SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U ∧
      SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U ≤ 8 * X := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hU0 : 0 < U := by rw [hU]; positivity
  have hUX : U ≤ X := by
    rw [hU]
    exact div_le_self hX.le (one_le_pow₀ hH)
  refine ⟨mul_pos (SchwartzTestPartition.scale_pos _) hU0, ?_⟩
  exact (mul_le_mul_of_nonneg_right (annular_scale_le_eight i) hU0.le).trans
    (mul_le_mul_of_nonneg_left hUX (by norm_num))

/-- The actual Mellin piece becomes a complete provider column after
one source-independent initial enlargement to `squarefreePool (8X)`. -/
theorem annularColumn_eq_complete {β : Type*}
    (B : Finset β) (bNorm : β → ℝ) (a : β → Ext → ℂ)
    (X H U : ℝ) (hX : 0 < X) (hH : 1 ≤ H) (hU : U = X / H ^ 3)
    (t : ℝ) (i : SchwartzTestPartition.Index) :
    annularColumn B (squarefreePool K S (8 * X)) bNorm (height K S) a U t i =
      ∑ b ∈ B, columnPhase t (Real.log (bNorm b ^ 3)) *
        ∑ n ∈ squarefreePool K S
            (2 * (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)),
          a b n * annularTest t i
            (height K S n /
              (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)) := by
  unfold annularColumn
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  exact squarefree_sum_eq_provider_pool K S (a b) (annularTest t i)
    (annularTest_support t i) _ (8 * X)
    (annular_columnScale_le X H U hX hH hU i).1
    (annular_columnScale_le X H U hX hH hU i).2

/-- A genuinely subunit annular column can only contain the unit
ideal. This is proved from the integral ideal norm and the actual test
support, without passing a negative column length to the provider. -/
theorem small_column_test_zero (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (U : ℝ)
    (hU : 0 < U) (hU1 : U < 1) (n : Ext) (hn : n.val.val ≠ 1) :
    W (height K S n / U) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hbound := (div_le_iff₀ hU).mp (hW hs).2
  have hnorm : (n.val.val.absNorm : ℝ) < 2 := by
    change height K S n < 2
    linarith
  have hnlt : n.val.val.absNorm < 2 := by exact_mod_cast hnorm
  have hnpos := Ideal.absNorm_pos_of_nonZeroDivisors n.val
  have hone : n.val.val.absNorm = 1 := by omega
  exact hn (by simpa only [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp hone)

theorem small_column_norm_le (N : Finset Ext) (a : Ext → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (U A : ℝ) (hU : 0 < U) (hU1 : U < 1) (hA : 0 ≤ A)
    (ha : ∀ n ∈ N, ‖a n‖ ≤ A) :
    ‖∑ n ∈ N, a n * W (height K S n / U)‖ ≤
      A * SchwartzMap.seminorm ℝ 0 0 W := by
  by_cases hex : ∃ n ∈ N, n.val.val = 1
  · obtain ⟨n₀, hn₀, hunit⟩ := hex
    have hsum : (∑ n ∈ N, a n * W (height K S n / U)) =
        a n₀ * W (height K S n₀ / U) := by
      apply Finset.sum_eq_single n₀
      · intro n hn hne
        have hnot : n.val.val ≠ 1 := by
          intro he
          exact hne ((ideal_injective K S) (he.trans hunit.symm))
        rw [small_column_test_zero K S W hW U hU hU1 n hnot, mul_zero]
      · exact fun hn => (hn hn₀).elim
    rw [hsum, norm_mul]
    exact mul_le_mul (ha n₀ hn₀) (SchwartzMap.norm_le_seminorm ℝ W _) (norm_nonneg _) hA
  · have hz (n : Ext) (hn : n ∈ N) : W (height K S n / U) = 0 :=
      small_column_test_zero K S W hW U hU hU1 n (fun h => hex ⟨n, hn, h⟩)
    have hsum : (∑ n ∈ N, a n * W (height K S n / U)) = 0 := by
      exact Finset.sum_eq_zero (fun n hn => by rw [hz n hn, mul_zero])
    rw [hsum, norm_zero]
    exact mul_nonneg hA (apply_nonneg _ _)

/-- The bounded-column Mellin piece costs only the actual cube count.
The square of this count is canceled by `bounded_column_normalization`.
All cube characters and whole-index marks may remain in `a`. -/
theorem annularColumn_small_norm_le {β : Type*}
    (B : Finset β) (N : Finset Ext) (bNorm : β → ℝ) (a : β → Ext → ℂ)
    (U t A : ℝ) (i : SchwartzTestPartition.Index) (hU : 0 < U)
    (hsmall : SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U < 1)
    (hA : 0 ≤ A) (ha : ∀ b ∈ B, ∀ n ∈ N, ‖a b n‖ ≤ A) :
    ‖annularColumn B N bNorm (height K S) a U t i‖ ≤
      (B.card : ℝ) * A * SchwartzMap.seminorm ℝ 0 0 (annularTest t i) := by
  unfold annularColumn
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ B, A * SchwartzMap.seminorm ℝ 0 0 (annularTest t i) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul, norm_columnPhase, one_mul]
      exact small_column_norm_le K S N (a b) (annularTest t i) (annularTest_support t i)
        _ A (mul_pos (SchwartzTestPartition.scale_pos _) hU) hsmall hA (ha b hb)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionPools
