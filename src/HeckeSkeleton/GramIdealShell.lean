import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeSkeleton.GramDyadic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The ideal double shell of the Gram estimate (GR-09)

From the uncompiled candidate `ActualIdealDyadicDoubleSum.lean`
(old repository cache `actual-gram-dyadic-sum-20261012`), compiled here, plus
the conversion to the skeleton's form with `N ^ (-2 : ℝ)`. The only counting
input is the proved linear count of all nonzero integral ideals.
-/

noncomputable section

namespace HeckeSkeleton.GramIdealShell

open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.GramDyadic
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- A genuine dyadic shell index, chosen from the actual ideal norm. -/
def idealShellIndex (I : NonzeroIdeal K) : ℕ :=
  Classical.choose (exists_nat_pow_near (one_le_idealNorm K I)
    (by norm_num : (1 : ℝ) < 2))

theorem idealShellIndex_spec (I : NonzeroIdeal K) :
    (2 : ℝ) ^ idealShellIndex K I ≤ idealNorm K I ∧
      idealNorm K I < (2 : ℝ) ^ (idealShellIndex K I + 1) :=
  Classical.choose_spec (exists_nat_pow_near (one_le_idealNorm K I)
    (by norm_num : (1 : ℝ) < 2))

def idealPairShellIndex (p : NonzeroIdeal K × NonzeroIdeal K) : ℕ × ℕ :=
  (idealShellIndex K p.1, idealShellIndex K p.2)

/-- The norm kernel remaining after the frequency count and the `N²` factor
in (3.37). The inverse square is essential for the shell summation. -/
def idealPairKernel (L : ℝ) (p : NonzeroIdeal K × NonzeroIdeal K) : ℝ :=
  (idealNorm K p.1 * idealNorm K p.2)⁻¹ ^ 2 *
    min 1 ((idealNorm K p.1 * idealNorm K p.2 / L) ^ 3)

theorem idealPairKernel_nonneg {L : ℝ} (hL : 0 < L)
    (p : NonzeroIdeal K × NonzeroIdeal K) : 0 ≤ idealPairKernel K L p := by
  unfold idealPairKernel
  exact mul_nonneg (sq_nonneg _) (le_min (by norm_num)
    (pow_nonneg (div_nonneg (mul_nonneg (idealNorm_pos K _).le
      (idealNorm_pos K _).le) hL.le) _))

/-- Exact finite regrouping by the two actual ideal norms. -/
theorem sum_idealPairKernel_eq_shells (s : Finset (NonzeroIdeal K × NonzeroIdeal K))
    (L : ℝ) :
    (∑ p ∈ s, idealPairKernel K L p) =
      ∑ n ∈ s.image (idealPairShellIndex K),
        ∑ p ∈ s with idealPairShellIndex K p = n, idealPairKernel K L p := by
  symm
  apply Finset.sum_fiberwise_of_maps_to (g := idealPairShellIndex K)
  intro p hp
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- The real norm kernel on a shell is dominated by the corresponding
numerical kernel, with the upper endpoints producing the shift `L / 4`. -/
theorem idealPairKernel_le_shell {L : ℝ} (hL : 0 < L)
    (p : NonzeroIdeal K × NonzeroIdeal K) (n : ℕ × ℕ)
    (hp : idealPairShellIndex K p = n) :
    idealPairKernel K L p ≤ ((2 : ℝ) ^ (n.1 + n.2))⁻¹ ^ 2 *
      min 1 (((2 : ℝ) ^ (n.1 + n.2) / (L / 4)) ^ 3) := by
  have h1 := idealShellIndex_spec K p.1
  have h2 := idealShellIndex_spec K p.2
  have hi : idealShellIndex K p.1 = n.1 := congrArg Prod.fst hp
  have hj : idealShellIndex K p.2 = n.2 := congrArg Prod.snd hp
  rw [hi] at h1
  rw [hj] at h2
  have hpow : 0 < (2 : ℝ) ^ (n.1 + n.2) := by positivity
  have hnorm : 0 < idealNorm K p.1 * idealNorm K p.2 :=
    mul_pos (idealNorm_pos K _) (idealNorm_pos K _)
  have hlo : (2 : ℝ) ^ (n.1 + n.2) ≤ idealNorm K p.1 * idealNorm K p.2 := by
    rw [pow_add]
    exact mul_le_mul h1.1 h2.1 (by positivity) (idealNorm_pos K _).le
  have hhi : idealNorm K p.1 * idealNorm K p.2 ≤
      4 * (2 : ℝ) ^ (n.1 + n.2) := by
    calc
      _ ≤ (2 : ℝ) ^ (n.1 + 1) * (2 : ℝ) ^ (n.2 + 1) :=
        mul_le_mul h1.2.le h2.2.le (idealNorm_pos K _).le (by positivity)
      _ = _ := by simp only [pow_add, pow_one]; ring
  have hinv := pow_le_pow_left₀ (inv_nonneg.mpr hnorm.le)
    ((inv_le_inv₀ hnorm hpow).mpr hlo) 2
  have hdiv : idealNorm K p.1 * idealNorm K p.2 / L ≤
      (2 : ℝ) ^ (n.1 + n.2) / (L / 4) := by
    calc
      _ ≤ (4 * (2 : ℝ) ^ (n.1 + n.2)) / L :=
        div_le_div_of_nonneg_right hhi hL.le
      _ = _ := by field_simp [ne_of_gt hL]
  have hmin : min 1 ((idealNorm K p.1 * idealNorm K p.2 / L) ^ 3) ≤
      min 1 (((2 : ℝ) ^ (n.1 + n.2) / (L / 4)) ^ 3) :=
    min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hnorm.le hL.le) hdiv 3)
  exact mul_le_mul hinv hmin
    (le_min (by norm_num) (pow_nonneg (div_nonneg hnorm.le hL.le) _))
    (sq_nonneg _)

/-- Each finite shell fibre is counted by two genuine norm cutoffs. The
constant is the existing all-ideal count constant, not an extra assumption
on the finite family. -/
theorem exists_shell_fibre_count :
    ∃ a : ℝ, 0 < a ∧ ∀ (s : Finset (NonzeroIdeal K × NonzeroIdeal K)) (n : ℕ × ℕ),
      ((s.filter (fun p => idealPairShellIndex K p = n)).card : ℝ) ≤
        4 * a ^ 2 * (2 : ℝ) ^ (n.1 + n.2) := by
  obtain ⟨a, ha, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨a, ha, ?_⟩
  intro s n
  let A := dyadicIdealSupport K ((2 : ℝ) ^ (n.1 + 1) / 2)
  let B := dyadicIdealSupport K ((2 : ℝ) ^ (n.2 + 1) / 2)
  have hsub : s.filter (fun p => idealPairShellIndex K p = n) ⊆ A ×ˢ B := by
    intro p hp
    have hpn := (Finset.mem_filter.mp hp).2
    have h1 := (idealShellIndex_spec K p.1).2
    have h2 := (idealShellIndex_spec K p.2).2
    have hi : idealShellIndex K p.1 = n.1 := congrArg Prod.fst hpn
    have hj : idealShellIndex K p.2 = n.2 := congrArg Prod.snd hpn
    rw [hi] at h1
    rw [hj] at h2
    apply Finset.mem_product.mpr
    constructor
    · change p.1 ∈ dyadicIdealSupport K ((2 : ℝ) ^ (n.1 + 1) / 2)
      apply (mem_dyadicIdealSupport_iff K
        (D := (2 : ℝ) ^ (n.1 + 1) / 2) (by positivity) p.1).mpr
      nlinarith
    · change p.2 ∈ dyadicIdealSupport K ((2 : ℝ) ^ (n.2 + 1) / 2)
      apply (mem_dyadicIdealSupport_iff K
        (D := (2 : ℝ) ^ (n.2 + 1) / 2) (by positivity) p.2).mpr
      nlinarith
  have hc : ((s.filter (fun p => idealPairShellIndex K p = n)).card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product A B)
  have hA : (A.card : ℝ) ≤ a * (2 : ℝ) ^ (n.1 + 1) :=
    hcount _ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hB : (B.card : ℝ) ≤ a * (2 : ℝ) ^ (n.2 + 1) :=
    hcount _ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  calc
    _ ≤ (A.card : ℝ) * (B.card : ℝ) := hc
    _ ≤ (a * (2 : ℝ) ^ (n.1 + 1)) * (a * (2 : ℝ) ^ (n.2 + 1)) :=
      mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
    _ = _ := by simp only [pow_add, pow_one]; ring

/-- Uniform finite-partial-sum control; all arithmetic shell counting and
finite regrouping have already been performed inside the proof. -/
theorem exists_idealPairKernel_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 < L →
      ∀ s : Finset (NonzeroIdeal K × NonzeroIdeal K),
        (∑ p ∈ s, idealPairKernel K L p) ≤ C * (1 + Real.log (2 + L)) / L := by
  obtain ⟨a, ha, hcount⟩ := exists_shell_fibre_count K
  let C := 16 * a ^ 2 * dyadicBoundConstant
  have hD : 0 < dyadicBoundConstant :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) dyadicBoundConstant_ge_four
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L hL s
  have hL4 : 0 < L / 4 := by positivity
  have hfinite : (∑ p ∈ s, idealPairKernel K L p) ≤
      4 * a ^ 2 * ∑ n ∈ s.image (idealPairShellIndex K), dyadicKernel (L / 4) (n.1+n.2) := by
    rw [sum_idealPairKernel_eq_shells K, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    let z : ℝ := (2 : ℝ) ^ (n.1 + n.2)
    let b : ℝ := z⁻¹ ^ 2 * min 1 ((z / (L / 4)) ^ 3)
    have hz : 0 < z := by dsimp [z]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    calc
      _ ≤ ∑ p ∈ s.filter (fun p => idealPairShellIndex K p = n), b := by
        apply Finset.sum_le_sum
        intro p hp
        exact idealPairKernel_le_shell K hL p n (Finset.mem_filter.mp hp).2
      _ = ((s.filter (fun p => idealPairShellIndex K p = n)).card : ℝ) * b := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * a ^ 2 * z) * b :=
        mul_le_mul_of_nonneg_right (hcount s n) hb
      _ = 4 * a ^ 2 * dyadicKernel (L / 4) (n.1+n.2) := by
        have hhalf : (1 / 2 : ℝ) ^ (n.1 + n.2) = z⁻¹ := by
          dsimp [z]
          rw [one_div_pow, one_div]
        change (4 * a ^ 2 * z) *
          (z⁻¹ ^ 2 * min 1 ((z / (L / 4)) ^ 3)) =
          4 * a ^ 2 * ((1 / 2 : ℝ) ^ (n.1 + n.2) *
            min 1 ((z / (L / 4)) ^ 3))
        rw [hhalf]
        generalize min 1 ((z / (L / 4)) ^ 3) = t
        field_simp [ne_of_gt hz]
  have hpartial : (∑ n ∈ s.image (idealPairShellIndex K),
      dyadicKernel (L / 4) (n.1+n.2)) ≤
      ∑' n : ℕ × ℕ, dyadicKernel (L / 4) (n.1+n.2) :=
    (summable_pairKernel hL4).sum_le_tsum _ (fun n _ => dyadicKernel_nonneg hL4 _)
  have hnumeric : (∑' n : ℕ × ℕ, dyadicKernel (L / 4) (n.1+n.2)) ≤
      dyadicBoundConstant * (1 + Real.log (2 + L / 4)) / (L / 4) := by
    rw [tsum_pairKernel_eq hL4]
    exact tsum_weightedKernel_le_log hL4
  have hlog : Real.log (2 + L / 4) ≤ Real.log (2 + L) :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ 4 * a ^ 2 * ∑ n ∈ s.image (idealPairShellIndex K),
        dyadicKernel (L / 4) (n.1+n.2) := hfinite
    _ ≤ 4 * a ^ 2 * (dyadicBoundConstant * (1 + Real.log (2 + L / 4)) / (L / 4)) :=
      mul_le_mul_of_nonneg_left (hpartial.trans hnumeric) (by positivity)
    _ = C * (1 + Real.log (2 + L / 4)) / L := by
      dsimp [C]
      field_simp [ne_of_gt hL]
      ring
    _ ≤ C * (1 + Real.log (2 + L)) / L :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by dsimp [C]; positivity)) hL.le

/-- The actual ideal double series is summable, with its bound uniform in
the positive continuous parameter. No rearrangement premise is imposed. -/
theorem exists_idealPairKernel_tsum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      Summable (idealPairKernel K L) ∧
        (∑' p, idealPairKernel K L p) ≤ C * (1 + Real.log (2 + L)) / L := by
  obtain ⟨C, hC, hb⟩ := exists_idealPairKernel_finite_bound K
  refine ⟨C, hC, ?_⟩
  intro L hL
  exact ⟨summable_of_sum_le (idealPairKernel_nonneg K hL) (hb L hL),
    Real.tsum_le_of_sum_le (idealPairKernel_nonneg K hL) (hb L hL)⟩

/-- In particular, the original two finite ideal cutoffs need no shell or
cardinality premise. The constant precedes both cutoffs and the parameter. -/
theorem exists_finite_ideal_double_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 < L →
      ∀ A B : Finset (NonzeroIdeal K),
        (∑ I ∈ A, ∑ J ∈ B, idealPairKernel K L (I, J)) ≤
          C * (1 + Real.log (2 + L)) / L := by
  obtain ⟨C, hC, hb⟩ := exists_idealPairKernel_finite_bound K
  refine ⟨C, hC, ?_⟩
  intro L hL A B
  simpa only [Finset.sum_product] using hb L hL (A ×ˢ B)

/-- The literal scale substitution from the nonexceptional calculation:
`L = Y / (H * Pa)`. This isolates the factor `Pa² / Y` when the later
annular `H`-decay is inserted. It does not assert the still separate Gram
or moving-profile estimate. -/
theorem exists_scaled_ideal_double_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Y H Pa : ℝ),
      0 < Q → 0 < Y → 0 < H → 0 < Pa →
      ∀ A B : Finset (NonzeroIdeal K),
        (Q * (H * Pa) / Y) *
          (∑ I ∈ A, ∑ J ∈ B, idealPairKernel K (Y / (H * Pa)) (I, J)) ≤
        C * (Q / Y) * ((H * Pa) ^ 2 / Y) *
          (1 + Real.log (2 + Y / (H * Pa))) := by
  obtain ⟨C, hC, hb⟩ := exists_finite_ideal_double_sum_bound K
  refine ⟨C, hC, ?_⟩
  intro Q Y H Pa hQ hY hH hPa A B
  have hHP : 0 < H * Pa := mul_pos hH hPa
  calc
    _ ≤ (Q * (H * Pa) / Y) *
        (C * (1 + Real.log (2 + Y / (H * Pa))) / (Y / (H * Pa))) :=
      mul_le_mul_of_nonneg_left (hb _ (div_pos hY hHP) A B) (by positivity)
    _ = _ := by field_simp [ne_of_gt hY, ne_of_gt hH, ne_of_gt hPa]

theorem idealPairKernel_eq (L : ℝ) (p : NonzeroIdeal K × NonzeroIdeal K) :
    (idealNorm K p.1) ^ (-2 : ℝ) * (idealNorm K p.2) ^ (-2 : ℝ) *
        min 1 ((idealNorm K p.1 * idealNorm K p.2 / L) ^ 3) = idealPairKernel K L p := by
  unfold idealPairKernel
  rw [Real.rpow_neg (idealNorm_pos K p.1).le, Real.rpow_neg (idealNorm_pos K p.2).le,
    Real.rpow_two, Real.rpow_two, mul_inv, mul_pow, inv_pow, inv_pow]

/-- GR-09 in the form stated in `HeckeSkeleton.Gram`. -/
theorem actual_ideal_double_shell :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-2 : ℝ) * (idealNorm K IJ.2) ^ (-2 : ℝ) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C * (1 + Real.log (2 + Λ)) / Λ := by
  obtain ⟨C, hC, hb⟩ := exists_idealPairKernel_tsum_bound K
  refine ⟨C, hC, fun Λ hΛ => ?_⟩
  obtain ⟨hs, hle⟩ := hb Λ hΛ
  refine ⟨hs.congr (fun p => (idealPairKernel_eq K Λ p).symm), ?_⟩
  rw [tsum_congr (idealPairKernel_eq K Λ)]
  exact hle

end HeckeSkeleton.GramIdealShell
