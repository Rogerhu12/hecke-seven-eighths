import HeckeSkeleton.HighBinSupport.FiniteLocalTable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Lean.Elab.Tactic.Omega
/-!
# Summing the actual valuation table: all denominator and sixth-power indices

The sextic recurrence and its zero lower edge are proved from the explicit
conductor table. Both geometric series are proved summable before their
values are used. This module supplies the local infinite-series step from
the valuation formula to the five finite Euler rational factors.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
The diagonal recurrence argument follows the supplied OpenAI reference
`Detector/HighRowsDiagonal.lean`; the arithmetic coefficients here are the
general residue-field Gauss parameters of `FiniteLocalTable`.
-/

noncomputable section
namespace HighBin.ValuationSeries
open HighBin.FiniteLocalTable
open scoped Classical BigOperators

lemma valuationGauss_step (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ) (hρ : ρ ^ 6 = 1)
    (t r J : ℕ) (ht : 0 < t) :
    valuationGauss q G ρ (t + 6) (r + 6) (J + 6) =
      q ^ 6 * valuationGauss q G ρ t r J := by
  have hd : 6 ∣ r + 6 ↔ 6 ∣ r := by omega
  have hm : (r + 6) % 6 = r % 6 := by omega
  have hlt : t + 6 ≤ J + 6 ↔ t ≤ J := by omega
  have hsub : t + 6 - 1 = (t - 1) + 6 := by omega
  have he : J + 6 = (t - 1) + 6 ↔ J = t - 1 := by omega
  have hi : (ρ⁻¹) ^ 6 = 1 := by rw [inv_pow, hρ, inv_one]
  simp only [valuationGauss, hd, hm, hlt, he, hsub, pow_add, hi, mul_one]
  split_ifs <;> ring

lemma valuationGauss_zero_below (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ)
    (t r J : ℕ) (hJ : J < t - 1) : valuationGauss q G ρ t r J = 0 := by
  simp only [valuationGauss]
  split_ifs <;> simp_all <;> omega

lemma valuationGauss_stable (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ)
    (t r J J' : ℕ) (ht : 0 < t) (hJ : t ≤ J) (hJ' : t ≤ J') :
    valuationGauss q G ρ t r J = valuationGauss q G ρ t r J' := by
  have he : J ≠ t - 1 := by omega
  have he' : J' ≠ t - 1 := by omega
  simp only [valuationGauss, hJ, hJ', he, he', if_true, if_false]

lemma positiveConvolution_step (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ) (hρ : ρ ^ 6 = 1)
    (t k J : ℕ) (ht : 0 < t) :
    positiveConvolution q G ρ (t + 6) k (J + 6) =
      q ^ 6 * positiveConvolution q G ρ t k J := by
  unfold positiveConvolution
  by_cases hk : k = 0
  · simp only [hk, if_true]
    exact valuationGauss_step q G ρ hρ t t J ht
  · simp only [hk, if_false]
    by_cases hk1 : k = 1
    · simp only [hk1, if_true]
      rw [show t + 6 + 1 = (t + 1) + 6 by omega,
        show t + 6 - 1 = (t - 1) + 6 by omega,
        valuationGauss_step q G ρ hρ (t + 1) (t - 1) J (by omega)]
      ring
    · simp [hk1]

lemma positiveConvolution_zero_below (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ)
    (t k J : ℕ) (hJ : J < t - 1) :
    positiveConvolution q G ρ t k J = 0 := by
  unfold positiveConvolution
  split_ifs
  · exact valuationGauss_zero_below q G ρ t t J hJ
  · rw [valuationGauss_zero_below q G ρ (t + 1) (t - 1) J (by omega), mul_zero]
  · rfl

lemma positiveConvolution_stable (q : ℂ) (G : ℕ → ℂ) (ρ : ℂ)
    (t k J J' : ℕ) (ht : 0 < t) (hJ : t + 1 ≤ J) (hJ' : t + 1 ≤ J') :
    positiveConvolution q G ρ t k J = positiveConvolution q G ρ t k J' := by
  unfold positiveConvolution
  split_ifs
  · exact valuationGauss_stable q G ρ t t J J' ht (by omega) (by omega)
  · rw [valuationGauss_stable q G ρ (t + 1) (t - 1) J J' (by omega) hJ hJ']
  · rfl

/-- Exclude the completed unit index; it is restored separately. -/
def markedTerm (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j e l k m : ℕ) : ℂ :=
  if e + 3 * l = 0 then 0 else weightedTerm q θ G ρ X Y V j e l k m

lemma markedTerm_step (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (j e l k m : ℕ) (ht : 0 < e + 3 * l) :
    markedTerm q θ G ρ X Y V j e (l + 2) k (m + 1) =
      ratio q θ X V * markedTerm q θ G ρ X Y V j e l k m := by
  simp only [markedTerm, show e + 3 * (l + 2) ≠ 0 by omega,
    show e + 3 * l ≠ 0 by omega, if_false, weightedTerm]
  rw [show e + 3 * (l + 2) = (e + 3 * l) + 6 by omega,
    show j + 6 * (m + 1) = (j + 6 * m) + 6 by omega,
    positiveConvolution_step q G ρ hρ (e + 3 * l) k (j + 6 * m) ht]
  rw [pow_add θ (e + 3 * l) 6, pow_add q l 2,
    pow_add X (e + 3 * l) 6, pow_succ V m]
  unfold ratio
  field_simp [hq] <;> ring

lemma markedTerm_lower_edge (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j e l k : ℕ) (hj : j < 6) (ht : 0 < e + 3 * l) :
    markedTerm q θ G ρ X Y V j e (l + 2) k 0 = 0 := by
  rw [markedTerm, if_neg (by omega)]
  unfold weightedTerm
  rw [positiveConvolution_zero_below q G ρ _ _ _ (by omega), mul_zero]

lemma markedTerm_higher_denominator (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j e l k m : ℕ) : markedTerm q θ G ρ X Y V j e l (k + 2) m = 0 := by
  simp [markedTerm, weightedTerm, positiveConvolution]

lemma geometric_indicator_summable (V A : ℂ) (hV : ‖V‖ < 1) (p : ℕ → Prop) :
    Summable (fun m => (if p m then A else 0) * V ^ m) := by
  convert (((hasSum_geometric_of_norm_lt_one hV).summable.mul_left A).indicator
    {m | p m}) using 1
  funext m
  by_cases hm : p m <;> simp [hm]

lemma valuationGauss_summable (q : ℂ) (G : ℕ → ℂ) (ρ V : ℂ)
    (hV : ‖V‖ < 1) (t r : ℕ) (J : ℕ → ℕ) :
    Summable (fun m => valuationGauss q G ρ t r (J m) * V ^ m) := by
  by_cases hr : 6 ∣ r
  · have hA := geometric_indicator_summable V (q ^ (t - 1) * (q - 1)) hV
      (fun m => t ≤ J m)
    have hB := geometric_indicator_summable V (-q ^ (t - 1)) hV
      (fun m => ¬ t ≤ J m ∧ J m = t - 1)
    convert hA.add hB using 1
    funext m
    by_cases hJ : t ≤ J m
    · simp only [Pi.add_apply, valuationGauss, hr, hJ, ite_true,
        not_true_eq_false, false_and, ite_false, zero_mul, add_zero]
    · by_cases hE : J m = t - 1
      · have hB : ¬t ≤ J m ∧ J m = t - 1 := ⟨hJ, hE⟩
        simp only [Pi.add_apply, valuationGauss, if_pos hr, if_neg hJ,
          if_pos hE, if_pos hB, zero_mul, zero_add]
        ring
      · have hB : ¬(¬t ≤ J m ∧ J m = t - 1) := fun h => hE h.2
        simp only [Pi.add_apply, valuationGauss, if_pos hr, if_neg hJ,
          if_neg hE, if_neg hB, mul_zero, zero_mul, zero_add]
  · convert geometric_indicator_summable V
      (q ^ (t - 1) * (ρ⁻¹ ^ r * G (r % 6))) hV (fun m => J m = t - 1) using 1
    funext m
    simp only [valuationGauss, if_neg hr]
    split_ifs <;> ring

lemma positiveConvolution_summable (q : ℂ) (G : ℕ → ℂ) (ρ V : ℂ)
    (hV : ‖V‖ < 1) (t k : ℕ) (J : ℕ → ℕ) :
    Summable (fun m => positiveConvolution q G ρ t k (J m) * V ^ m) := by
  unfold positiveConvolution
  split_ifs with hk hk1
  · exact valuationGauss_summable q G ρ V hV t t J
  · convert (valuationGauss_summable q G ρ V hV (t + 1) (t - 1) J).mul_left (G 1 / q) using 1
    funext m
    ring
  · simp

lemma markedTerm_frequency_summable (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hV : ‖V‖ < 1) (j e l k : ℕ) :
    Summable (fun m => markedTerm q θ G ρ X Y V j e l k m) := by
  by_cases ht : e + 3 * l = 0
  · simp only [markedTerm, if_pos ht, summable_zero]
  · simp only [markedTerm, if_neg ht, weightedTerm]
    convert (positiveConvolution_summable q G ρ V hV (e + 3 * l) k
      (fun m => j + 6 * m)).mul_left
      ((G 2 / q) ^ e * θ ^ (e + 3 * l) / q ^ l * X ^ (e + 3 * l) * Y ^ k) using 1
    funext m
    ring

lemma markedTerm_base_tail (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j e l k m : ℕ) (ht : 0 < e + 3 * l) (ht6 : e + 3 * l ≤ 6) :
    markedTerm q θ G ρ X Y V j e l k (m + 2) =
      markedTerm q θ G ρ X Y V j e l k 2 * V ^ m := by
  simp only [markedTerm, show e + 3 * l ≠ 0 by omega, if_false, weightedTerm]
  rw [positiveConvolution_stable q G ρ (e + 3 * l) k (j + 6 * (m + 2))
    (j + 6 * 2) ht (by omega) (by omega), pow_add V m 2]
  ring

/-- Both denominator valuations are retained. -/
def inner (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2, ∑' m, markedTerm q θ G ρ X Y V j e l k.val m

/-- The full positive completed-index local series. -/
def markedSeries (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l, inner q θ G ρ X Y V j e.val l

@[simp] lemma inner_zero (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : ℕ) :
    inner q θ G ρ X Y V j 0 0 = 0 := by simp [inner, markedTerm]

lemma inner_base (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (hV : ‖V‖ < 1)
    (j e l : ℕ) (ht : 0 < e + 3 * l) (ht6 : e + 3 * l ≤ 6) :
    inner q θ G ρ X Y V j e l = baseAt q θ G ρ X Y V j e l := by
  unfold inner baseAt
  apply Finset.sum_congr rfl
  intro k _
  have ht' : HasSum (fun m => markedTerm q θ G ρ X Y V j e l k.val (m + 2))
      (markedTerm q θ G ρ X Y V j e l k.val 2 / (1 - V)) := by
    have hg := (hasSum_geometric_of_norm_lt_one hV).mul_left
      (markedTerm q θ G ρ X Y V j e l k.val 2)
    rw [← div_eq_mul_inv] at hg
    convert hg using 1
    funext m
    exact markedTerm_base_tail q θ G ρ X Y V j e l k.val m ht ht6
  have hs := ht'.sum_range_add
    (f := fun m => markedTerm q θ G ρ X Y V j e l k.val m) (k := 2)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    markedTerm, show e + 3 * l ≠ 0 by omega, if_false] using hs.tsum_eq

lemma diagonal_recurrence_eq (f : ℕ → ℕ → ℂ) (R : ℂ)
    (hstep : ∀ r m, f (r + 1) (m + 1) = R * f r m) (hz : ∀ r, f (r + 1) 0 = 0) :
    ∀ r m, f r m = if r ≤ m then R ^ r * f 0 (m - r) else 0 := by
  intro r
  induction r with
  | zero => intro m; simp
  | succ r ih =>
    intro m
    cases m with
    | zero => simp [hz]
    | succ m =>
      rw [hstep, ih]
      by_cases h : r ≤ m
      · simp only [h, if_true, Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub, pow_succ]
        ring
      · simp only [h, if_false, Nat.succ_le_succ_iff, mul_zero]

lemma diagonal_recurrence_inner_hasSum (f : ℕ → ℕ → ℂ) (R : ℂ)
    (hstep : ∀ r m, f (r + 1) (m + 1) = R * f r m) (hz : ∀ r, f (r + 1) 0 = 0)
    (hs : Summable (f 0)) (r : ℕ) : HasSum (f r) (R ^ r * ∑' m, f 0 m) := by
  have he := diagonal_recurrence_eq f R hstep hz
  have htail : HasSum (fun m => f r (m + r)) (R ^ r * ∑' m, f 0 m) := by
    convert hs.hasSum.mul_left (R ^ r) using 1
    funext m
    rw [he, if_pos (Nat.le_add_left r m), Nat.add_sub_cancel]
  have hzero : (∑ m ∈ Finset.range r, f r m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [he, if_neg (by have := Finset.mem_range.mp hm; omega)]
  simpa only [hzero, zero_add] using htail.sum_range_add

lemma diagonal_recurrence_hasSum (f : ℕ → ℕ → ℂ) (R : ℂ)
    (hstep : ∀ r m, f (r + 1) (m + 1) = R * f r m) (hz : ∀ r, f (r + 1) 0 = 0)
    (hs : Summable (f 0)) (hR : ‖R‖ < 1) :
    HasSum (fun r => ∑' m, f r m) ((∑' m, f 0 m) / (1 - R)) := by
  have he (r : ℕ) := (diagonal_recurrence_inner_hasSum f R hstep hz hs r).tsum_eq
  have hg : HasSum (fun r => R ^ r * ∑' m, f 0 m) ((∑' m, f 0 m) / (1 - R)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (∑' m, f 0 m)
  convert hg using 1
  funext r
  exact he r

lemma inner_family_hasSum (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (hV : ‖V‖ < 1) (hR : ‖ratio q θ X V‖ < 1)
    (j e l : ℕ) (hj : j < 6) (ht : 0 < e + 3 * l) :
    HasSum (fun r => inner q θ G ρ X Y V j e (l + 2 * r))
      (inner q θ G ρ X Y V j e l / (1 - ratio q θ X V)) := by
  have hs (k : ℕ) : HasSum
      (fun r => ∑' m, markedTerm q θ G ρ X Y V j e (l + 2 * r) k m)
      ((∑' m, markedTerm q θ G ρ X Y V j e l k m) / (1 - ratio q θ X V)) := by
    apply diagonal_recurrence_hasSum
    · intro r m
      rw [show l + 2 * (r + 1) = (l + 2 * r) + 2 by omega]
      exact markedTerm_step q θ G ρ X Y V hq hρ j e (l + 2 * r) k m (by omega)
    · intro r
      rw [show l + 2 * (r + 1) = (l + 2 * r) + 2 by omega]
      exact markedTerm_lower_edge q θ G ρ X Y V j e (l + 2 * r) k hj (by omega)
    · simpa only [mul_zero, add_zero] using
        markedTerm_frequency_summable q θ G ρ X Y V hV j e l k
    · exact hR
  simpa only [inner, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, add_div] using (hs 0).add (hs 1)

/-- All four positive residue classes of the completed ideal, including
both odd and even cube indices, are summed explicitly. -/
theorem markedSeries_eq_base (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (hV : ‖V‖ < 1) (hR : ‖ratio q θ X V‖ < 1)
    (j : ℕ) (hj : j < 6) :
    markedSeries q θ G ρ X Y V j = baseMarked q θ G ρ X Y V j / (1 - ratio q θ X V) := by
  have h02 := inner_family_hasSum q θ G ρ X Y V hq hρ hV hR j 0 2 hj (by omega)
  have h10 := inner_family_hasSum q θ G ρ X Y V hq hρ hV hR j 1 0 hj (by omega)
  have h01 := inner_family_hasSum q θ G ρ X Y V hq hρ hV hR j 0 1 hj (by omega)
  have h11 := inner_family_hasSum q θ G ρ X Y V hq hρ hV hR j 1 1 hj (by omega)
  have he0 : HasSum (fun r => inner q θ G ρ X Y V j 0 (2 * r))
      (inner q θ G ρ X Y V j 0 2 / (1 - ratio q θ X V)) := by
    have hshift : HasSum (fun r => inner q θ G ρ X Y V j 0 (2 * (r + 1)))
        (inner q θ G ρ X Y V j 0 2 / (1 - ratio q θ X V)) := by
      convert h02 using 1
      funext r
      congr 1
      omega
    have hh := hshift.sum_range_add
      (f := fun r => inner q θ G ρ X Y V j 0 (2 * r)) (k := 1)
    simpa only [Finset.sum_range_one, mul_zero, inner_zero, zero_add] using hh
  have he1 : HasSum (fun r => inner q θ G ρ X Y V j 1 (2 * r))
      (inner q θ G ρ X Y V j 1 0 / (1 - ratio q θ X V)) := by
    simpa only [zero_add] using h10
  have ho0 : HasSum (fun r => inner q θ G ρ X Y V j 0 (2 * r + 1))
      (inner q θ G ρ X Y V j 0 1 / (1 - ratio q θ X V)) := by
    simpa only [Nat.add_comm 1] using h01
  have ho1 : HasSum (fun r => inner q θ G ρ X Y V j 1 (2 * r + 1))
      (inner q θ G ρ X Y V j 1 1 / (1 - ratio q θ X V)) := by
    simpa only [Nat.add_comm 1] using h11
  unfold markedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [(he0.even_add_odd ho0).tsum_eq, (he1.even_add_odd ho1).tsum_eq]
  rw [inner_base q θ G ρ X Y V hV j 0 2 (by omega) (by omega),
    inner_base q θ G ρ X Y V hV j 1 0 (by omega) (by omega),
    inner_base q θ G ρ X Y V hV j 0 1 (by omega) (by omega),
    inner_base q θ G ρ X Y V hV j 1 1 (by omega) (by omega)]
  unfold baseMarked
  ring

/-- Local ramified Euler identification from the explicit valuation series.
The input never assumes the five-row rational identity. -/
theorem ramifiedSeries_eq_finiteTable (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1) (hV : ‖V‖ < 1) (hR : ‖ratio q θ X V‖ < 1)
    (j : Fin 5) :
    1 + (1 - V) * markedSeries q θ G ρ X Y V (j.val + 1) =
      finiteTableCorrection q θ G ρ X Y V j := by
  rw [markedSeries_eq_base q θ G ρ X Y V hq hρ hV hR (j.val + 1) (by omega)]
  unfold finiteTableCorrection
  ring

#print axioms markedSeries_eq_base
#print axioms ramifiedSeries_eq_finiteTable
end HighBin.ValuationSeries
