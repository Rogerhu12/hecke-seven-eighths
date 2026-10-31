import HeckeSkeleton.HighBinSupport.ValuationSeries

/-!
# Four-exponent local-block summation

This pure module retains the original four-exponent index and the exact
unit and positive completed-index branches. Fubini is justified by an
explicit Summable hypothesis; the actual number-field instantiation
supplies it from the original absolute-convergence theorem.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open HighBin.FiniteLocalTable HighBin.ValuationSeries
open scoped Classical BigOperators

abbrev FourExponent := (ℕ × ℕ) × (ℕ × ℕ)

/-- All four local exponents, before their convergent summation. -/
def localBlockValue (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : ℕ)
    (n : FourExponent) : ℂ :=
  if n.1.1 ≤ 1 then
    if n.1.1 + 3 * n.1.2 = 0 then
      Y ^ n.2.1 * V ^ n.2.2 *
        (if n.2.1 = 0 then 1 else if j + 6 * n.2.2 = 0 then ρ ^ n.2.1 else 0)
    else weightedTerm q θ G ρ X Y V j n.1.1 n.1.2 n.2.1 n.2.2
  else 0

/-- The literal completed-unit row before either infinite sum. -/
def localCompletedUnitTerm (ρ Y V : ℂ) (j : ℕ) (km : ℕ × ℕ) : ℂ :=
  Y ^ km.1 * V ^ km.2 *
    (if km.1 = 0 then 1 else if j + 6 * km.2 = 0 then ρ ^ km.1 else 0)

/-- Both completed indices must vanish in the unit row. -/
def localCompletedBlock (ρ Y V : ℂ) (j : ℕ) (n : FourExponent) : ℂ :=
  if n.1 = (0, 0) then localCompletedUnitTerm ρ Y V j n.2 else 0

/-- The positive completed index, retaining the original squarefree mask. -/
def localPositiveBlock (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ) (j : ℕ)
    (n : FourExponent) : ℂ :=
  if n.1.1 ≤ 1 then markedTerm q θ G ρ X Y V j n.1.1 n.1.2 n.2.1 n.2.2 else 0

/-- The exact value of the completed-unit row. -/
def completedUnitSeries (ρ Y V : ℂ) (j : ℕ) : ℂ :=
  1 / (1 - V) + if j = 0 then ρ * Y / (1 - ρ * Y) else 0

theorem localBlockValue_split (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j : ℕ) (n : FourExponent) :
    localBlockValue q θ G ρ X Y V j n =
      localCompletedBlock ρ Y V j n + localPositiveBlock q θ G ρ X Y V j n := by
  rcases n with ⟨⟨e, l⟩, ⟨k, m⟩⟩
  by_cases he : e ≤ 1
  · by_cases ht : e + 3 * l = 0
    · have he₀ : e = 0 := by omega
      have hl₀ : l = 0 := by omega
      subst e l
      simp [localBlockValue, localCompletedBlock, localCompletedUnitTerm,
        localPositiveBlock, markedTerm]
    · have hp : (e, l) ≠ (0, 0) := by
        intro h
        cases h
        simp at ht
      simp only [localBlockValue, localCompletedBlock, localPositiveBlock,
        markedTerm, he, ht, hp, if_true, if_false, zero_add]
  · have ht : e + 3 * l ≠ 0 := by omega
    have hp : (e, l) ≠ (0, 0) := by
      intro h
      cases h
      omega
    simp only [localBlockValue, localCompletedBlock, localPositiveBlock,
      he, hp, if_false, zero_add]

theorem localPositiveBlock_eq_indicator (q θ : ℂ) (G : ℕ → ℂ)
    (ρ X Y V : ℂ) (j : ℕ) :
    localPositiveBlock q θ G ρ X Y V j =
      {n : FourExponent | n.1.1 + 3 * n.1.2 ≠ 0}.indicator
        (localBlockValue q θ G ρ X Y V j) := by
  funext n
  by_cases he : n.1.1 ≤ 1 <;> by_cases ht : n.1.1 + 3 * n.1.2 = 0 <;>
    simp only [Set.indicator, Set.mem_setOf_eq, localPositiveBlock, localBlockValue,
      markedTerm, ne_eq, he, ht, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, ite_self]

theorem localPositiveBlock_summable (q θ : ℂ) (G : ℕ → ℂ)
    (ρ X Y V : ℂ) (j : ℕ) (h : Summable (localBlockValue q θ G ρ X Y V j)) :
    Summable (localPositiveBlock q θ G ρ X Y V j) := by
  rw [localPositiveBlock_eq_indicator]
  exact h.indicator _

theorem localCompletedBlock_summable (q θ : ℂ) (G : ℕ → ℂ)
    (ρ X Y V : ℂ) (j : ℕ) (h : Summable (localBlockValue q θ G ρ X Y V j)) :
    Summable (localCompletedBlock ρ Y V j) := by
  have hp := localPositiveBlock_summable q θ G ρ X Y V j h
  convert h.sub hp using 1
  funext n
  rw [localBlockValue_split]
  ring

theorem tsum_nat_eq_fin_two (f : ℕ → ℂ) (h : ∀ n, 2 ≤ n → f n = 0) :
    (∑' n : ℕ, f n) = ∑ n : Fin 2, f n.val := by
  rw [tsum_eq_sum (s := Finset.range 2) (by
    intro n hn
    exact h n (by simpa only [Finset.mem_range, not_lt] using hn))]
  simp [Finset.sum_range_succ, Fin.sum_univ_two]

/-- Only the proved zero branches e >= 2 and k >= 2 are removed. -/
theorem localPositiveBlock_tsum (q θ : ℂ) (G : ℕ → ℂ)
    (ρ X Y V : ℂ) (j : ℕ) (h : Summable (localPositiveBlock q θ G ρ X Y V j)) :
    (∑' n : FourExponent, localPositiveBlock q θ G ρ X Y V j n) =
      markedSeries q θ G ρ X Y V j := by
  calc
    _ = ∑' el : ℕ × ℕ, ∑' km : ℕ × ℕ,
        localPositiveBlock q θ G ρ X Y V j (el, km) := h.tsum_prod
    _ = ∑' e : ℕ, ∑' l : ℕ, ∑' km : ℕ × ℕ,
        localPositiveBlock q θ G ρ X Y V j ((e, l), km) := h.prod.tsum_prod
    _ = ∑ e : Fin 2, ∑' l : ℕ, ∑' km : ℕ × ℕ,
        localPositiveBlock q θ G ρ X Y V j ((e.val, l), km) := by
      apply tsum_nat_eq_fin_two
      intro e he
      have he' : ¬e ≤ 1 := by omega
      simp only [localPositiveBlock, he', if_false, tsum_zero]
    _ = markedSeries q θ G ρ X Y V j := by
      unfold markedSeries
      apply Finset.sum_congr rfl
      intro e _
      apply tsum_congr
      intro l
      rw [(h.prod_factor (e.val, l)).tsum_prod]
      have he : e.val ≤ 1 := by omega
      simp only [localPositiveBlock, he, if_true, HighBin.ValuationSeries.inner]
      apply tsum_nat_eq_fin_two
      intro k hk
      have hk₀ : k ≠ 0 := by omega
      have hk₁ : k ≠ 1 := by omega
      simp [markedTerm, weightedTerm, positiveConvolution, hk₀, hk₁]

theorem localCompletedUnitTerm_tsum_frequency (ρ Y V : ℂ) (hV : ‖V‖ < 1)
    (j k : ℕ) :
    (∑' m : ℕ, localCompletedUnitTerm ρ Y V j (k, m)) =
      if k = 0 then 1 / (1 - V) else if j = 0 then (ρ * Y) ^ k else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa only [localCompletedUnitTerm, pow_zero, if_true, one_mul, mul_one,
      one_div] using (hasSum_geometric_of_norm_lt_one hV).tsum_eq
  · simp only [hk, if_false]
    by_cases hj : j = 0
    · subst j
      simp only [if_true]
      calc
        _ = ∑' m : ℕ, if m = 0 then (ρ * Y) ^ k else 0 := by
          apply tsum_congr
          intro m
          by_cases hm : m = 0
          · subst m
            simp only [localCompletedUnitTerm, hk, if_false, Nat.mul_zero,
              Nat.zero_add, if_true, pow_zero, mul_one, mul_pow]
            ring
          · have hJ : 0 + 6 * m ≠ 0 := by omega
            simp only [localCompletedUnitTerm, hk, hm, hJ, if_false, mul_zero]
        _ = _ := by simp
    · have hJ (m : ℕ) : j + 6 * m ≠ 0 := by omega
      simp only [localCompletedUnitTerm, hk, hj, hJ, if_false, mul_zero, tsum_zero]

/-- The two geometric series use their true norm-convergence hypotheses. -/
theorem localCompletedUnitTerm_tsum (ρ Y V : ℂ) (hV : ‖V‖ < 1)
    (hY : ‖ρ * Y‖ < 1) (j : ℕ) (h : Summable (localCompletedUnitTerm ρ Y V j)) :
    (∑' km : ℕ × ℕ, localCompletedUnitTerm ρ Y V j km) =
      completedUnitSeries ρ Y V j := by
  rw [h.tsum_prod]
  simp_rw [localCompletedUnitTerm_tsum_frequency ρ Y V hV j]
  unfold completedUnitSeries
  by_cases hj : j = 0
  · simp only [hj, if_true]
    have htail : HasSum (fun k : ℕ => (ρ * Y) ^ (k + 1))
        (ρ * Y / (1 - ρ * Y)) := by
      convert (hasSum_geometric_of_norm_lt_one hY).mul_left (ρ * Y) using 1
      · funext k
        rw [pow_succ]
        ring
      · simp only [div_eq_mul_inv]
    have htail' : HasSum
        (fun k : ℕ => if k + 1 = 0 then 1 / (1 - V) else (ρ * Y) ^ (k + 1))
        (ρ * Y / (1 - ρ * Y)) := by simpa only [Nat.add_eq_zero, one_ne_zero,
          and_false, if_false] using htail
    simpa only [if_true] using
      (htail'.zero_add (f := fun k : ℕ => if k = 0 then 1 / (1 - V) else (ρ * Y) ^ k)).tsum_eq
  · simp only [hj, if_false, add_zero, tsum_ite_eq]

theorem localCompletedBlock_tsum (ρ Y V : ℂ) (hV : ‖V‖ < 1)
    (hY : ‖ρ * Y‖ < 1) (j : ℕ) (h : Summable (localCompletedBlock ρ Y V j)) :
    (∑' n : FourExponent, localCompletedBlock ρ Y V j n) =
      completedUnitSeries ρ Y V j := by
  have hkm : Summable (localCompletedUnitTerm ρ Y V j) := by
    simpa only [localCompletedBlock, if_true] using h.prod_factor (0, 0)
  calc
    _ = ∑' el : ℕ × ℕ, ∑' km : ℕ × ℕ,
        localCompletedBlock ρ Y V j (el, km) := h.tsum_prod
    _ = ∑' km : ℕ × ℕ, localCompletedBlock ρ Y V j ((0, 0), km) := by
      apply tsum_eq_single (0, 0)
      intro el hel
      simp only [localCompletedBlock, hel, if_false, tsum_zero]
    _ = ∑' km : ℕ × ℕ, localCompletedUnitTerm ρ Y V j km := by
      simp only [localCompletedBlock, if_true]
    _ = completedUnitSeries ρ Y V j := localCompletedUnitTerm_tsum ρ Y V hV hY j hkm

theorem localBlockValue_tsum (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j : ℕ) (h : Summable (localBlockValue q θ G ρ X Y V j))
    (hV : ‖V‖ < 1) (hY : ‖ρ * Y‖ < 1) :
    (∑' n : FourExponent, localBlockValue q θ G ρ X Y V j n) =
      completedUnitSeries ρ Y V j + markedSeries q θ G ρ X Y V j := by
  have hp := localPositiveBlock_summable q θ G ρ X Y V j h
  have hu := localCompletedBlock_summable q θ G ρ X Y V j h
  calc
    _ = ∑' n : FourExponent,
        (localCompletedBlock ρ Y V j n + localPositiveBlock q θ G ρ X Y V j n) :=
      tsum_congr (localBlockValue_split q θ G ρ X Y V j)
    _ = (∑' n : FourExponent, localCompletedBlock ρ Y V j n) +
        ∑' n : FourExponent, localPositiveBlock q θ G ρ X Y V j n := hu.tsum_add hp
    _ = _ := by rw [localCompletedBlock_tsum ρ Y V hV hY j hu,
      localPositiveBlock_tsum q θ G ρ X Y V j hp]

/-- A mark removes exactly the completed-unit summand. -/
theorem localMarkedBlock_tsum (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (j : ℕ) (b : Prop) [Decidable b]
    (h : Summable (localBlockValue q θ G ρ X Y V j))
    (hV : ‖V‖ < 1) (hY : ‖ρ * Y‖ < 1) :
    (∑' n : FourExponent, if b ∧ n.1.1 + 3 * n.1.2 = 0 then 0 else
      localBlockValue q θ G ρ X Y V j n) =
      (if b then 0 else completedUnitSeries ρ Y V j) + markedSeries q θ G ρ X Y V j := by
  by_cases hb : b
  · simp only [hb, true_and, if_true, zero_add]
    calc
      _ = ∑' n : FourExponent, localPositiveBlock q θ G ρ X Y V j n := by
        apply tsum_congr
        intro n
        by_cases he : n.1.1 ≤ 1 <;> by_cases ht : n.1.1 + 3 * n.1.2 = 0 <;>
          simp only [localPositiveBlock, localBlockValue, markedTerm, he, ht,
            if_true, if_false]
      _ = _ := localPositiveBlock_tsum q θ G ρ X Y V j
        (localPositiveBlock_summable q θ G ρ X Y V j h)
  · simp only [hb, false_and, if_false]
    exact localBlockValue_tsum q θ G ρ X Y V j h hV hY

#print axioms localPositiveBlock_tsum
#print axioms localCompletedUnitTerm_tsum
#print axioms localMarkedBlock_tsum

end HeckeSkeleton.HighBinActualInitial
