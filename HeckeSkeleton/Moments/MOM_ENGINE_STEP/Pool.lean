import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One use of a prime pool on the whole coefficient

The finite algebra below keeps the same coefficient `c` in the original
polynomial, its amplified value, and all three errors.  In particular `c`
may be the entire centered difference, including every live slot and mask.
There is one pool average and one pushforward of its main term.  Errors
are summed at the original pairs and are never amplified a second time.

The local input `hlocal` is a column identity away from valuations 1, 6, 7;
it is deliberately distinct from a bound on an entire polynomial or energy.
The local finite-sum table is supplied by `LocalAmplifier`.

The finite averaging and pushforward arguments generalize the corresponding
arguments in openai/math, `Moments/AmplificationGlobal.lean` and
`Moments/AmplificationCount.lean` (the task's reference implementation).
-/

noncomputable section
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineStep

/-- A finite Gauss polynomial, with its complete coefficient kept intact. -/
def wholePolynomial {ι H : Type*} (s : Finset ι) (c : ι → ℂ)
    (G : ι → H → ℂ) (h : H) : ℂ :=
  ∑ i ∈ s, c i * G i h

/-- The difference of a column at a specified valuation. -/
def valuationError {ι H : Type*} (s : Finset ι) (c : ι → ℂ)
    (G : ι → H → ℂ) (ν : ι → ℕ) (k : ℕ) (h hAmp : H) : ℂ :=
  ∑ i ∈ s, if ν i = k then c i * (G i h - G i hAmp) else 0

theorem whole_polynomial_amplification {ι H : Type*} (s : Finset ι)
    (c : ι → ℂ) (G : ι → H → ℂ) (ν : ι → ℕ) (h hAmp : H)
    (hlocal : ∀ i ∈ s, ν i ≠ 1 → ν i ≠ 6 → ν i ≠ 7 →
      G i hAmp = G i h) :
    wholePolynomial s c G h = wholePolynomial s c G hAmp +
      valuationError s c G ν 1 h hAmp + valuationError s c G ν 6 h hAmp +
      valuationError s c G ν 7 h hAmp := by
  simp only [wholePolynomial, valuationError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h1 : ν i = 1
  · simp only [h1, ite_true, show ¬(1 : ℕ) = 6 by decide,
      show ¬(1 : ℕ) = 7 by decide, ite_false]
    ring
  by_cases h6 : ν i = 6
  · simp only [h6, ite_true, show ¬(6 : ℕ) = 1 by decide,
      show ¬(6 : ℕ) = 7 by decide, ite_false]
    ring
  by_cases h7 : ν i = 7
  · simp only [h7, ite_true, show ¬(7 : ℕ) = 1 by decide,
      show ¬(7 : ℕ) = 6 by decide, ite_false]
    ring
  simp only [h1, h6, h7, ite_false, add_zero, hlocal i hi h1 h6 h7]

theorem norm_four_sum_sq (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have hn : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc
      _ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le a b) le_rfl) le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
    sq_nonneg (‖a‖ - ‖d‖), sq_nonneg (‖b‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

theorem whole_polynomial_amplification_bound {ι H : Type*} (s : Finset ι)
    (c : ι → ℂ) (G : ι → H → ℂ) (ν : ι → ℕ) (h hAmp : H)
    (hlocal : ∀ i ∈ s, ν i ≠ 1 → ν i ≠ 6 → ν i ≠ 7 →
      G i hAmp = G i h) :
    ‖wholePolynomial s c G h‖ ^ 2 ≤ 4 *
      (‖wholePolynomial s c G hAmp‖ ^ 2 +
       ‖valuationError s c G ν 1 h hAmp‖ ^ 2 +
       ‖valuationError s c G ν 6 h hAmp‖ ^ 2 +
       ‖valuationError s c G ν 7 h hAmp‖ ^ 2) := by
  rw [whole_polynomial_amplification s c G ν h hAmp hlocal]
  exact norm_four_sum_sq _ _ _ _

theorem eligible_pool_average {P : Type*} (pool : Finset P) (hne : pool.Nonempty)
    (value : ℂ) (main e1 e6 e7 : P → ℂ)
    (hid : ∀ p ∈ pool, value = main p + e1 p + e6 p + e7 p) :
    ‖value‖ ^ 2 ≤ (4 / (pool.card : ℝ)) *
      ∑ p ∈ pool, (‖main p‖ ^ 2 + ‖e1 p‖ ^ 2 + ‖e6 p‖ ^ 2 + ‖e7 p‖ ^ 2) := by
  have hc : (0 : ℝ) < pool.card := Nat.cast_pos.mpr hne.card_pos
  have hb : (pool.card : ℝ) * ‖value‖ ^ 2 ≤ 4 *
      ∑ p ∈ pool, (‖main p‖ ^ 2 + ‖e1 p‖ ^ 2 + ‖e6 p‖ ^ 2 + ‖e7 p‖ ^ 2) := by
    have hb := Finset.sum_le_sum (s := pool) (fun p hp => show ‖value‖ ^ 2 ≤
      4 * (‖main p‖ ^ 2 + ‖e1 p‖ ^ 2 + ‖e6 p‖ ^ 2 + ‖e7 p‖ ^ 2) by
        rw [hid p hp]
        exact norm_four_sum_sq _ _ _ _)
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] using hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  convert hb using 1 <;> ring

theorem positive_pushforward_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (C : ℝ)
    (hg : ∀ y ∈ S.image f, 0 ≤ g y)
    (hf : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ C) :
    (∑ x ∈ S, g (f x)) ≤ C * ∑ y ∈ S.image f, g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ = ((S.filter (fun x => f x = y)).card : ℝ) * g y := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hf y hy) (hg y hy)

def eligiblePairs {H P : Type*} (rows : Finset H) (pool : Finset P)
    (allow : H → P → Prop) : Finset (H × P) :=
  (rows.product pool).filter (fun x => allow x.1 x.2)

theorem sum_eligiblePairs {H P : Type*} (rows : Finset H) (pool : Finset P)
    (allow : H → P → Prop) (f : H → P → ℝ) :
    (∑ h ∈ rows, ∑ p ∈ pool.filter (allow h), f h p) =
      ∑ x ∈ eligiblePairs rows pool allow, f x.1 x.2 := by
  simp only [eligiblePairs, Finset.sum_filter]
  exact (Finset.sum_product rows pool
    (fun x : H × P => if allow x.1 x.2 then f x.1 x.2 else 0)).symm

/-- The main term is pushed forward once; all error terms stay on pairs. -/
theorem one_pool_energy {H P : Type*} [DecidableEq H]
    (rows : Finset H) (pool : Finset P) (allow : H → P → Prop)
    (amplify : H × P → H) (value : H → ℂ) (e1 e6 e7 : H → P → ℂ)
    (density multiplicity : ℝ) (hdensity : 0 < density)
    (hsize : ∀ h ∈ rows, density ≤ (pool.filter (allow h)).card)
    (hid : ∀ h ∈ rows, ∀ p ∈ pool, allow h p →
      value h = value (amplify (h, p)) + e1 h p + e6 h p + e7 h p)
    (hfiber : ∀ y ∈ (eligiblePairs rows pool allow).image amplify,
      (((eligiblePairs rows pool allow).filter (fun x => amplify x = y)).card : ℝ) ≤
        multiplicity) :
    (∑ h ∈ rows, ‖value h‖ ^ 2) ≤ (4 / density) *
      (multiplicity * ∑ y ∈ (eligiblePairs rows pool allow).image amplify, ‖value y‖ ^ 2 +
       ∑ x ∈ eligiblePairs rows pool allow,
         (‖e1 x.1 x.2‖ ^ 2 + ‖e6 x.1 x.2‖ ^ 2 + ‖e7 x.1 x.2‖ ^ 2)) := by
  have hj : (∑ h ∈ rows, ‖value h‖ ^ 2) ≤ (4 / density) *
      ∑ x ∈ eligiblePairs rows pool allow,
        (‖value (amplify x)‖ ^ 2 + ‖e1 x.1 x.2‖ ^ 2 +
          ‖e6 x.1 x.2‖ ^ 2 + ‖e7 x.1 x.2‖ ^ 2) := by
    rw [← sum_eligiblePairs rows pool allow (fun h p =>
      ‖value (amplify (h, p))‖ ^ 2 + ‖e1 h p‖ ^ 2 + ‖e6 h p‖ ^ 2 + ‖e7 h p‖ ^ 2),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hn : (pool.filter (allow h)).Nonempty :=
      Finset.card_pos.mp (Nat.cast_pos.mp (hdensity.trans_le (hsize h hh)))
    have hb := eligible_pool_average (pool.filter (allow h)) hn (value h)
      (fun p => value (amplify (h, p))) (e1 h) (e6 h) (e7 h) (by
        intro p hp
        exact hid h hh p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by norm_num) hdensity (hsize h hh))
      (Finset.sum_nonneg (fun p _ => by positivity)))
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hf := positive_pushforward_bound (eligiblePairs rows pool allow)
    amplify (fun y => ‖value y‖ ^ 2) multiplicity (fun _ _ => sq_nonneg _) hfiber
  simp only [Finset.sum_add_distrib]
  linarith

/-- Apply the pool inequality to the literal finite polynomial, with all
three error polynomials generated by its own columns and coefficients. -/
theorem whole_polynomial_pool_energy {ι H P : Type*} [DecidableEq H]
    (s : Finset ι) (c : ι → ℂ) (G : ι → H → ℂ) (ν : P → ι → ℕ)
    (rows : Finset H) (pool : Finset P) (allow : H → P → Prop)
    (amplify : H × P → H) (density multiplicity : ℝ) (hdensity : 0 < density)
    (hsize : ∀ h ∈ rows, density ≤ (pool.filter (allow h)).card)
    (hlocal : ∀ h ∈ rows, ∀ p ∈ pool, allow h p → ∀ i ∈ s,
      ν p i ≠ 1 → ν p i ≠ 6 → ν p i ≠ 7 → G i (amplify (h, p)) = G i h)
    (hfiber : ∀ y ∈ (eligiblePairs rows pool allow).image amplify,
      (((eligiblePairs rows pool allow).filter (fun x => amplify x = y)).card : ℝ) ≤
        multiplicity) :
    (∑ h ∈ rows, ‖wholePolynomial s c G h‖ ^ 2) ≤ (4 / density) *
      (multiplicity * ∑ y ∈ (eligiblePairs rows pool allow).image amplify,
          ‖wholePolynomial s c G y‖ ^ 2 +
       ∑ x ∈ eligiblePairs rows pool allow,
         (‖valuationError s c G (ν x.2) 1 x.1 (amplify x)‖ ^ 2 +
          ‖valuationError s c G (ν x.2) 6 x.1 (amplify x)‖ ^ 2 +
          ‖valuationError s c G (ν x.2) 7 x.1 (amplify x)‖ ^ 2)) := by
  apply one_pool_energy rows pool allow amplify (wholePolynomial s c G)
    (fun h p => valuationError s c G (ν p) 1 h (amplify (h, p)))
    (fun h p => valuationError s c G (ν p) 6 h (amplify (h, p)))
    (fun h p => valuationError s c G (ν p) 7 h (amplify (h, p)))
    density multiplicity hdensity hsize
  · intro h hh p hp hallow
    exact whole_polynomial_amplification s c G (ν p) h (amplify (h, p))
      (hlocal h hh p hp hallow)
  · exact hfiber

/-- Removing a union of forbidden labels loses only their total count. -/
theorem eligible_count_after_deletions {P : Type*} [DecidableEq P]
    (pool bad₁ bad₂ : Finset P) (D₁ D₂ density : ℝ)
    (h₁ : (bad₁.card : ℝ) ≤ D₁) (h₂ : (bad₂.card : ℝ) ≤ D₂)
    (hpool : density + D₁ + D₂ ≤ pool.card) :
    density ≤ ((pool \ (bad₁ ∪ bad₂)).card : ℝ) := by
  have hs : (pool \ (bad₁ ∪ bad₂)).card + (bad₁ ∪ bad₂).card ≥ pool.card :=
    Finset.card_le_card_sdiff_add_card
  have hu : (bad₁ ∪ bad₂).card ≤ bad₁.card + bad₂.card := Finset.card_union_le _ _
  have hs' : (pool.card : ℝ) ≤ ((pool \ (bad₁ ∪ bad₂)).card : ℝ) +
      ((bad₁ ∪ bad₂).card : ℝ) := by exact_mod_cast hs
  have hu' : ((bad₁ ∪ bad₂).card : ℝ) ≤ (bad₁.card : ℝ) + (bad₂.card : ℝ) := by
    exact_mod_cast hu
  linarith

end HeckeSkeleton.Moments.EngineStep
