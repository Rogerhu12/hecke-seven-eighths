import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Small powers for finitely many local states

The usual `B^omega(I)` bound needs only finitely many primes below each norm
threshold.  Every sufficiently large prime pays its own factor `B` using an
arbitrarily small power of its norm.  This direct proof does not require an
unavailable ideal-divisor estimate.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.SupportPowers
open scoped Classical BigOperators

/-- Each exceptional prime is paid once, uniformly over every support. -/
theorem finite_exception_product_bound {ι : Type*}
    (q : ι → ℝ) (hq : ∀ i, 1 ≤ q i) (B eps : ℝ)
    (hB : 1 ≤ B) (heps : 0 ≤ eps) (bad : Finset ι)
    (hlarge : ∀ i, i ∉ bad → B ≤ q i ^ eps) (s : Finset ι) :
    B ^ s.card ≤ B ^ bad.card * (∏ i ∈ s, q i) ^ eps := by
  classical
  have hpoint (i : ι) : B ≤ (if i ∈ bad then B else 1) * q i ^ eps := by
    by_cases hi : i ∈ bad
    · rw [if_pos hi]
      calc
        B = B * 1 := by ring
        _ ≤ B * q i ^ eps := mul_le_mul_of_nonneg_left
          (Real.one_le_rpow (hq i) heps) (zero_le_one.trans hB)
    · simpa only [if_neg hi, one_mul] using hlarge i hi
  have hcount : (s.filter (fun i => i ∈ bad)).card ≤ bad.card := by
    apply Finset.card_le_card
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmask : (∏ i ∈ s, if i ∈ bad then B else 1) ≤ B ^ bad.card := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcount
  calc
    _ = ∏ _i ∈ s, B := by simp
    _ ≤ ∏ i ∈ s, (if i ∈ bad then B else 1) * q i ^ eps := by
      exact Finset.prod_le_prod₀ (fun _ _ => zero_le_one.trans hB) (fun i _ => hpoint i)
    _ = (∏ i ∈ s, if i ∈ bad then B else 1) * (∏ i ∈ s, q i ^ eps) :=
      Finset.prod_mul_distrib
    _ ≤ B ^ bad.card * (∏ i ∈ s, q i ^ eps) :=
      mul_le_mul_of_nonneg_right hmask (Finset.prod_nonneg
        (fun i _ => Real.rpow_nonneg (zero_le_one.trans (hq i)) _))
    _ = _ := by
      rw [Real.finsetProd_rpow s q (fun i _ => zero_le_one.trans (hq i))]

/-- A proper positive norm makes every fixed local-state count a small power
of the product of the support norms. -/
theorem fixed_states_small_power {ι : Type*}
    (q : ι → ℝ) (hq : ∀ i, 1 ≤ q i)
    (hfinite : ∀ T : ℝ, Set.Finite {i | q i ≤ T})
    (B eps : ℝ) (hB : 1 ≤ B) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : Finset ι,
      B ^ s.card ≤ C * (∏ i ∈ s, q i) ^ eps := by
  classical
  let T : ℝ := B ^ (1 / eps)
  let bad : Finset ι := (hfinite T).toFinset
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hT : T ^ eps = B := by
    dsimp [T]
    rw [← Real.rpow_mul hBp.le]
    have he : (1 / eps) * eps = 1 := by field_simp [heps.ne']
    rw [he, Real.rpow_one]
  have hlarge : ∀ i, i ∉ bad → B ≤ q i ^ eps := by
    intro i hi
    have hn : ¬ q i ≤ T := by
      intro hle
      exact hi ((hfinite T).mem_toFinset.mpr hle)
    rw [← hT]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hBp.le _) (le_of_lt (lt_of_not_ge hn)) heps.le
  exact ⟨B ^ bad.card, one_le_pow₀ hB,
    finite_exception_product_bound q hq B eps hB heps.le bad hlarge⟩

/-- Counting assignments of a fixed finite state type is exactly a power. -/
theorem finite_state_assignments_small_power {ι : Type*}
    (q : ι → ℝ) (hq : ∀ i, 1 ≤ q i)
    (hfinite : ∀ T : ℝ, Set.Finite {i | q i ≤ T})
    (r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : Finset ι,
      (Fintype.card (s → Fin r) : ℝ) ≤ C * (∏ i ∈ s, q i) ^ eps := by
  classical
  obtain ⟨C, hC, hbound⟩ := fixed_states_small_power q hq hfinite
    (max 1 (r : ℝ)) eps (le_max_left _ _) heps
  refine ⟨C, hC, ?_⟩
  intro s
  have hcard : (Fintype.card (s → Fin r) : ℝ) = (r : ℝ) ^ s.card := by
    simp
  rw [hcard]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg r) (le_max_right 1 (r : ℝ)) s.card).trans
    (hbound s)

#print axioms finite_exception_product_bound
#print axioms fixed_states_small_power
#print axioms finite_state_assignments_small_power

end HeckeSkeleton.LowEnergy.SupportPowers
