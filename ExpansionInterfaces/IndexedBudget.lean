import ExpansionInterfaces.CommonBudget

/-!
# A common budget for complete moving families

The fifth component of the expansion is a family of witness counts indexed
by a block, amplitude label and real detector parameter.  Those indices are
not finite and may depend on Z and T.  Only the number of component kinds
must be finite.  This lemma keeps all their indices inside the final
universal quantifier and does not choose new constants after an index.
-/

namespace ExpansionInterfaces

theorem finite_simultaneous_indexed_bound {n : ℕ}
    (Index : Fin n → ℝ → ℝ → Type*)
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (heightful : Fin n → Bool)
    (value scale : (i : Fin n) → (Z T : ℝ) → Index i Z T → ℝ)
    (hscale : ∀ i Z T q, 2 ≤ Z → 0 ≤ scale i Z T q)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z → ∀ q : Index i Z (Z ^ τ),
        value i Z (Z ^ τ) q ≤ (cuts τ i).constant * scale i Z (Z ^ τ) q *
          (1 + Z ^ τ) ^ budgetExponent (heightful i) (budgets i).degree)
    (τ : ℝ) (hτ : 0 < τ) (hceiling : τ ≤ (HeightBudget.common budgets).ceiling)
    (Z : ℝ) (hZ : (Cutoffs.common (cuts τ)).threshold ≤ Z)
    (i : Fin n) (q : Index i Z (Z ^ τ)) :
    value i Z (Z ^ τ) q ≤ (Cutoffs.common (cuts τ)).constant * scale i Z (Z ^ τ) q *
      (1 + Z ^ τ) ^ budgetExponent (heightful i) (HeightBudget.common budgets).degree := by
  have hbd := HeightBudget.common_dominates budgets i
  have hcd := Cutoffs.common_dominates (cuts τ) i
  have hZtwo : 2 ≤ Z := (Cutoffs.common (cuts τ)).threshold_two.trans hZ
  have hbase : 1 ≤ 1 + Z ^ τ := by
    have hh := Real.rpow_nonneg (by linarith : 0 ≤ Z) τ
    linarith
  have hb := hcomponent i τ hτ (hceiling.trans hbd.2) Z (hcd.1.trans hZ) q
  have hweight := hscale i Z (Z ^ τ) q hZtwo
  have hleft : (cuts τ i).constant * scale i Z (Z ^ τ) q ≤
      (Cutoffs.common (cuts τ)).constant * scale i Z (Z ^ τ) q :=
    mul_le_mul_of_nonneg_right hcd.2 hweight
  have he : budgetExponent (heightful i) (budgets i).degree ≤
      budgetExponent (heightful i) (HeightBudget.common budgets).degree := by
    unfold budgetExponent
    split_ifs
    · exact hbd.1
    · exact le_rfl
  have hright := Real.rpow_le_rpow_of_exponent_le hbase he
  exact hb.trans (mul_le_mul hleft hright
    (Real.rpow_nonneg (by linarith) _)
    (mul_nonneg (Cutoffs.common (cuts τ)).constant_nonneg hweight))

/-- Constants are shared across the entire possibly infinite moving family.
All analytic component estimates remain explicit hypotheses of this
independent finite-merging theorem. -/
theorem finite_simultaneous_indexed_package {n : ℕ}
    (Index : Fin n → ℝ → ℝ → Type*)
    (budgets : Fin n → HeightBudget) (cuts : ℝ → Fin n → Cutoffs)
    (heightful : Fin n → Bool)
    (value scale : (i : Fin n) → (Z T : ℝ) → Index i Z T → ℝ)
    (hscale : ∀ i Z T q, 2 ≤ Z → 0 ≤ scale i Z T q)
    (hcomponent : ∀ i τ, 0 < τ → τ ≤ (budgets i).ceiling →
      ∀ Z, (cuts τ i).threshold ≤ Z → ∀ q : Index i Z (Z ^ τ),
        value i Z (Z ^ τ) q ≤ (cuts τ i).constant * scale i Z (Z ^ τ) q *
          (1 + Z ^ τ) ^ budgetExponent (heightful i) (budgets i).degree) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 2 ≤ Z₀ ∧ 0 ≤ C ∧
        ∀ Z, Z₀ ≤ Z → ∀ i, ∀ q : Index i Z (Z ^ τ),
          value i Z (Z ^ τ) q ≤ C * scale i Z (Z ^ τ) q *
            (1 + Z ^ τ) ^ budgetExponent (heightful i) A := by
  let b := HeightBudget.common budgets
  refine ⟨b.degree, b.ceiling, b.degree_nonneg, b.ceiling_pos, ?_⟩
  intro τ hτ hc
  let c := Cutoffs.common (cuts τ)
  refine ⟨c.threshold, c.constant, c.threshold_two, c.constant_nonneg, ?_⟩
  intro Z hZ i q
  exact finite_simultaneous_indexed_bound Index budgets cuts heightful value scale
    hscale hcomponent τ hτ hc Z hZ i q

end ExpansionInterfaces
