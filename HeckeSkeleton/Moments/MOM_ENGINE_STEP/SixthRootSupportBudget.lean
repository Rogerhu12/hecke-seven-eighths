import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualMovingFrequencyFactors

/-!
# Paying the complete second sixth-root support

The sixth-power extraction leaves a coprimality mask for the complete
sixth-root ideal.  That ideal need not divide the old mask times the
unit and nonunit frequency radicals.  Its norm must therefore remain
in the support budget.

At every original common prime the multiplicities are positive, and
`1 + min(m,n) / 6 ≤ min(m,n)`.  Consequently the common radical times
the complete sixth-root ideal divides each original common ideal.
The actual unit-frequency radical has exponent at most one, so its
product with the same root divides the original gcd as well.

The resulting logarithmic inequalities pay the full root, including
all its prime-power multiplicities.  They hold for every frequency;
neither a live-row assumption nor any final geometry or mass bound is
needed.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- One copy of an original common prime and its complete sixth-root
exponent fit inside the original minimum multiplicity. -/
theorem secondSixthRootBudget_exponent (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    1 + min m n / 6 ≤ min m n := by
  have hmin : 0 < min m n := lt_min hm hn
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sixthRootBudget_product_dvd_of_le
    (p : ι → ExteriorPrime A) (a b : ι → ℕ) (hab : ∀ i, a i ≤ b i) :
    (primePowerProduct p a).val ∣ (primePowerProduct p b).val :=
  Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow _ (hab i))

theorem secondSixthRootIdeal_dvd_gcd
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    (secondSixthRootIdeal p m n).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  exact dvd_trans
    (sixthRootBudget_product_dvd_of_le p _ _ (fun i => Nat.div_le_self _ _))
    (primePowerProduct_min_dvd_gcd p m n)

/-- The unit indicator costs at most one additional copy of each
original prime.  All sixth-root multiplicities are retained. -/
theorem unitFrequencyRadical_mul_secondSixthRootIdeal_dvd_gcd
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R) :
    (unitFrequencyRadical C p m n h).val * (secondSixthRootIdeal p m n).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  unfold unitFrequencyRadical secondSixthRootIdeal
  rw [← primePowerProduct_add]
  refine dvd_trans (sixthRootBudget_product_dvd_of_le p _ _ ?_)
    (primePowerProduct_min_dvd_gcd p m n)
  intro i
  have hi := secondSixthRootBudget_exponent (m i) (n i) (hm i) (hn i)
  split_ifs <;> omega

/-- A stronger support budget: the entire common radical, together
with the complete sixth root, divides the actual gcd. -/
theorem commonRadical_mul_secondSixthRootIdeal_dvd_gcd
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val *
        (secondSixthRootIdeal p m n).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  rw [commonRadical_primePowerProduct p hp m n hm hn]
  have hone : (∏ i, (p i).val.asIdeal) =
      (primePowerProduct p (fun _ => 1)).val := by
    change (∏ i, (p i).val.asIdeal) = ∏ i, (p i).val.asIdeal ^ 1
    simp only [pow_one]
  rw [hone, secondSixthRootIdeal, ← primePowerProduct_add]
  exact dvd_trans
    (sixthRootBudget_product_dvd_of_le p _ _
      (fun i => secondSixthRootBudget_exponent (m i) (n i) (hm i) (hn i)))
    (primePowerProduct_min_dvd_gcd p m n)

theorem commonRadical_mul_secondSixthRootIdeal_dvd_left
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val *
        (secondSixthRootIdeal p m n).val ∣ (primePowerProduct p m).val :=
  dvd_trans (commonRadical_mul_secondSixthRootIdeal_dvd_gcd p hp m n hm hn)
    (gcd_dvd_left _ _)

theorem commonRadical_mul_secondSixthRootIdeal_dvd_right
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val *
        (secondSixthRootIdeal p m n).val ∣ (primePowerProduct p n).val :=
  dvd_trans (commonRadical_mul_secondSixthRootIdeal_dvd_gcd p hp m n hm hn)
    (gcd_dvd_right _ _)

/-- The support estimate pays the product of the two actual norms,
rather than replacing the sixth root by its radical. -/
theorem unitFrequencyRadical_mul_secondSixthRootIdeal_norm_le
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R) :
    A.exteriorNorm (unitFrequencyRadical C p m n h) *
        A.exteriorNorm (secondSixthRootIdeal p m n) ≤
      (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) := by
  simpa only [map_mul, Nat.cast_mul] using
    ideal_norm_le_of_dvd (gcd_ne_zero_of_left (primePowerProduct p m).property.1)
      (unitFrequencyRadical_mul_secondSixthRootIdeal_dvd_gcd C p m n hm hn h)

theorem commonRadical_mul_secondSixthRootIdeal_norm_le
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    (Ideal.absNorm (commonRadical (primePowerProduct p m).val
        (primePowerProduct p n).val) : ℝ) *
        A.exteriorNorm (secondSixthRootIdeal p m n) ≤
      min (A.exteriorNorm (primePowerProduct p m))
        (A.exteriorNorm (primePowerProduct p n)) := by
  apply le_min
  · simpa only [map_mul, Nat.cast_mul] using
      ideal_norm_le_of_dvd (primePowerProduct p m).property.1
        (commonRadical_mul_secondSixthRootIdeal_dvd_left p hp m n hm hn)
  · simpa only [map_mul, Nat.cast_mul] using
      ideal_norm_le_of_dvd (primePowerProduct p n).property.1
        (commonRadical_mul_secondSixthRootIdeal_dvd_right p hp m n hm hn)

private theorem sixthRootBudget_log_mul (Z : ℝ) (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealLogLength Z (I * J) = idealLogLength Z I + idealLogLength Z J := by
  have hi : (Ideal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj : (Ideal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul hi hj]
  ring

private theorem sixthRootBudget_log_le_of_dvd (Z : ℝ) (hZ : 1 < Z)
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) (hd : I ∣ J) :
    idealLogLength Z I ≤ idealLogLength Z J := by
  have hi : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  exact div_le_div_of_nonneg_right
    (Real.log_le_log hi (ideal_norm_le_of_dvd hJ hd)) (Real.log_pos hZ).le

theorem secondSixthRootIdeal_logLength_nonneg (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    0 ≤ idealLogLength Z (secondSixthRootIdeal p m n).val :=
  idealLogLength_nonneg Z hZ _ (secondSixthRootIdeal p m n).property.1

/-- The exact `t₂ + r₆ ≤ g₂` slack, with the full original root norm. -/
theorem secondSixthRoot_unit_log_slack
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R) :
    idealLogLength Z (unitFrequencyRadical C p m n h).val +
        idealLogLength Z (secondSixthRootIdeal p m n).val ≤
      idealLogLength Z (gcd (primePowerProduct p m).val (primePowerProduct p n).val) := by
  rw [← sixthRootBudget_log_mul Z _ _ (unitFrequencyRadical C p m n h).property.1
    (secondSixthRootIdeal p m n).property.1]
  exact sixthRootBudget_log_le_of_dvd Z hZ _ _
    (mul_ne_zero (unitFrequencyRadical C p m n h).property.1
      (secondSixthRootIdeal p m n).property.1)
    (gcd_ne_zero_of_left (primePowerProduct p m).property.1)
    (unitFrequencyRadical_mul_secondSixthRootIdeal_dvd_gcd C p m n hm hn h)

/-- Each of the original left and right common lengths separately
pays the common radical and the complete sixth-root length. -/
theorem secondSixthRoot_common_log_slack
    (Z : ℝ) (hZ : 1 < Z) (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    idealLogLength Z (commonRadical (primePowerProduct p m).val
        (primePowerProduct p n).val) +
        idealLogLength Z (secondSixthRootIdeal p m n).val ≤
      min (idealLogLength Z (primePowerProduct p m).val)
        (idealLogLength Z (primePowerProduct p n).val) := by
  rw [← sixthRootBudget_log_mul Z _ _ (commonRadical_ne_zero _ _)
    (secondSixthRootIdeal p m n).property.1]
  have hprod := mul_ne_zero (commonRadical_ne_zero
    (primePowerProduct p m).val (primePowerProduct p n).val)
    (secondSixthRootIdeal p m n).property.1
  exact le_min
    (sixthRootBudget_log_le_of_dvd Z hZ _ _ hprod (primePowerProduct p m).property.1
      (commonRadical_mul_secondSixthRootIdeal_dvd_left p hp m n hm hn))
    (sixthRootBudget_log_le_of_dvd Z hZ _ _ hprod (primePowerProduct p n).property.1
      (commonRadical_mul_secondSixthRootIdeal_dvd_right p hp m n hm hn))

/-- The exact `p₂ + r₆ ≤ (c₂ + d₂) / 2` slack used by the joint
width ledger.  No rounded or reselected child length enters it. -/
theorem secondSixthRoot_common_log_slack_mean
    (Z : ℝ) (hZ : 1 < Z) (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    idealLogLength Z (commonRadical (primePowerProduct p m).val
        (primePowerProduct p n).val) +
        idealLogLength Z (secondSixthRootIdeal p m n).val ≤
      (idealLogLength Z (primePowerProduct p m).val +
        idealLogLength Z (primePowerProduct p n).val) / 2 := by
  have hboth := secondSixthRoot_common_log_slack Z hZ p hp m n hm hn
  have hleft := hboth.trans (min_le_left _ _)
  have hright := hboth.trans (min_le_right _ _)
  linarith

namespace ActualSecondCorrelationRows

variable {H : Type*} (R : ActualSecondCorrelationRows A σ H ι)

/-- The same complete root is paid on every original frequency row.
This directly supplies the two scalar slacks without assuming either
an enlarged old-mask window or a descendant geometry inequality. -/
theorem sixthRoot_log_budget
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i)
    (h : H) :
    let left := (primePowerProduct R.primes R.leftMultiplicity).val
    let right := (primePowerProduct R.primes R.rightMultiplicity).val
    let b₂ := (idealLogLength Z left + idealLogLength Z right) / 2
    let g₂ := idealLogLength Z (gcd left right)
    let p₂ := idealLogLength Z (commonRadical left right)
    let t₂ := idealLogLength Z (unitFrequencyRadical C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h)).val
    let r₆ := idealLogLength Z
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
    0 ≤ r₆ ∧ t₂ + r₆ ≤ g₂ ∧ p₂ + r₆ ≤ b₂ := by
  dsimp only
  exact ⟨secondSixthRootIdeal_logLength_nonneg Z hZ R.primes _ _,
    secondSixthRoot_unit_log_slack C Z hZ R.primes _ _ hm hn (R.frequency h),
    secondSixthRoot_common_log_slack_mean Z hZ R.primes R.primes_injective _ _ hm hn⟩

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.unitFrequencyRadical_mul_secondSixthRootIdeal_dvd_gcd
#print axioms HeckeSkeleton.Moments.EngineStep.commonRadical_mul_secondSixthRootIdeal_dvd_gcd
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.sixthRoot_log_budget
