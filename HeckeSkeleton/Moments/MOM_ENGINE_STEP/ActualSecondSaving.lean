import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalFrequency

/-!
# The second saving at the literal original ideal lengths

Every logarithmic length below is computed from the original common
ideals or one of the actual frequency radicals.  On a live row, the
complete local correlations prove the unequal-depth sixth-divisibility
condition.  The equal-depth frequency partition identifies the three
indicators in the scalar ledger with the actual unit, nonunit, and
multiplicity-one nonunit radicals.

Summing that ledger with the logarithmic norm of each original prime
therefore proves the full second saving.  No equal-prime-norm model,
dyadic replacement, or additional saving hypothesis is used.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- On a nonzero complete local correlation, the unit-frequency
alternative is exactly the complement of the actual nonunit alternative
at equal nonprincipal depth. -/
theorem actual_unitFrequencySaving_iff
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R)
    (hne : actualPrimePowerCorrelation C p m n h ≠ 0) :
    unitFrequencySaving C p m n h ↔
      m = n ∧ ¬6 ∣ m ∧ ¬nonunitFrequencySaving C p m n h := by
  constructor
  · intro hu
    exact ⟨hu.1, hu.2.1, unit_nonunit_frequency_disjoint C p m n h hu⟩
  · rintro ⟨heq, hsix, hnot⟩
    subst n
    rcases actual_equal_frequency_partition C p m hsix h hne with hu | hv
    · exact hu
    · exact False.elim (hnot hv)

theorem nonunitFrequencySaving_ledger_iff
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) :
    (m = n ∧ ¬6 ∣ m ∧ nonunitFrequencySaving C p m n h) ↔
      nonunitFrequencySaving C p m n h :=
  ⟨fun hcond => hcond.2.2, fun hv => ⟨hv.1, hv.2.1, hv⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The final local ledger term selects the actual multiplicity-one
nonunit radical, retaining both original multiplicities. -/
theorem multiplicityOneNonunitPrimes_ledger_iff
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) (i : ι) :
    (m i = n i ∧ m i = 1 ∧ nonunitFrequencySaving C (p i) (m i) (n i) h) ↔
      i ∈ multiplicityOneNonunitPrimes C p m n h := by
  constructor
  · rintro ⟨heq, hm, hv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hm, heq.symm.trans hm, hv⟩
  · intro hi
    obtain ⟨hm, hn, hv⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨hm.trans hn.symm, hm, hv⟩

/-- The literal prime-power product has its actual logarithmic prime
weights, with no approximation of distinct prime norms. -/
theorem idealLogLength_primePowerProduct (Z : ℝ)
    (p : ι → ExteriorPrime A) (n : ι → ℕ) :
    idealLogLength Z (primePowerProduct p n).val =
      ∑ i, idealLogLength Z (p i).val.asIdeal * (n i : ℝ) := by
  exact idealLogLength_powerProduct Z Finset.univ
    (fun i => (p i).val.asIdeal) n (fun i _ => (p i).val.prime.ne_zero)

theorem idealLogLength_primePowerIndicator (Z : ℝ)
    (p : ι → ExteriorPrime A) (P : ι → Prop) [DecidablePred P] :
    idealLogLength Z (primePowerProduct p (fun i => if P i then 1 else 0)).val =
      ∑ i, if P i then idealLogLength Z (p i).val.asIdeal else 0 := by
  rw [idealLogLength_primePowerProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P i <;> simp only [hi, if_true, if_false, Nat.cast_one,
    Nat.cast_zero, mul_one, mul_zero]

/-- Positive original multiplicities identify both supports with the
same actual prime list.  Their common radical contains each prime once. -/
theorem commonRadical_primePowerProduct
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    commonRadical (primePowerProduct p m).val (primePowerProduct p n).val =
      ∏ i, (p i).val.asIdeal := by
  rw [commonRadical, primePowerProduct_support p hp m hm,
    primePowerProduct_support p hp n hn, Finset.inter_self,
    Finset.prod_image (primePowerProduct_prime_injective p hp).injOn]

theorem idealLogLength_commonRadical_primePowerProduct (Z : ℝ)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    idealLogLength Z
        (commonRadical (primePowerProduct p m).val (primePowerProduct p n).val) =
      ∑ i, idealLogLength Z (p i).val.asIdeal := by
  rw [commonRadical_primePowerProduct p hp m n hm hn]
  exact idealLogLength_prod Z Finset.univ
    (fun i => (p i).val.asIdeal) (fun i _ => (p i).val.prime.ne_zero)

theorem idealLogLength_gcd_primePowerProduct (Z : ℝ)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) :
    idealLogLength Z (gcd (primePowerProduct p m).val (primePowerProduct p n).val) =
      ∑ i, idealLogLength Z (p i).val.asIdeal * (min (m i) (n i) : ℝ) := by
  rw [← primePowerProduct_min_eq_gcd p hp m n]
  simpa only [Nat.cast_min] using
    idealLogLength_primePowerProduct Z p (fun i => min (m i) (n i))

theorem idealLogLength_unitFrequencyRadical
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) :
    idealLogLength Z (unitFrequencyRadical C p m n h).val =
      ∑ i, if unitFrequencySaving C (p i) (m i) (n i) h then
        idealLogLength Z (p i).val.asIdeal else 0 :=
  idealLogLength_primePowerIndicator Z p (fun i => unitFrequencySaving C (p i) (m i) (n i) h)

theorem idealLogLength_nonunitFrequencyRadical
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) :
    idealLogLength Z (nonunitFrequencyRadical C p m n h).val =
      ∑ i, if nonunitFrequencySaving C (p i) (m i) (n i) h then
        idealLogLength Z (p i).val.asIdeal else 0 :=
  idealLogLength_primePowerIndicator Z p (fun i => nonunitFrequencySaving C (p i) (m i) (n i) h)

theorem idealLogLength_multiplicityOneNonunitRadical
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) :
    idealLogLength Z (multiplicityOneNonunitRadical C p m n h).val =
      ∑ i, if i ∈ multiplicityOneNonunitPrimes C p m n h then
        idealLogLength Z (p i).val.asIdeal else 0 :=
  idealLogLength_primePowerIndicator Z p (fun i => i ∈ multiplicityOneNonunitPrimes C p m n h)

/-- The local scalar expression has exactly the three actual frequency
indicators.  The final coefficient is written as `2 / 6`, matching the
two copies paid by the multiplicity-one nonunit base factor. -/
theorem actual_secondLocalSaving_identity
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) (i : ι) (w : ℝ)
    (hne : actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    w * secondLocalSaving (m i) (n i)
        (nonunitFrequencySaving C (p i) (m i) (n i) h) =
      w * (m i : ℝ) + w * (n i : ℝ) - 5 * (w * (min (m i) (n i) : ℝ)) / 6 - w +
        (if unitFrequencySaving C (p i) (m i) (n i) h then w else 0) +
        (if nonunitFrequencySaving C (p i) (m i) (n i) h then w else 0) / 6 +
        2 * (if i ∈ multiplicityOneNonunitPrimes C p m n h then w else 0) / 6 := by
  unfold secondLocalSaving
  simp only [← actual_unitFrequencySaving_iff C (p i) (m i) (n i) h hne,
    nonunitFrequencySaving_ledger_iff C (p i) (m i) (n i) h,
    multiplicityOneNonunitPrimes_ledger_iff C p m n h i]
  split_ifs <;> ring

private theorem actual_secondSaving_sum_identity
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) (w : ι → ℝ)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    (∑ i, w i * secondLocalSaving (m i) (n i)
      (nonunitFrequencySaving C (p i) (m i) (n i) h)) =
      (∑ i, w i * (m i : ℝ)) + (∑ i, w i * (n i : ℝ)) -
        5 * (∑ i, w i * (min (m i) (n i) : ℝ)) / 6 - (∑ i, w i) +
        (∑ i, if unitFrequencySaving C (p i) (m i) (n i) h then w i else 0) +
        (∑ i, if nonunitFrequencySaving C (p i) (m i) (n i) h then w i else 0) / 6 +
        2 * (∑ i, if i ∈ multiplicityOneNonunitPrimes C p m n h then w i else 0) / 6 := by
  have hlocal (i : ι) := actual_secondLocalSaving_identity C p m n h i (w i) (hne i)
  simp_rw [hlocal]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum]

/-- The genuine second saving at the exact original norms, from the
nonvanishing of the actual complete local factors. -/
theorem actual_second_saving_of_local_nonzero
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (h : A.R)
    (hne : ∀ i, actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0) :
    let b₂ := (idealLogLength Z (primePowerProduct p m).val +
      idealLogLength Z (primePowerProduct p n).val) / 2
    let g₂ := idealLogLength Z (gcd (primePowerProduct p m).val (primePowerProduct p n).val)
    let p₂ := idealLogLength Z
      (commonRadical (primePowerProduct p m).val (primePowerProduct p n).val)
    let t₂ := idealLogLength Z (unitFrequencyRadical C p m n h).val
    let V := idealLogLength Z (nonunitFrequencyRadical C p m n h).val
    let v₁ := idealLogLength Z (multiplicityOneNonunitRadical C p m n h).val
    2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V / 6 + 2 * v₁ / 6 := by
  let w : ι → ℝ := fun i => idealLogLength Z (p i).val.asIdeal
  have hweighted := weighted_secondSaving_lower Finset.univ w m n
    (fun i => nonunitFrequencySaving C (p i) (m i) (n i) h)
    (fun i _ => idealLogLength_nonneg Z hZ (p i).val.asIdeal (p i).val.prime.ne_zero)
    (fun i _ => hm i) (fun i _ => hn i)
    (fun i _ hneq => actualPrimePowerCorrelation_six_of_ne C (p i) (m i) (n i)
      h (hm i) (hn i) hneq (hne i))
  rw [actual_secondSaving_sum_identity C p m n h w hne] at hweighted
  dsimp only [w] at hweighted
  dsimp only
  rw [idealLogLength_primePowerProduct Z p m, idealLogLength_primePowerProduct Z p n,
    idealLogLength_gcd_primePowerProduct Z p hp m n,
    idealLogLength_commonRadical_primePowerProduct Z p hp m n hm hn,
    idealLogLength_unitFrequencyRadical C Z p m n h,
    idealLogLength_nonunitFrequencyRadical C Z p m n h,
    idealLogLength_multiplicityOneNonunitRadical C Z p m n h]
  linarith

/-- Arbitrary source generators supply all local nonvanishing premises
by the proved complete-correlation norm identity. -/
theorem actual_second_saving_of_generates
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m)
      (primePowerProduct p n) a b ha hb h ≠ 0) :
    let b₂ := (idealLogLength Z (primePowerProduct p m).val +
      idealLogLength Z (primePowerProduct p n).val) / 2
    let g₂ := idealLogLength Z (gcd (primePowerProduct p m).val (primePowerProduct p n).val)
    let p₂ := idealLogLength Z
      (commonRadical (primePowerProduct p m).val (primePowerProduct p n).val)
    let t₂ := idealLogLength Z (unitFrequencyRadical C p m n h).val
    let V := idealLogLength Z (nonunitFrequencyRadical C p m n h).val
    let v₁ := idealLogLength Z (multiplicityOneNonunitRadical C p m n h).val
    2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V / 6 + 2 * v₁ / 6 :=
  actual_second_saving_of_local_nonzero C Z hZ p hp m n hm hn h
    (actual_product_correlation_nonzero_local_of_generates C p hp m n a b ha hb h hne)

namespace ActualSecondCorrelationRows

variable {H : Type*} (R : ActualSecondCorrelationRows A σ H ι)

/-- Every original live row satisfies the full second-saving ledger at
its literal common ideals and actual three frequency radicals.  The
positive multiplicities are the original common-support conditions. -/
theorem live_second_saving
    (C : A.GeneralArithmeticContext σ η hS) (Z : ℝ) (hZ : 1 < Z)
    (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i)
    (h : R.live) :
    let left := (primePowerProduct R.primes R.leftMultiplicity).val
    let right := (primePowerProduct R.primes R.rightMultiplicity).val
    let b₂ := (idealLogLength Z left + idealLogLength Z right) / 2
    let g₂ := idealLogLength Z (gcd left right)
    let p₂ := idealLogLength Z (commonRadical left right)
    let t₂ := idealLogLength Z (unitFrequencyRadical C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val)).val
    let V := idealLogLength Z (nonunitFrequencyRadical C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val)).val
    let v₁ := idealLogLength Z (multiplicityOneNonunitRadical C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h.val)).val
    2 * b₂ / 3 ≤ 2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V / 6 + 2 * v₁ / 6 :=
  actual_second_saving_of_local_nonzero C Z hZ R.primes R.primes_injective
    R.leftMultiplicity R.rightMultiplicity hm hn (R.frequency h.val)
    (R.live_local_correlation_nonzero C h)

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_saving_of_local_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_saving_of_generates
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.live_second_saving
