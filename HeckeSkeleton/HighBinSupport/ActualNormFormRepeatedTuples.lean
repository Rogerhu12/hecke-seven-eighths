import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeDeficit
import HeckeSkeleton.HighBinSupport.HighNormFormTuple
import HeckeSkeleton.HighBinSupport.ActualNormFormHigherPrimePowers
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Repeated-prime slots in the actual disjoint prime windows.

The finite tuple set below is defined from the original `primeWindow`
and the prime exponents of the actual frequency ideal. Its cardinality
costs an arbitrarily small power of the row norm. The radical deficit is
used separately for every tuple before the sum is estimated; neither an
ideal count for the row family nor a prime ideal theorem enters.
-/

noncomputable section
namespace HighBinVerified.NormFormActual

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem actual_primeSupport_card_growth (I : NonzeroIdeal K) :
    (2 : ℝ) ^ (primeExponents I).support.card ≤ idealNorm K I := by
  rw [actual_idealNorm_eq_primeSupport_product]
  apply NormForm.two_pow_support_card_le
  · intro p hp
    exact_mod_cast one_lt_primeIdeal_absNorm K p
  · intro p hp
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

def repeatedTupleConstant (J : ℕ) (eps : ℝ) : ℝ :=
  ((Nat.factorial J : ℝ) / (eps * Real.log 2) ^ J) * (2 : ℝ) ^ eps

theorem repeatedTupleConstant_pos (J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    0 < repeatedTupleConstant J eps := by
  have hf : (0 : ℝ) < (Nat.factorial J : ℝ) := by exact_mod_cast Nat.factorial_pos J
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos (div_pos hf (pow_pos (mul_pos heps hl) J))
    (Real.rpow_pos_of_pos (by norm_num) eps)

theorem actual_support_tuple_count_subpower (I : NonzeroIdeal K)
    (J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    (((primeExponents I).support.card : ℝ) + 1) ^ J ≤
      repeatedTupleConstant J eps * idealNorm K I ^ eps :=
  NormForm.support_tuple_count_subpower (idealNorm K I)
    (primeExponents I).support.card J eps heps (actual_primeSupport_card_growth K I)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The original window with the actual repeated-row-prime condition. -/
def repeatedPrimeWindow (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots) :
    Finset (ExteriorPrime K S) :=
  (primeWindow K S g T Z i).filter (fun p => 2 ≤ primeExponents u.ideal.val p.val)

/-- Only the specified repeated slots are indexed. Empty selected sets
produce the unique empty tuple, as required by the full subset expansion. -/
def repeatedPrimeTuples (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots)) :
    Finset (J → ExteriorPrime K S) :=
  Fintype.piFinset (fun i : J => repeatedPrimeWindow K S u g T Z i.val)

theorem repeatedPrimeWindow_card_le (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots) :
    (repeatedPrimeWindow K S u g T Z i).card ≤ (primeExponents u.ideal.val).support.card := by
  have hsub : (repeatedPrimeWindow K S u g T Z i).image Subtype.val ⊆
      (primeExponents u.ideal.val).support := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hr := (Finset.mem_filter.mp hq).2
    exact Finsupp.mem_support_iff.mpr (by omega)
  calc
    _ = ((repeatedPrimeWindow K S u g T Z i).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem repeatedPrimeTuples_card_le (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots)) :
    (repeatedPrimeTuples K S u g T Z J).card ≤
      ((primeExponents u.ideal.val).support.card + 1) ^ J.card := by
  unfold repeatedPrimeTuples
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : J, ((primeExponents u.ideal.val).support.card + 1) := by
      apply Finset.prod_le_prod
      intro i hi
      exact (repeatedPrimeWindow_card_le K S u g T Z i.val).trans (Nat.le_succ _)
    _ = _ := by simp

theorem repeatedPrimeTuples_card_subpower
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots))
    {eps : ℝ} (heps : 0 < eps) :
    ((repeatedPrimeTuples K S u g T Z J).card : ℝ) ≤
      repeatedTupleConstant J.card eps * frequencyRowNorm K S u ^ eps := by
  have hcard : ((repeatedPrimeTuples K S u g T Z J).card : ℝ) ≤
      ((((primeExponents u.ideal.val).support.card + 1) ^ J.card : ℕ) : ℝ) := by
    exact_mod_cast repeatedPrimeTuples_card_le K S u g T Z J
  have hnorm := actual_support_tuple_count_subpower K u.ideal.val J.card heps
  apply le_trans ?_ hnorm
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hcard

/-- A single repeated slot has the same prime-scale cap as the regular
character term, up to an arbitrarily small row-norm factor. This bound is
used only for the amplitude cap; the sharper tuple allocation below
retains the individual repeated primes in the norm-form estimate. -/
theorem repeatedPrimeWindow_power_sum_le
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots)
    {lam eta : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (heta : 0 < eta)
    (hP : 0 < primeScale g Z) :
    (∑ p ∈ repeatedPrimeWindow K S u g T Z i,
        (p.val.asIdeal.absNorm : ℝ) ^ lam) ≤
      (2 * repeatedTupleConstant 1 eta) * frequencyRowNorm K S u ^ eta *
        (primeScale g Z) ^ lam := by
  let F := repeatedPrimeWindow K S u g T Z i
  have hcard : (F.card : ℝ) ≤ repeatedTupleConstant 1 eta * frequencyRowNorm K S u ^ eta := by
    have hc : (F.card : ℝ) ≤ ((primeExponents u.ideal.val).support.card : ℝ) := by
      exact_mod_cast repeatedPrimeWindow_card_le K S u g T Z i
    have ht := actual_support_tuple_count_subpower K u.ideal.val 1 heta
    simp only [pow_one] at ht
    exact hc.trans ((le_add_of_nonneg_right zero_le_one).trans ht)
  have htwo : (2 : ℝ) ^ lam ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlam1
  have hp : ∀ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ lam ≤ 2 * (primeScale g Z) ^ lam := by
    intro p hp
    have hnorm := actual_primeWindow_norm_range K S g T Z i p (Finset.mem_filter.mp hp).1
    calc
      _ ≤ (2 * primeScale g Z) ^ lam :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm.2.2.le hlam
      _ = (2 : ℝ) ^ lam * (primeScale g Z) ^ lam := Real.mul_rpow (by norm_num) hP.le
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hP.le _)
  change (∑ p ∈ F, (p.val.asIdeal.absNorm : ℝ) ^ lam) ≤ _
  calc
    _ ≤ ∑ _p ∈ F, 2 * (primeScale g Z) ^ lam := Finset.sum_le_sum hp
    _ = (F.card : ℝ) * (2 * (primeScale g Z) ^ lam) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (repeatedTupleConstant 1 eta * frequencyRowNorm K S u ^ eta) *
        (2 * (primeScale g Z) ^ lam) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem repeatedPrimeTuple_injective
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots))
    (p : J → ExteriorPrime K S) (hp : p ∈ repeatedPrimeTuples K S u g T Z J) :
    Function.Injective (fun i => (p i).val) := by
  intro i j heq
  apply Subtype.ext
  by_contra hij
  have hd := actual_primeWindows_disjoint K S g T Z i.val j.val hij
  have hi := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).1
  have hj := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp j)).1
  have hpij : p i = p j := Subtype.ext heq
  exact Finset.disjoint_left.mp hd hi (hpij.symm ▸ hj)

/-- Exact allocation for each actual tuple. Distinctness is derived from
the original disjoint smooth windows, not supplied as an extra premise. -/
theorem repeatedPrimeTuple_conductor_allocation
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots))
    (p : J → ExteriorPrime K S) (hp : p ∈ repeatedPrimeTuples K S u g T Z J) :
    (∏ i : J, ((p i).val.asIdeal.absNorm : ℝ)) *
      (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S u := by
  let selected := (Finset.univ : Finset J).image (fun i => (p i).val)
  have hr : ∀ q ∈ selected, 2 ≤ primeExponents u.ideal.val q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  have hprod : (∏ q ∈ selected, (q.asIdeal.absNorm : ℝ)) =
      ∏ i : J, ((p i).val.asIdeal.absNorm : ℝ) :=
    Finset.prod_image (repeatedPrimeTuple_injective K S u g T Z J p hp).injOn
  have h := actual_selected_repeated_product_mul_radicalNorm_le K u.ideal.val selected hr
  rwa [hprod] at h

/-- A complete sum over the literal repeated-prime choices, with the
radical factor absorbed before summation. The fixed explicit constant is
independent of rows, Z, heights, characters and local term values. -/
theorem repeatedPrimeTuple_sum_with_conductor_bound
    (u : FrequencyRow K S) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots))
    (term : (J → ExteriorPrime K S) → ℂ) (C lam eps : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (heps : 0 < eps)
    (hterm : ∀ p ∈ repeatedPrimeTuples K S u g T Z J,
      ‖term p‖ ≤ C * (∏ i : J, ((p i).val.asIdeal.absNorm : ℝ)) ^ lam) :
    (u.ideal.val.val.radical.absNorm : ℝ) ^ lam *
      ‖∑ p ∈ repeatedPrimeTuples K S u g T Z J, term p‖ ≤
        (C * repeatedTupleConstant J.card eps) * frequencyRowNorm K S u ^ (lam + eps) := by
  have hN : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hsum := NormForm.repeated_tuple_sum_bound
    (repeatedPrimeTuples K S u g T Z J) term
    (fun p => ∏ i : J, ((p i).val.asIdeal.absNorm : ℝ))
    (frequencyRowNorm K S u) (u.ideal.val.val.radical.absNorm : ℝ) C lam
    hN (Nat.cast_nonneg _) hC hlam
    (fun p hp => Finset.prod_nonneg (fun i hi => Nat.cast_nonneg _))
    (repeatedPrimeTuple_conductor_allocation K S u g T Z J) hterm
  apply hsum.trans
  calc
    _ ≤ C * (repeatedTupleConstant J.card eps * frequencyRowNorm K S u ^ eps) *
        frequencyRowNorm K S u ^ lam := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
      exact mul_le_mul_of_nonneg_left
        (repeatedPrimeTuples_card_subpower K S u g T Z J heps) hC
    _ = _ := by
      rw [Real.rpow_add hN]
      ring

/-- The actual finite family of smooth annular window profiles has a
single fixed norm bound, chosen before scales, rows and heights. -/
theorem exists_primeWindow_profile_norm_bound (g : PrimeWindowGeometry) :
    ∃ M : ℝ, 0 < M ∧ ∀ (i : Fin g.slots) (y : ℝ), ‖(g.weight i).toFun y‖ ≤ M := by
  have hi : ∀ i : Fin g.slots, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, ‖(g.weight i).toFun y‖ ≤ C := by
    intro i
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
      (g.weight i).smooth.continuous.continuousOn
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro y
    by_cases hy : (g.weight i).toFun y = 0
    · simpa only [hy, norm_zero] using le_max_left (0 : ℝ) B
    · have hs := g.support_annular i hy
      exact (hB y ⟨hs.1.le, hs.2.le⟩).trans (le_max_right _ _)
  choose C hC hbound using hi
  have hsum : 0 ≤ ∑ i : Fin g.slots, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨1 + ∑ i : Fin g.slots, C i, by linarith, ?_⟩
  intro i y
  exact (hbound i y).trans ((Finset.single_le_sum (fun j _ => hC j)
    (Finset.mem_univ i)).trans (by linarith))

/-- The actual higher-prime-power error for every original prime window.
All constants precede the character, scale, slot and phase height. The
annular support and profile bound come from the supplied geometry itself. -/
theorem exists_actual_window_higherPower_bound (g : PrimeWindowGeometry)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : HeckeCharacter K) (Z t : ℝ) (i : Fin g.slots),
      0 < Z →
      ‖∑' pn, HigherPrimePowers.heckeHigherAnnularTerm K chi (g.weight i).toFun
        (primeScale g Z) t pn‖ ≤ C * (primeScale g Z) ^ delta := by
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  refine ⟨M * HigherPrimePowers.higherPowerConstant K delta * (2 : ℝ) ^ delta,
    mul_pos (mul_pos hM (HigherPrimePowers.higherPowerConstant_pos K delta))
      (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro chi Z t i hZ
  have hP : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  have h := HigherPrimePowers.hecke_higherAnnular_tsum_le K chi (g.weight i).toFun
    (primeScale g Z) delta t M hP hdelta hM.le (g.support_annular i) (hprofile i)
  calc
    _ ≤ M * HigherPrimePowers.higherPowerConstant K delta * (2 * primeScale g Z) ^ delta := h
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP.le]
      ring

end HighBinVerified.NormFormActual

#print axioms HighBinVerified.NormFormActual.actual_primeSupport_card_growth
#print axioms HighBinVerified.NormFormActual.repeatedPrimeTuples_card_subpower
#print axioms HighBinVerified.NormFormActual.repeatedPrimeWindow_power_sum_le
#print axioms HighBinVerified.NormFormActual.repeatedPrimeTuple_conductor_allocation
#print axioms HighBinVerified.NormFormActual.repeatedPrimeTuple_sum_with_conductor_bound
#print axioms HighBinVerified.NormFormActual.exists_actual_window_higherPower_bound
