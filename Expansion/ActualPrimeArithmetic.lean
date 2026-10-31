import Expansion.ActualPrimeLogSeries
import ExpansionInterfaces.LogDividedAnnularProfile
import HeckeGeneral.Analysis.FrequencyRowCounting
import PrimeCancellationPrimeSeries
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual prime arithmetic and exact removal of the logarithmic weight

The linear prime count is derived by injection into the genuine finite
ideal norm window. Every character coefficient retains its actual ramified
zeros. The literal finite log-divided polynomial is identified with the
proved prime-plus-positive-power-tail series, with no kernel/slot character
identification assumed.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Physical
open ExpansionInterfaces.Mellin PrimeCancellationPrimeSeries
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

def actualPrimeNorm (p : HeightOneSpectrum (𝓞 K)) : ℝ := (Ideal.absNorm p.asIdeal : ℝ)

theorem actualPrimeNorm_ge_two (p : HeightOneSpectrum (𝓞 K)) :
    2 ≤ actualPrimeNorm K p := by
  have hp : 2 ≤ Ideal.absNorm p.asIdeal := one_lt_primeIdeal_absNorm K p
  change (2 : ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ)
  exact_mod_cast hp

/-- One genuine count constant works before every unitary character. -/
theorem exists_actualPrimeArithmetic :
    ∃ d : ℝ, 0 < d ∧ ∀ χ : HeckeCharacter K,
      PrimeArithmetic (actualPrimeNorm K) (primeCoefficient K χ) d := by
  obtain ⟨d, hd, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨d, hd, ?_⟩
  intro χ
  refine ⟨hd.le, actualPrimeNorm_ge_two K, ?_, norm_primeCoefficient_le_one K χ⟩
  intro pool Y hY0
  by_cases hY : 1 ≤ Y
  · have hsub : (pool.filter (fun p => actualPrimeNorm K p ≤ Y)).image
        (primeNonzeroIdeal K) ⊆ dyadicIdealSupport K (Y / 2) := by
      intro I hI
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
      apply (mem_dyadicIdealSupport_iff K (by positivity) _).mpr
      change actualPrimeNorm K p ≤ 2 * (Y / 2)
      have hn := (Finset.mem_filter.mp hp).2
      linarith
    have hc : (pool.filter (fun p => actualPrimeNorm K p ≤ Y)).card ≤
        (dyadicIdealSupport K (Y / 2)).card := by
      calc
        _ = ((pool.filter (fun p => actualPrimeNorm K p ≤ Y)).image
            (primeNonzeroIdeal K)).card :=
          (Finset.card_image_of_injective _ (primeNonzeroIdeal_injective K)).symm
        _ ≤ _ := Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hc).trans (hcount Y hY)
  · have he : pool.filter (fun p => actualPrimeNorm K p ≤ Y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hn := (Finset.mem_filter.mp hp).2
      linarith [actualPrimeNorm_ge_two K p]
    rw [he]
    simpa only [Finset.card_empty, Nat.cast_zero] using mul_nonneg hd.le hY0

/-- Compact smooth support supplies the prime-power window bound itself. -/
theorem exists_actualPrimeWindowBound (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ M : ℝ, 0 < M ∧ WindowBound W M := by
  have hc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hW.continuous
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  exact ⟨(zero_le_one.trans (le_max_left _ _)), hs,
    fun x => (hB x).trans (le_max_right _ _)⟩

/-- At zero center frequency the actual finite Mellin term is precisely
 the existing log-weighted positive prime-power term. -/
theorem actual_logDivided_term_eq (χ : HeckeCharacter K) (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hs : Function.support W ⊆ Icc (1 : ℝ) 2)
    (P : ℝ) (hP : 2 ≤ P) (np : ActualPrimeLogIndex K) :
    smoothedTerm (logDividedAnnularProfile W hW hs P hP)
      (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K) (vertical 0 0) P np =
      logWeightedPowerTerm (actualPrimeNorm K) (primeCoefficient K χ) W P np.1 np.2 := by
  simp only [smoothedTerm, logDividedAnnularProfile, vertical, Complex.ofReal_zero,
    zero_mul, zero_add, neg_zero, Complex.cpow_zero, mul_one,
    actualPrimeLogCoefficient, actualPrimePowerNorm_eq, logWeightedPowerTerm, actualPrimeNorm]

/-- The literal finite support is enough for an exact total-series identity;
all omitted terms vanish by the same physical profile support. -/
theorem actual_logDivided_finite_sum_eq_weightedSum (χ : HeckeCharacter K)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (P : ℝ) (hP : 2 ≤ P) :
    (∑ np ∈ actualPrimeLogWindow K (2 * P),
      smoothedTerm (logDividedAnnularProfile W hW hs P hP)
        (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K) (vertical 0 0) P np) =
      weightedSum (actualPrimeNorm K) (primeCoefficient K χ) W P := by
  have hPpos : 0 < P := by linarith
  calc
    _ = ∑ np ∈ actualPrimeLogWindow K (2 * P),
        logWeightedPowerTerm (actualPrimeNorm K) (primeCoefficient K χ) W P np.1 np.2 :=
      Finset.sum_congr rfl (fun np _ => actual_logDivided_term_eq K χ W hW hs P hP np)
    _ = _ := by
      symm
      unfold weightedSum
      apply tsum_eq_sum
      intro np hnp
      have hz : W (actualPrimePowerNorm K np / P) = 0 := by
        by_contra hn
        have hN : actualPrimePowerNorm K np ≤ 2 * P :=
          (div_le_iff₀ hPpos).mp (hs hn).2
        exact hnp (mem_actualPrimeLogWindow_of_le K (2 * P) np hN)
      have hz' : W (actualPrimeNorm K np.2 ^ (np.1 + 1) / P) = 0 := by
        simpa only [actualPrimePowerNorm_eq, actualPrimeNorm] using hz
      simp only [logWeightedPowerTerm, PrimeCancellationLogWindow.logWindow,
        hz', zero_div, mul_zero]

/-- The exact finite log-divided polynomial splits into actual primes and
higher prime powers; arithmetic and summability are proved above. -/
theorem actual_logDivided_finite_sum_eq_primeSum_add_tailSum (χ : HeckeCharacter K)
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (P : ℝ) (hP : 2 ≤ P) :
    (∑ np ∈ actualPrimeLogWindow K (2 * P),
      smoothedTerm (logDividedAnnularProfile W hW hs P hP)
        (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K) (vertical 0 0) P np) =
      primeSum (actualPrimeNorm K) (primeCoefficient K χ) W P +
        tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P := by
  rw [actual_logDivided_finite_sum_eq_weightedSum K χ W hW hs P hP]
  obtain ⟨d, hd, hA⟩ := exists_actualPrimeArithmetic K
  obtain ⟨M, hM, hWin⟩ := exists_actualPrimeWindowBound W hW hs
  exact weightedSum_eq_primeSum_add_tailSum (actualPrimeNorm K) (primeCoefficient K χ)
    W d M P (by linarith) (hA χ) hWin

/-- A constant fixed by K and W controls the actual higher-prime-power tail
for every character and every positive scale. -/
theorem exists_actual_primePower_tail_bound (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (P : ℝ), 0 < P →
      ‖tailSum (actualPrimeNorm K) (primeCoefficient K χ) W P‖ ≤ C * Real.sqrt P := by
  obtain ⟨d, hd, hA⟩ := exists_actualPrimeArithmetic K
  obtain ⟨M, hM, hWin⟩ := exists_actualPrimeWindowBound W hW hs
  refine ⟨M * d * (1 + Real.sqrt 2), by positivity, ?_⟩
  intro χ P hP
  exact norm_tailSum_le (actualPrimeNorm K) (primeCoefficient K χ) W d M P hP (hA χ) hWin

end Expansion.Project

#print axioms Expansion.Project.exists_actualPrimeArithmetic
#print axioms Expansion.Project.actual_logDivided_finite_sum_eq_weightedSum
#print axioms Expansion.Project.actual_logDivided_finite_sum_eq_primeSum_add_tailSum
#print axioms Expansion.Project.exists_actual_primePower_tail_bound
