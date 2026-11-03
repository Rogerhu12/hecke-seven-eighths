/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeCancellationAux
import PrimeCancellationIdealMask
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic cost of a prime-ideal mask

Distinct height-one primes dividing D have product dividing D.  Applying
any natural-valued multiplicative ideal norm, their count above a threshold
B>1 is at most log(ND)/log(B).  Thus an arbitrary Boolean mask is allowed
only when its deleted primes have this explicitly controlled support.

Using `N = Ideal.absNorm` specializes these theorems to number fields without
relying on the missing Hecke project.  Positivity of N(D) is an explicit input.
-/

noncomputable section
open scoped Classical BigOperators
open IsDedekindDomain

namespace PrimeCancellation.MaskCount

theorem card_le_log_of_prod_le {α : Type*} (s : Finset α) (n : α → ℝ)
    (B D : ℝ) (hB : 1 < B) (hn : ∀ i ∈ s, B ≤ n i)
    (hprod : (∏ i ∈ s, n i) ≤ D) :
    (s.card : ℝ) ≤ Real.log D / Real.log B := by
  have hBpos : 0 < B := zero_lt_one.trans hB
  have hpow : B ^ s.card ≤ D := by
    calc
      B ^ s.card = ∏ _i ∈ s, B := by simp
      _ ≤ ∏ i ∈ s, n i := Finset.prod_le_prod₀ (fun _ _ => hBpos.le) hn
      _ ≤ D := hprod
  have hlog := Real.log_le_log (pow_pos hBpos _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hB)).mpr hlog

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem primeIdeal_prod_dvd (s : Finset (HeightOneSpectrum R)) (D : Ideal R)
    (hdiv : ∀ p ∈ s, p.asIdeal ∣ D) :
    (∏ p ∈ s, p.asIdeal) ∣ D := by
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    change IsCoprime p.asIdeal q.asIdeal
    rw [HeckeSkeleton.PrimeCancellationIdealMask.prime_isCoprime_iff_not_dvd]
    intro h
    exact hpq (HeckeSkeleton.PrimeCancellationIdealMask.prime_eq_of_asIdeal_dvd h)
  · exact hdiv

theorem idealNorm_prod_le (N : Ideal R →*₀ ℕ)
    (s : Finset (HeightOneSpectrum R)) (D : Ideal R)
    (hD : 0 < N D) (hdiv : ∀ p ∈ s, p.asIdeal ∣ D) :
    (∏ p ∈ s, N p.asIdeal) ≤ N D := by
  have hdvd := map_dvd N (primeIdeal_prod_dvd s D hdiv)
  have hdvd' : (∏ p ∈ s, N p.asIdeal) ∣ N D := by
    simpa only [map_prod] using hdvd
  exact Nat.le_of_dvd hD hdvd'

theorem card_prime_divisors_le_log (N : Ideal R →*₀ ℕ)
    (s : Finset (HeightOneSpectrum R)) (D : Ideal R) (B : ℝ)
    (hD : 0 < N D) (hB : 1 < B)
    (hn : ∀ p ∈ s, B ≤ (N p.asIdeal : ℝ))
    (hdiv : ∀ p ∈ s, p.asIdeal ∣ D) :
    (s.card : ℝ) ≤ Real.log (N D : ℝ) / Real.log B := by
  apply card_le_log_of_prod_le s (fun p => (N p.asIdeal : ℝ)) B (N D : ℝ) hB hn
  exact_mod_cast idealNorm_prod_le N s D hD hdiv

/-- The resulting logarithmic sparse-mask bound is now derived from ideal
divisibility, rather than supplied as a cardinality assumption. -/
theorem norm_maskedSum_le_log (N : Ideal R →*₀ ℕ)
    (s : Finset (HeightOneSpectrum R)) (f : HeightOneSpectrum R → ℂ)
    (keep : HeightOneSpectrum R → Bool) (D : Ideal R) (B C : ℝ)
    (hD : 0 < N D) (hB : 1 < B) (hC : 0 ≤ C)
    (hf : ∀ p ∈ s, keep p = false → ‖f p‖ ≤ C)
    (hn : ∀ p ∈ s, keep p = false → B ≤ (N p.asIdeal : ℝ))
    (hdiv : ∀ p ∈ s, keep p = false → p.asIdeal ∣ D) :
    ‖PrimeCancellationAux.maskedSum s f keep‖ ≤
      ‖∑ p ∈ s, f p‖ + (Real.log (N D : ℝ) / Real.log B) * C := by
  apply PrimeCancellationAux.norm_maskedSum_le_of_card s f keep C
    (Real.log (N D : ℝ) / Real.log B) hC hf
  apply card_prime_divisors_le_log N (s.filter (fun p => keep p = false)) D B hD hB
  · intro p hp
    exact hn p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  · intro p hp
    exact hdiv p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-- The actual mask deletes only primes dividing a fixed ideal times the row. -/
theorem norm_originalMask_sum_le_log (N : Ideal R →*₀ ℕ)
    (s : Finset (HeightOneSpectrum R)) (f : HeightOneSpectrum R → ℂ)
    (S : Set (HeightOneSpectrum R)) (D u : Ideal R) (B C : ℝ)
    (hD : 0 < N (D * u)) (hB : 1 < B) (hC : 0 ≤ C)
    (hS : ∀ p : HeightOneSpectrum R, p ∈ S → p.asIdeal ∣ D)
    (hsix : ∀ p : HeightOneSpectrum R, (6 : R) ∈ p.asIdeal → p.asIdeal ∣ D)
    (hf : ∀ p ∈ s, ‖f p‖ ≤ C)
    (hn : ∀ p ∈ s, B ≤ (N p.asIdeal : ℝ)) :
    ‖PrimeCancellationAux.maskedSum s f
        (fun p => HeckeSkeleton.PrimeCancellationIdealMask.originalMask S u p.asIdeal)‖ ≤
      ‖∑ p ∈ s, f p‖ + (Real.log (N (D * u) : ℝ) / Real.log B) * C := by
  apply norm_maskedSum_le_log N s f
    (fun p => HeckeSkeleton.PrimeCancellationIdealMask.originalMask S u p.asIdeal)
    (D * u) B C hD hB hC
  · intro p hp _
    exact hf p hp
  · intro p hp _
    exact hn p hp
  · intro p _ hdel
    exact HeckeSkeleton.PrimeCancellationIdealMask.deleted_prime_dvd_fixed_mul_row
      S D u hS hsix p hdel

end PrimeCancellation.MaskCount

#print axioms PrimeCancellation.MaskCount.card_le_log_of_prod_le
#print axioms PrimeCancellation.MaskCount.primeIdeal_prod_dvd
#print axioms PrimeCancellation.MaskCount.idealNorm_prod_le
#print axioms PrimeCancellation.MaskCount.card_prime_divisors_le_log
#print axioms PrimeCancellation.MaskCount.norm_maskedSum_le_log
#print axioms PrimeCancellation.MaskCount.norm_originalMask_sum_le_log
