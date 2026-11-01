import HeckeSkeleton.ExpansionModels.OriginalMask
import ExpansionDetector.EulerDeletionSpectrum

/-! Uniform arithmetic size bounds for the literal fixed-S/6/complete-row
deletion set. Fixed exceptional primes are retained in a fixed ideal
factor; the variable factor is the original complete row ideal. -/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.Analysis.ExpansionRecipe

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ExpansionDetector.EulerDeletion
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def fixedDeletedIdeal : Ideal (𝓞 K) :=
  (∏ p ∈ S.toFinset, p.asIdeal) * (sixNonzeroIdeal K).val

def originalDeletionEnvelope (u : NonzeroIdeal K) : Ideal (𝓞 K) :=
  fixedDeletedIdeal K S * u.val

theorem fixedDeletedIdeal_ne_zero : fixedDeletedIdeal K S ≠ 0 := by
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun p _ => p.ne_bot)
  · exact nonZeroDivisors.coe_ne_zero (sixNonzeroIdeal K)

theorem originalDeletionEnvelope_ne_zero (u : NonzeroIdeal K) :
    originalDeletionEnvelope K S u ≠ 0 :=
  mul_ne_zero (fixedDeletedIdeal_ne_zero K S) (nonZeroDivisors.coe_ne_zero u)

theorem originalDeletedPrimes_dvd_envelope (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ originalDeletedPrimes K S u) :
    p.asIdeal ∣ originalDeletionEnvelope K S u := by
  rcases (mem_originalDeletedPrimes K S u p).mp hp with hpS | hp6 | hpu
  · have hp' : p ∈ S.toFinset := Set.mem_toFinset.mpr hpS
    have hprod : p.asIdeal ∣ ∏ q ∈ S.toFinset, q.asIdeal := by
      apply Ideal.dvd_iff_le.mpr
      exact (Ideal.prod_le_inf (s := S.toFinset)
        (f := fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)).trans (Finset.inf_le hp')
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hprod _) _
  · have hsix := (prime_dvd_sixNonzeroIdeal K p).mpr hp6
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hsix _) _
  · exact dvd_mul_of_dvd_right hpu _

theorem originalDeletionEnvelope_norm (u : NonzeroIdeal K) :
    (Ideal.absNorm (originalDeletionEnvelope K S u) : ℝ) =
      (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * idealNorm K u := by
  simp only [originalDeletionEnvelope, map_mul, Nat.cast_mul, idealNorm]

/-- This supplies the elementary deletion-size premise of the actual
zero detector. It is independent of the ramification of the chosen χ. -/
theorem originalDeletion_card_bound (u : NonzeroIdeal K) :
    (2 : ℝ) ^ (originalDeletedPrimes K S u).card ≤
      (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * idealNorm K u := by
  have hb := spectrum_card_power_le_norm (originalDeletionEnvelope K S u)
    (originalDeletionEnvelope_ne_zero K S u) (originalDeletedPrimes K S u)
    (originalDeletedPrimes_dvd_envelope K S u)
  rwa [originalDeletionEnvelope_norm] at hb

theorem originalDeletion_card_bound_of_norm_le (u : NonzeroIdeal K)
    {U : ℝ} (hU : idealNorm K u ≤ 2 * U) :
    (2 : ℝ) ^ (originalDeletedPrimes K S u).card ≤
      (2 * (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ)) * U := by
  exact (originalDeletion_card_bound K S u).trans
    ((mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg _)).trans_eq (by ring))

/-- Positive-line deletion has an arbitrarily small power of the actual
row norm. The finite S/6 factor is entirely in the fixed constant. -/
theorem exists_originalDeletion_localMajorant_subpower
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : NonzeroIdeal K,
      (∏ p ∈ originalDeletedPrimes K S u,
        localMajorant δ (Ideal.absNorm p.asIdeal : ℝ)) ≤ C * idealNorm K u ^ ε := by
  obtain ⟨D, hD, hb⟩ := spectrum_localMajorant_subpower (K := K) δ ε hδ hε
  have hN : 0 < (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (fixedDeletedIdeal_ne_zero K S))
  refine ⟨D * (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) ^ ε, by positivity, ?_⟩
  intro u
  have h := hb (originalDeletionEnvelope K S u) (originalDeletionEnvelope_ne_zero K S u)
    (originalDeletedPrimes K S u) (originalDeletedPrimes_dvd_envelope K S u)
  rw [originalDeletionEnvelope_norm, Real.mul_rpow hN.le (idealNorm_pos K u).le] at h
  exact h.trans_eq (by ring)

end HeckeGeneral.Analysis.ExpansionRecipe
