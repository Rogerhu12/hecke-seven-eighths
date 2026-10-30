import PrimeCancellationPrimeSeries
import HeckeGeneral.Analysis.IdealEulerProduct

/-!
# Actual prime-ideal counting for the cancellation adapter

The common linear constant follows from Mathlib's proved ideal-counting
asymptotic.  It is selected before the finite pool, character, and cutoff.
No physical-row construction or moment estimate is imported.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationHecke

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open PrimeCancellationPrimeSeries
open scoped Classical Topology BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The prime index is countable because every ideal-norm fiber is finite. -/
instance primeIndex_countable : Countable (HeightOneSpectrum (𝓞 K)) := by
  haveI : Countable (Ideal (𝓞 K)) := by
    apply Set.Countable.of_preimage_singleton (f := Ideal.absNorm)
    intro n
    exact (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact HeightOneSpectrum.asIdeal_injective.countable


/-- The actual absolute ideal norm on the actual prime-ideal index. -/
def primeNorm (p : HeightOneSpectrum (𝓞 K)) : ℝ := (p.asIdeal.absNorm : ℝ)

theorem primeNorm_ge_two (p : HeightOneSpectrum (𝓞 K)) : 2 ≤ primeNorm K p := by
  have hn : 2 ≤ p.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p
  change (2 : ℝ) ≤ (p.asIdeal.absNorm : ℝ)
  exact_mod_cast hn


private theorem finite_normBound (Y : ℝ) (hY : 0 ≤ Y) :
    Finite {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} := by
  have hfinite : {I : Ideal (𝓞 K) | (I.absNorm : ℝ) ≤ Y}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le ⌊Y⌋₊).subset
      (fun I hI => (Nat.le_floor_iff hY).mpr hI)
  exact hfinite.to_subtype

/-- The genuine ideal-counting asymptotic supplies a field-only linear
constant, including the bounded initial interval. -/
theorem exists_ideal_count_bound : ∃ d : ℝ, 0 < d ∧ ∀ Y : ℝ, 1 ≤ Y →
    (Nat.card {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} : ℝ) ≤ d * Y := by
  let N (Y : ℝ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} : ℝ)
  have hlim : Tendsto (fun Y : ℝ => N Y / Y) atTop (𝓝 (dedekindZeta_residue K)) :=
    NumberField.Ideal.tendsto_norm_le_div_atTop K
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (lt_add_one (dedekindZeta_residue K))))
  let V := max 1 Y₀
  let D := dedekindZeta_residue K + 1
  have hD : 0 < D := by dsimp [D]; linarith [dedekindZeta_residue_pos K]
  have hN : 0 ≤ N V := Nat.cast_nonneg _
  refine ⟨N V + D, by positivity, ?_⟩
  intro Y hY
  by_cases hsmall : Y ≤ V
  · letI := finite_normBound K V (zero_le_one.trans (le_max_left _ _))
    have hmono : N Y ≤ N V := Nat.cast_le.mpr (Nat.card_le_card_of_injective
      (fun I : {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} =>
        (⟨I.val, I.property.trans hsmall⟩ : {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ V}))
      (fun _ _ h => Subtype.ext (congrArg Subtype.val h)))
    exact hmono.trans ((le_mul_of_one_le_right hN hY).trans
      (mul_le_mul_of_nonneg_right (by linarith : N V ≤ N V + D) (by linarith)))
  · have hlarge := hY₀ Y ((le_max_right 1 Y₀).trans (le_of_not_ge hsmall))
    have hlarge' : N Y < D * Y := (div_lt_iff₀ (by linarith : 0 < Y)).mp hlarge
    exact hlarge'.le.trans (mul_le_mul_of_nonneg_right
      (by linarith : D ≤ N V + D) (by linarith))

/-- A field-only linear prime-counting constant, valid for arbitrary finite
subsets and every nonnegative cutoff. No moment model enters this theorem. -/
theorem exists_prime_count_bound : ∃ d : ℝ, 0 < d ∧
    ∀ (pool : Finset (HeightOneSpectrum (𝓞 K))) (Y : ℝ), 0 ≤ Y →
      ((pool.filter (fun p => primeNorm K p ≤ Y)).card : ℝ) ≤ d * Y := by
  obtain ⟨d, hd, hcount⟩ := exists_ideal_count_bound K
  refine ⟨d, hd, ?_⟩
  intro pool Y hY
  by_cases hYone : 1 ≤ Y
  · let T := pool.filter (fun p => primeNorm K p ≤ Y)
    letI := finite_normBound K Y hY
    let f : T → {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} := fun p =>
      ⟨p.val.asIdeal, (Finset.mem_filter.mp p.property).2⟩
    have hf : Function.Injective f := by
      intro p q h
      apply Subtype.ext
      exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h)
    have hc := Nat.card_le_card_of_injective f hf
    have hc' : T.card ≤ Nat.card {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ Y} := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
    exact (Nat.cast_le.mpr hc').trans (hcount Y hYone)
  · have hempty : pool.filter (fun p => primeNorm K p ≤ Y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      have htwo := primeNorm_ge_two K p
      linarith
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hd.le hY

def primeCountConstant : ℝ := Classical.choose (exists_prime_count_bound K)

theorem primeCountConstant_pos : 0 < primeCountConstant K :=
  (Classical.choose_spec (exists_prime_count_bound K)).1

theorem actualPrimeArithmetic (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    PrimeArithmetic (primeNorm K) a (primeCountConstant K) where
  d_nonneg := (primeCountConstant_pos K).le
  norm_ge_two := primeNorm_ge_two K
  count := (Classical.choose_spec (exists_prime_count_bound K)).2
  coeff_bound := ha

#print axioms exists_ideal_count_bound
#print axioms actualPrimeArithmetic

end HeckeSkeleton.PrimeCancellationHecke
