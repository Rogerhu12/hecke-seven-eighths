import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-ideal pool multiplicities over an arbitrary number field

Working with ideals makes the fiber injection independent of a choice of
prime generators.  The coefficient estimates are those of `Pool.lean`;
this file proves the arithmetic multiplicity and size assertions used by
the single pool average.  The argument is the prime-ideal generalization
of openai/math `Moments/AmplificationCount.lean`.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

variable {K : Type*} [Field K] [NumberField K]

theorem ideal_norm_le_of_dvd {I D : Ideal (𝓞 K)} (hI : I ≠ 0) (hd : D ∣ I) :
    (Ideal.absNorm D : ℝ) ≤ Ideal.absNorm I := by
  have hpos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)

theorem primeIdeals_product_dvd (S : Finset (Ideal (𝓞 K)))
    (hP : ∀ P ∈ S, Prime P) (I : Ideal (𝓞 K)) (hd : ∀ P ∈ S, P ∣ I) :
    (∏ P ∈ S, P) ∣ I := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro P hPS Q hQS hPQ
  letI : P.IsMaximal := (Ideal.isPrime_of_prime (hP P hPS)).isMaximal (hP P hPS).ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime (hP Q hQS)).isMaximal (hP Q hQS).ne_zero
  exact Ideal.isCoprime_of_isMaximal hPQ

theorem large_prime_ideal_count (S : Finset (Ideal (𝓞 K))) (hP : ∀ P ∈ S, Prime P)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hd : ∀ P ∈ S, P ∣ I)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ P ∈ S, Z ^ ell ≤ (Ideal.absNorm P : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z ^ B) : (S.card : ℝ) ≤ B / ell := by
  have hpow : Z ^ (ell * (S.card : ℝ)) ≤ Z ^ B := by
    calc
      _ = (Z ^ ell) ^ S.card := Real.rpow_mul_natCast (zero_lt_one.trans hZ).le ell S.card
      _ = ∏ _P ∈ S, Z ^ ell := (Finset.prod_const _).symm
      _ ≤ ∏ P ∈ S, (Ideal.absNorm P : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hlower
      _ = (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by simp only [map_prod, Nat.cast_prod]
      _ ≤ (Ideal.absNorm I : ℝ) := ideal_norm_le_of_dvd hI (primeIdeals_product_dvd S hP I hd)
      _ ≤ _ := hupper
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hpow
  apply (le_div_iff₀ hell).mpr
  simpa only [mul_comm] using he

theorem indexed_large_prime_ideal_count {α : Type*} (S : Finset α)
    (P : α → Ideal (𝓞 K)) (hinj : Set.InjOn P S) (hp : ∀ i ∈ S, Prime (P i))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hd : ∀ i ∈ S, P i ∣ I)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ i ∈ S, Z ^ ell ≤ (Ideal.absNorm (P i) : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z ^ B) : (S.card : ℝ) ≤ B / ell := by
  have hb := large_prime_ideal_count (S.image P) (by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact hp i hi) I hI (by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact hd i hi) Z ell B hZ hell (by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact hlower i hi) hupper
  simpa only [Finset.card_image_of_injOn hinj] using hb

def idealAmplify (x : Ideal (𝓞 K) × Ideal (𝓞 K)) : Ideal (𝓞 K) := x.2 ^ 6 * x.1

theorem idealAmplify_norm (x : Ideal (𝓞 K) × Ideal (𝓞 K))
    (Z M L : ℝ) (hZ : 0 < Z)
    (hh : (Ideal.absNorm x.1 : ℝ) ≤ Z ^ M)
    (hp : (Ideal.absNorm x.2 : ℝ) ≤ Z ^ L) :
    (Ideal.absNorm (idealAmplify x) : ℝ) ≤ Z ^ (M + 6 * L) := by
  calc
    _ = (Ideal.absNorm x.2 : ℝ) ^ 6 * (Ideal.absNorm x.1 : ℝ) := by
      simp only [idealAmplify, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    _ ≤ (Z ^ L) ^ 6 * Z ^ M := mul_le_mul
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 6) hh (Nat.cast_nonneg _) (by positivity)
    _ = Z ^ (M + 6 * L) := by
      rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
      congr 1
      ring

theorem idealAmplify_fiber_count (F : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hp : ∀ x ∈ F, Prime x.2)
    (hrow : ∀ x ∈ F, idealAmplify x = I)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ F, Z ^ ell ≤ (Ideal.absNorm x.2 : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z ^ B) : (F.card : ℝ) ≤ B / ell := by
  apply indexed_large_prime_ideal_count F Prod.snd ?_ hp I hI ?_ Z ell B hZ hell hlower hupper
  · intro x hx y hy heq
    have hfirst : x.1 = y.1 := by
      apply mul_left_cancel₀ (pow_ne_zero 6 (hp x hx).ne_zero)
      change idealAmplify x = x.2 ^ 6 * y.1
      rw [hrow x hx, heq]
      exact (hrow y hy).symm
    exact Prod.ext hfirst heq
  · intro x hx
    rw [← hrow x hx]
    exact (dvd_pow_self x.2 (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem ideal_pool_pushforward (rows pool : Finset (Ideal (𝓞 K)))
    (allow : Ideal (𝓞 K) → Ideal (𝓞 K) → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ pool, Prime p)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ pool, Z ^ ell ≤ (Ideal.absNorm p : ℝ))
    (hpu : ∀ p ∈ pool, (Ideal.absNorm p : ℝ) ≤ Z ^ L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm h : ℝ) ≤ Z ^ M)
    (value : Ideal (𝓞 K) → ℂ) :
    (∑ x ∈ eligiblePairs rows pool allow, ‖value (idealAmplify x)‖ ^ 2) ≤
      ((M + 6 * L) / ell) *
        ∑ I ∈ (eligiblePairs rows pool allow).image idealAmplify, ‖value I‖ ^ 2 := by
  apply positive_pushforward_bound _ idealAmplify (fun I => ‖value I‖ ^ 2) _
    (fun _ _ => sq_nonneg _)
  intro I hI
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
  have hxm := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  apply idealAmplify_fiber_count _ _
    (mul_ne_zero (pow_ne_zero _ (hp x.2 hxm.2).ne_zero) (hrows x.1 hxm.1))
  · intro y hy
    exact hp y.2 (Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · exact hZ
  · exact hell
  · intro y hy
    exact hpl y.2 (Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
  · exact idealAmplify_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hxm.1) (hpu x.2 hxm.2)

end HeckeSkeleton.Moments.EngineStep
