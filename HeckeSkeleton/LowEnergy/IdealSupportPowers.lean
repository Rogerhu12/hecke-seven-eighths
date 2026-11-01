import HeckeSkeleton.LowEnergy.SupportPowers
import HeckeGeneral.Arithmetic.IdealFactorization

/-!
# Genuine ideal-support enumeration over an arbitrary number field

There is no ideal-divisor-count assumption.  The only global finiteness fact
is Mathlib's proved finiteness of prime ideals of bounded absolute norm.
Norm multiplicativity and exact prime-exponent reconstruction give the norm
budget.  In particular, all four-way local frozen choices cost `N(I)^eps`.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.IdealSupportPowers
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

def primeNorm (p : HeightOneSpectrum (𝓞 K)) : ℝ := p.asIdeal.absNorm

theorem one_le_primeNorm (p : HeightOneSpectrum (𝓞 K)) : 1 ≤ primeNorm K p := by
  change (1 : ℝ) ≤ (p.asIdeal.absNorm : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => p.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))

theorem finite_primeNorm_le (T : ℝ) : Set.Finite {p | primeNorm K p ≤ T} := by
  letI : Ring.HasFiniteQuotients (𝓞 K) := .of_module_finite ℤ _
  have h := Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
    (S := 𝓞 K) (Nat.ceil T)
  apply h.subset
  intro p hp
  have hle : (p.asIdeal.absNorm : ℝ) ≤ Nat.ceil T := hp.trans (Nat.le_ceil T)
  exact_mod_cast hle

/-- The prime support product is bounded by the actual ideal norm. -/
theorem support_product_le_norm (I : (Ideal (𝓞 K))⁰) :
    (∏ p ∈ (primeExponents I).support, primeNorm K p) ≤ (I.val.absNorm : ℝ) := by
  have hn := map_idealOfPrimeExponents Ideal.absNorm.toMonoidHom (primeExponents I)
  rw [idealOfPrimeExponents_primeExponents] at hn
  have hnorm := congrArg (fun n : ℕ => (n : ℝ)) hn
  simp only [Finsupp.prod, Nat.cast_prod, Nat.cast_pow] at hnorm
  change (I.val.absNorm : ℝ) = ∏ p ∈ (primeExponents I).support,
    primeNorm K p ^ primeExponents I p at hnorm
  rw [hnorm]
  apply Finset.prod_le_prod₀
  · intro p _
    exact zero_le_one.trans (one_le_primeNorm K p)
  · intro p hp
    have he : primeExponents I p ≠ 0 := Finsupp.mem_support_iff.mp hp
    exact le_self_pow₀ (one_le_primeNorm K p) he

/-- Fixed local-state counts on the actual prime support are `N(I)^eps`. -/
theorem prime_support_states_small_power (B eps : ℝ) (hB : 1 ≤ B) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : (Ideal (𝓞 K))⁰,
      B ^ (primeExponents I).support.card ≤ C * (I.val.absNorm : ℝ) ^ eps := by
  obtain ⟨C, hC, hbound⟩ := SupportPowers.fixed_states_small_power
    (primeNorm K) (one_le_primeNorm K) (finite_primeNorm_le K) B eps hB heps
  refine ⟨C, hC, ?_⟩
  intro I
  exact (hbound (primeExponents I).support).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ =>
        zero_le_one.trans (one_le_primeNorm K p))) (support_product_le_norm K I) heps.le)
      (zero_le_one.trans hC))

/-- This counts actual finite state tables, including the inactive choice and
three possible minima, without postulating an enumeration estimate. -/
theorem actual_state_table_count (r : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : (Ideal (𝓞 K))⁰,
      (Fintype.card ((primeExponents I).support → Fin r) : ℝ) ≤
        C * (I.val.absNorm : ℝ) ^ eps := by
  obtain ⟨C, hC, hbound⟩ := SupportPowers.finite_state_assignments_small_power
    (primeNorm K) (one_le_primeNorm K) (finite_primeNorm_le K) r eps heps
  refine ⟨C, hC, ?_⟩
  intro I
  exact (hbound (primeExponents I).support).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ =>
        zero_le_one.trans (one_le_primeNorm K p))) (support_product_le_norm K I) heps.le)
      (zero_le_one.trans hC))

/-- The complete fourth-state Cauchy loss is still one arbitrary small power. -/
theorem squared_four_state_count (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : (Ideal (𝓞 K))⁰,
      ((Fintype.card ((primeExponents I).support → Fin 4) : ℝ)) ^ 2 ≤
        C * (I.val.absNorm : ℝ) ^ eps := by
  obtain ⟨C, hC, hbound⟩ := actual_state_table_count K 4 (eps / 2) (by positivity)
  refine ⟨C ^ 2, one_le_pow₀ hC, ?_⟩
  intro I
  calc
    _ ≤ (C * (I.val.absNorm : ℝ) ^ (eps / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbound I) 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      congr 1
      congr 1
      ring

#print axioms finite_primeNorm_le
#print axioms support_product_le_norm
#print axioms prime_support_states_small_power
#print axioms actual_state_table_count
#print axioms squared_four_state_count

end HeckeSkeleton.LowEnergy.IdealSupportPowers
