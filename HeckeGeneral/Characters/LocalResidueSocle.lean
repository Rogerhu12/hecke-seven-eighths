import HeckeGeneral.Characters.LocalResidueDual
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! The explicit socle of a completed DVR residue ring and detection of every nonzero ideal. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem localUniformizerInteger_irreducible (v : HeightOneSpectrum (𝓞 K)) :
    Irreducible (localUniformizerInteger K v) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (local_maximalIdeal_eq_span_uniformizer K v)

def localSocleGenerator (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : LocalResidueRing K v (n + 1) :=
  Ideal.Quotient.mk _ (localUniformizerInteger K v ^ n)

theorem localSocleGenerator_ne_zero (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localSocleGenerator K v n ≠ 0 := by
  rw [localSocleGenerator, Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [localMaximalIdeal, local_mem_maximalIdeal_pow_iff_valuation]
  change ¬ Valued.v (localUniformizer K v ^ n) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))
  rw [map_pow, localUniformizer_valuation, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, Nat.cast_add, Nat.cast_one]
  omega

theorem localInteger_unit_uniformizer_factorization (v : HeightOneSpectrum (𝓞 K))
    (x : LocalIntegerRing K v) (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : (LocalIntegerRing K v)ˣ, x = u.val * localUniformizerInteger K v ^ n :=
  IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx
    (localUniformizerInteger_irreducible K v)

/-- Every nonzero residue element can be multiplied to the fixed socle generator. -/
theorem localResidue_mul_to_socle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : LocalResidueRing K v (n + 1)) (ha : a ≠ 0) :
    ∃ b : LocalResidueRing K v (n + 1), a * b = localSocleGenerator K v n := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ≠ 0 := by
    intro h
    exact ha (by rw [h, map_zero])
  obtain ⟨k, u, hxu⟩ := localInteger_unit_uniformizer_factorization K v x hx
  have hk : k ≤ n := by
    by_contra h
    have hn : n + 1 ≤ k := Nat.succ_le_iff.mpr (lt_of_not_ge h)
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [localMaximalIdeal, local_maximalIdeal_pow_eq_span_uniformizer_pow]
    apply Ideal.mem_span_singleton.mpr
    rw [hxu]
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ hn) _
  refine ⟨Ideal.Quotient.mk _ (u.inv * localUniformizerInteger K v ^ (n - k)), ?_⟩
  change Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ _ =
    Ideal.Quotient.mk _ (localUniformizerInteger K v ^ n)
  rw [← map_mul, hxu, mul_mul_mul_comm, u.val_inv, one_mul, ← pow_add, Nat.add_sub_of_le hk]

theorem localSocleGenerator_mem_every_nonzero_ideal (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (I : Ideal (LocalResidueRing K v (n + 1))) (hI : I ≠ ⊥) :
    localSocleGenerator K v n ∈ I := by
  obtain ⟨a, ha, hane⟩ := I.ne_bot_iff.mp hI
  obtain ⟨b, hb⟩ := localResidue_mul_to_socle K v n a hane
  rw [← hb]
  exact I.mul_mem_right b ha

end HeckeGeneral.Characters
