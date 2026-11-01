import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedReindex
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedScale
import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

/-!
# Actual extracted-prime mass and its normalization

Disjoint original lists make a selected tuple recoverable from its ideal
product.  Thus the number of extracted tuples is bounded by the actual
linear ideal-counting theorem.  The square of this count cancels the
original `Z^(-2G)` factor exactly, with a constant depending only on the
fixed number of slots.  No arithmetic fiber count is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedCount

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open ProviderMarkedSlots ProviderMarkedReindex
open scoped Classical BigOperators nonZeroDivisors Function

variable {K : Type} [Field K] [NumberField K] {J : ℕ}

/-- The actual ideal product remembers which original disjoint slot
selected every prime. -/
theorem tuple_product_injective
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) :
    Set.InjOn (primeProduct Finset.univ)
      (↑(tuples lists) : Set (Fin J → HeightOneSpectrum (𝓞 K))) := by
  intro p hp q hq heq
  funext i
  have hpi : (p i).asIdeal ∣ primeProduct Finset.univ q := by
    rw [← heq]
    exact Finset.dvd_prod_of_mem (fun i => (p i).asIdeal) (Finset.mem_univ i)
  obtain ⟨k, hk, hdvd⟩ := ((p i).prime.dvd_finsetProd_iff
    (fun k => (q k).asIdeal)).mp hpi
  have hprime : p i = q k := by
    by_contra hne
    exact (p i).prime.not_unit (((p i).isCoprime_of_ne (q k) hne).isUnit_of_dvd hdvd)
  have hik : i = k := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis hne) (Fintype.mem_piFinset.mp hp i)
      (by simpa only [hprime] using Fintype.mem_piFinset.mp hq k)
  simpa only [hik] using hprime

theorem tuple_product_norm_le
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (z : Fin J → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hupper : ∀ i p, p ∈ lists i → ProviderMarkedPools.norm p.asIdeal ≤ 2 * Z ^ z i)
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples lists) :
    ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤
      (2 : ℝ) ^ J * Z ^ (∑ i, z i) := by
  calc
    _ = ∏ i, ProviderMarkedPools.norm (p i).asIdeal := by
      simp only [ProviderMarkedPools.norm, primeProduct, map_prod, Nat.cast_prod]
    _ ≤ ∏ i, 2 * Z ^ z i := Finset.prod_le_prod₀
      (fun i hi => (ProviderMarkedPools.norm_pos (p i).ne_bot).le)
      (fun i hi => hupper i (p i) (Fintype.mem_piFinset.mp hp i))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ]

/-- A single counting constant works for every original tuple family,
scale, and collection of individual slot lengths. -/
theorem exists_original_tuple_count :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (J : ℕ)
      (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
      (z : Fin J → ℝ) (Z : ℝ),
      Pairwise (Disjoint on lists) → 1 ≤ Z → (∀ i, 0 ≤ z i) →
      (∀ i p, p ∈ lists i → ProviderMarkedPools.norm p.asIdeal ≤ 2 * Z ^ z i) →
      ((tuples lists).card : ℝ) ≤ A * (2 : ℝ) ^ J * Z ^ (∑ i, z i) := by
  obtain ⟨A, hA, _, hcount⟩ :=
    DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K
  refine ⟨A, hA, ?_⟩
  intro J lists z Z hdis hZ hz hupper
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hG : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i hi => hz i
  have hpow : 1 ≤ Z ^ (∑ i, z i) := Real.one_le_rpow hZ hG
  have htwo : 1 ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
  have hX : 1 ≤ (2 : ℝ) ^ J * Z ^ (∑ i, z i) := by
    simpa only [one_mul] using mul_le_mul htwo hpow zero_le_one (by positivity)
  have hb := hcount ((2 : ℝ) ^ J * Z ^ (∑ i, z i)) hX
    ((tuples lists).image (primeProduct Finset.univ)) (by
      intro I hI
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
      exact tuple_product_norm_le lists z Z hZ0 hupper p hp)
  rw [Finset.card_image_of_injOn (tuple_product_injective lists hdis)] at hb
  exact hb.trans_eq (by ring)

/-- The actual two occurrences of extracted-prime counting are exactly
paid by the square of the original overlap normalization. -/
theorem squared_mass_cancel (Z G A N : ℝ) (hZ : 0 < Z) (hN : 0 ≤ N)
    (hcount : N ≤ A * Z ^ G) :
    Z ^ (-2 * G) * N ^ 2 ≤ A ^ 2 := by
  have hsq := pow_le_pow_left₀ hN hcount 2
  have hcancel : Z ^ (-2 * G) * (Z ^ G) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 <;> ring
  calc
    _ ≤ Z ^ (-2 * G) * (A * Z ^ G) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_pos_of_pos hZ _).le
    _ = A ^ 2 * (Z ^ (-2 * G) * (Z ^ G) ^ 2) := by ring
    _ = _ := by rw [hcancel, mul_one]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedCount
