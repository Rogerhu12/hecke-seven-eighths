import HeckePort.CenteredMoment.Mask
import HeckePort.Moments.Descent.Marks
import HeckePort.Moments.Descent.Overlap
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

/-!
# Ideal masks and prime marks

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/IdealMasks.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K` for an arbitrary number field `K`.

* `ideal_primeSupport_mul_cube` replaces `n * b ^ 3`; the divisor-power bound of
  `ideal_primeMark_small_power` is obtained from the upstream
  `ideal_divisor_count_le_rpow` (via `2 ^ ω(A) ≤ #divisors`), so its constant depends on `K`.
* Not ported: `idealZeroMask_primary_indicator` and `hybrid_quadratic_square_mask`.
  They are statements about `CanonicalQuadraticSieve.idealZeroMask` / `quadraticRow`, the
  quadratic-residue row of `ℤ[ω]` evaluated at the primary generator; this object is part of the
  quadratic-sieve interface (obligation MI-M-QUADRATIC-SIEVE), not of S0.
* `hybrid_column_decomposition` uses Mathlib's `exists_sq_mul_squarefree` for the
  square/squarefree split and the `gcd = ⊔` structure on ideals of a Dedekind domain.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve HeckePort.IdealMobiusDivisorSum

variable {K : Type*} [Field K] [NumberField K]

theorem prime_mem_support_iff_dvd (P A : Ideal (𝓞 K))
    (hP : Prime P) (hA : A ≠ ⊥) :
    P ∈ primeSupport A ↔ P ∣ A := by
  simp only [primeSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff hA, hP, true_and]

theorem ideal_primeMark_eq_divisibility {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (hL : ∀ i ∈ I, ∀ P ∈ L i, Prime P)
    (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) :
    primeMark I L a (primeSupport A) =
      ∏ i ∈ I, ∑ P ∈ L i, if P ∣ A then a i P else 0 := by
  unfold primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro P hP
  simp only [prime_mem_support_iff_dvd P A (hL i hi P hP) hA]

theorem ideal_primeSupport_mul_cube (n b : Ideal (𝓞 K))
    (hn : n ≠ ⊥) (hb : b ≠ ⊥) :
    primeSupport (n * b ^ 3) = primeSupport n ∪ primeSupport b := by
  simp only [primeSupport,
    normalizedFactors_mul hn (pow_ne_zero 3 hb), normalizedFactors_pow,
    Multiset.toFinset_add]
  congr 1
  ext P
  simp

theorem ideal_whole_mark_priority {σ : Type*} [DecidableEq σ]
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ)
    (n b : Ideal (𝓞 K)) (hn : n ≠ ⊥) (hb : b ≠ ⊥) :
    primeMark I L a (primeSupport (n * b ^ 3)) =
      ∑ J ∈ I.powerset,
        primeMark J L a (primeSupport n) *
        primeMark (I \ J) L a (primeSupport b \ primeSupport n) := by
  rw [ideal_primeSupport_mul_cube n b hn hb]
  exact primeMark_priority _ _ _ _ _

/-- `2 ^ ω(A) ≤ C_ε N(A)^ε`; the general-field replacement of openai's
`SquarefreeDivisorBound.prime_support_subsets_bound`, from the upstream divisor bound. -/
theorem prime_support_subsets_bound (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC1, hC⟩ := ideal_divisor_count_le_rpow K ε hε
  refine ⟨C, by linarith, fun I hI => ?_⟩
  have hcard : 2 ^ (primeSupport I).card ≤ (idealDivisors I).card := by
    have h1 : ((idealDivisors I).filter Squarefree).card ≤ (idealDivisors I).card :=
      Finset.card_filter_le _ _
    rw [squarefree_divisors_eq_image I hI, Finset.card_image_of_injOn, Finset.card_powerset]
      at h1
    · exact h1
    · intro S hS T hT hST
      exact support_product_injective (Finset.mem_powerset.mp hS)
        (Finset.mem_powerset.mp hT) hST
  calc (2 : ℝ) ^ (primeSupport I).card = ((2 ^ (primeSupport I).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((idealDivisors I).card : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := hC I

theorem ideal_primeMark_small_power (K : Type*) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
      (a : σ → Ideal (𝓞 K) → ℂ),
      (I : Set σ).PairwiseDisjoint L →
      (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) →
      ∀ A : Ideal (𝓞 K), A ≠ ⊥ →
        ‖primeMark I L a (primeSupport A)‖ ≤
          C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := prime_support_subsets_bound K ε hε
  refine ⟨C, hC, ?_⟩
  intro σ _ I L a hL ha A hA
  exact (primeMark_norm_le_divisor_count I L a _ hL ha).trans (hb A hA)

theorem ideal_coprime_mobius (k P : Ideal (𝓞 K)) (hk : k ≠ ⊥) :
    (if IsCoprime k P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, if R ∣ P then (moebius R : ℂ) else 0 := by
  rw [isCoprime_comm]
  exact CenteredMomentMask.ideal_coprime_mobius P k hk

theorem hybrid_double_mask_mobius
    (k P c : Ideal (𝓞 K)) (hk : k ≠ ⊥) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

/-- The quotient `I / D` (zero if `D ∤ I`); openai's `CanonicalQuadraticSieve.idealQuotient`. -/
def idealQuotient (D I : Ideal (𝓞 K)) : Ideal (𝓞 K) := if h : D ∣ I then h.choose else ⊥

theorem idealQuotient_mul {D I : Ideal (𝓞 K)} (h : D ∣ I) : D * idealQuotient D I = I := by
  have e : idealQuotient D I = h.choose := by simp [idealQuotient, h]
  rw [e]
  exact h.choose_spec.symm

theorem gcd_eq_iff_quotient_coprime (D I J : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (idealQuotient D I) (idealQuotient D J) := by
  have he : gcd I J = D * gcd (idealQuotient D I) (idealQuotient D J) := by
    calc
      gcd I J = gcd (D * idealQuotient D I) (D * idealQuotient D J) := by
        rw [idealQuotient_mul hDI, idealQuotient_mul hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

/-- Square part of an ideal (`I = squarePart I ^ 2 * squarefreePart I`). -/
def squarePart (I : Ideal (𝓞 K)) : Ideal (𝓞 K) := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal (𝓞 K)) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal (𝓞 K)) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

theorem squarePart_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : squarePart I ≠ ⊥ := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, ← Ideal.zero_eq_bot, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm

theorem squarefree_decomposition_unique {A B D E : Ideal (𝓞 K)}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal (𝓞 K)) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)

theorem hybrid_column_decomposition
    (n b : Ideal (𝓞 K)) (hn : Squarefree n) (hb : b ≠ ⊥) :
    ∃ c m h t : Ideal (𝓞 K),
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ ⊥ := by
  let g := squarefreePart b
  let t := squarePart b
  let c := gcd n g
  let m := idealQuotient c n
  let h := idealQuotient c g
  have hg : Squarefree g := squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ ⊥ := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (idealQuotient_mul hcn).symm
  have hgh : g = c * h := (idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    squarePart_ne_zero hb⟩

theorem ideal_product_fiber_card (P : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ((P.filter (fun p => p.1 * p.2 = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    rw [← (Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1 ≠ ⊥ := by
      intro hz
      simp only [hz, Ideal.bot_mul] at hp'
      exact hJ hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp', he, hq']

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (B J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ ⊥ := by
      intro hz
      apply hJ
      rw [← hep, hz, Ideal.mul_bot]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end HeckePort.Moments

end
