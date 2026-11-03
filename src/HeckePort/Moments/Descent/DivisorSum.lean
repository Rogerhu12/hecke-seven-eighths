import HeckePort.Moments.Descent.DivisorExtraction

/-!
# Inverse-norm sums over divisor pools

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/DivisorSum.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The file uses two auxiliary facts from outside the shared set, reproved here in general:
* `columnDyadicLength N = ⌈log N / log 2⌉` and its cover property
  (openai `QuadraticSieve/DyadicColumns`),
* `finite_inverse_norm_sum`: `∑_{I ∈ S} 1/N(I) ≤ 2 C (columnDyadicLength H + 1)` for a finite set of
  nonzero ideals of norm at most `H` (openai `MeanSquare/TransformedColumns`, with the constant
  `256 = 2 * 128` becoming `2 * idealCountConstant K`), via the dyadic decomposition of norms.

`hybridDivisorPool`, `hybridDivisorPairPool` and the three theorems are ported as stated, with
the constant `256` replaced by `2 * idealCountConstant K`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open DedekindZetaZeroFree.LargeSieve HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊

theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))

theorem norm_le_of_dvd {k D : Ideal (𝓞 K)} (hk : k ≠ ⊥) (h : D ∣ k) :
    (Ideal.absNorm D : ℝ) ≤ Ideal.absNorm k := by
  have hpos : 0 < Ideal.absNorm k :=
    Nat.pos_of_ne_zero (fun hz => hk (Ideal.absNorm_eq_zero_iff.mp hz))
  exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm h)

theorem finite_inverse_norm_sum (S : Finset (Ideal (𝓞 K))) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ ⊥) (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1 / (Ideal.absNorm I : ℝ)) ≤
      2 * idealCountConstant K * (columnDyadicLength H + 1 : ℝ) := by
  have hC := one_le_idealCountConstant K
  have hpos (I : Ideal (𝓞 K)) (hI : I ∈ S) : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  set L := columnDyadicLength H with hL
  have hmaps : ∀ I ∈ S, Nat.log 2 (Ideal.absNorm I) ∈ Finset.range (L + 1) := by
    intro I hI
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have h1 : (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ L := (hH I hI).trans (columnDyadicLength_cover H)
    have h2 : Ideal.absNorm I ≤ 2 ^ L := by exact_mod_cast h1
    calc Nat.log 2 (Ideal.absNorm I) ≤ Nat.log 2 (2 ^ L) := Nat.log_mono_right h2
      _ = L := Nat.log_pow (by norm_num) L
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun I => Nat.log 2 (Ideal.absNorm I)) hmaps]
  have hfiber : ∀ j ∈ Finset.range (L + 1),
      (∑ I ∈ S with Nat.log 2 (Ideal.absNorm I) = j, 1 / (Ideal.absNorm I : ℝ)) ≤
        2 * idealCountConstant K := by
    intro j _
    set F := S.filter (fun I => Nat.log 2 (Ideal.absNorm I) = j) with hF
    have hlow (I : Ideal (𝓞 K)) (hI : I ∈ F) : (2 : ℝ) ^ j ≤ Ideal.absNorm I := by
      obtain ⟨hIS, hj⟩ := Finset.mem_filter.mp hI
      have := Nat.pow_log_le_self 2 (hpos I hIS).ne'
      rw [hj] at this
      exact_mod_cast this
    have hup (I : Ideal (𝓞 K)) (hI : I ∈ F) : (Ideal.absNorm I : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      obtain ⟨hIS, hj⟩ := Finset.mem_filter.mp hI
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Ideal.absNorm I)
      rw [hj] at this
      exact_mod_cast this.le
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hone : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hcard : (F.card : ℝ) ≤ idealCountConstant K * 2 ^ (j + 1) :=
      card_le_idealCountConstant K F _ hone hup
    calc
      (∑ I ∈ F, 1 / (Ideal.absNorm I : ℝ)) ≤ ∑ _I ∈ F, 1 / (2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro I hI
        exact one_div_le_one_div_of_le hp (hlow I hI)
      _ = (F.card : ℝ) / 2 ^ j := by simp [div_eq_mul_inv]
      _ ≤ (idealCountConstant K * 2 ^ (j + 1)) / 2 ^ j :=
        div_le_div_of_nonneg_right hcard hp.le
      _ = 2 * idealCountConstant K := by
        rw [pow_succ]
        field_simp
  calc
    _ ≤ ∑ _j ∈ Finset.range (L + 1), 2 * idealCountConstant K := Finset.sum_le_sum hfiber
    _ = 2 * idealCountConstant K * (L + 1 : ℝ) := by
      simp [Finset.sum_const, mul_comm]

def hybridDivisorPool (rows : Finset (Ideal (𝓞 K))) : Finset (Ideal (𝓞 K)) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal (𝓞 K))) :
    Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal (𝓞 K))) (N : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ ⊥ ∧ (Ideal.absNorm k : ℝ) ≤ N)
    (D : Ideal (𝓞 K)) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ ⊥ ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (norm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal (𝓞 K))) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal (𝓞 K))) (N : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ ⊥ ∧ (Ideal.absNorm k : ℝ) ≤ N) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (2 * idealCountConstant K * (columnDyadicLength N + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows N hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) N
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end HeckePort.Moments

end
