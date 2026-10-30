import HeckePort.Moments.Descent.Quadratic
import HeckePort.Moments.Descent.Hybrid

/-!
# Reduction of the hybrid block to the quadratic and cubic sieves

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/HybridReduction.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

As in `Descent/Quadratic` and `Descent/Hybrid`, the quadratic row `quadraticRow k (primaryGenerator J)`
is an abstract `q k J` and the cubic kernel `inverseCubicKernel P J` is an abstract `κ P J`; the
quadratic large sieve is the hypothesis `ColumnEnergy q RowAdm ColAdm`, and the cubic large
sieve `CubicSieve.family_squared_norm_le` (the bound `sieveNorm N L` for the matrix
`(κ P J)`) is the hypothesis `hcubic` of the `sieve_norm` theorems, in finset form.  The predicates
`CanonicalQuadraticSieve.Admissible` and `CubicSieve.Admissible` become `RowAdm`/`ColAdm` and
`CubAdm`.  `finite_inverse_cubic_energy` (the conversion of the matrix large sieve into the
finset form) is therefore not stated: its output is `hcubic`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

theorem hybrid_quadratic_reduction (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm : Ideal (𝓞 K) → Prop) (hCol : ∀ J, ColAdm J → J ≠ ⊥)
    (hmul : ∀ k, RowAdm k → ∀ B J : Ideal (𝓞 K), q k (B * J) = q k B * q k J)
    (hnorm : ∀ k, RowAdm k → ∀ J, ‖q k J‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (Cq : ℝ) (hCq : 0 < Cq)
    (hsieve : ColumnEnergy q RowAdm ColAdm (ε / 2) Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ A X : ℝ, 1 ≤ A → 1 ≤ X →
    ∀ (rows : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ p ∈ pairs, ColAdm (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal (𝓞 K)) (cset : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
      (Pset : Finset (Ideal (𝓞 K))) (coef : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
      (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        q k (B * (p.1 * p.2)) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * κ P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (A * X) ^ ε * (A + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * κ P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ :=
    quadratic_product_column_energy_fixed_factor q RowAdm ColAdm hCol hmul hnorm ε hε Cq hCq hsieve
  refine ⟨C, hC, ?_⟩
  intro A X hA hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (c : Ideal (𝓞 K)) :=
    ∑ P ∈ Pset, coef p.2 P * κ P (c * (mBad * p.1))
  have he := hquadratic A X hA hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal (𝓞 K) × Ideal (𝓞 K)) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (A * X) ^ ε * (A + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (CubAdm : Ideal (𝓞 K) → Prop) (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Jset Pset : Finset (Ideal (𝓞 K)))
      (mBad : Ideal (𝓞 K)) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal (𝓞 K) → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * κ P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal (𝓞 K) → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * κ P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD1, hdiv⟩ := ideal_divisor_count_le_rpow K ε hε
  have hD : 0 < D := zero_lt_one.trans_le hD1
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal (𝓞 K)) := ‖∑ P ∈ Pset, a P * κ P J‖ ^ 2
  have hfiber (J : Ideal (𝓞 K)) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := hCub J (hJset J hJ).1
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

/-- openai `cubic_product_row_sieve_norm`; `sieveNorm` is `CubicSieve.sieveNorm`, and the cubic
large sieve (openai `finite_inverse_cubic_energy`) is the hypothesis `hcubic`. -/
theorem cubic_product_row_sieve_norm (κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (CubAdm : Ideal (𝓞 K) → Prop) (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (sieveNorm : ℝ → ℝ → ℝ)
    (hcubic : ∀ (Jset Pset : Finset (Ideal (𝓞 K))) (N L : ℝ),
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal (𝓞 K) → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * κ P J‖ ^ 2) ≤
          sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Jset Pset : Finset (Ideal (𝓞 K)))
      (mBad : Ideal (𝓞 K)),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal (𝓞 K) → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * κ P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve κ CubAdm hCub ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (sieveNorm N L) hmap hJ (hcubic Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm CubAdm : Ideal (𝓞 K) → Prop) (hCol : ∀ J, ColAdm J → J ≠ ⊥)
    (hCub : ∀ J, CubAdm J → J ≠ ⊥)
    (hmul : ∀ k, RowAdm k → ∀ B J : Ideal (𝓞 K), q k (B * J) = q k B * q k J)
    (hnorm : ∀ k, RowAdm k → ∀ J, ‖q k J‖ ≤ 1)
    (sieveNorm : ℝ → ℝ → ℝ) (hsieveNorm : ∀ N L, 0 ≤ sieveNorm N L)
    (hcubic : ∀ (Jset Pset : Finset (Ideal (𝓞 K))) (N L : ℝ),
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal (𝓞 K) → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * κ P J‖ ^ 2) ≤
          sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) (Cq : ℝ) (hCq : 0 < Cq)
    (hsieve : ColumnEnergy q RowAdm ColAdm (ε / 2) Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ A X N L : ℝ, 1 ≤ A → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal (𝓞 K))) (pairs cubicPairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
      (Hset Jset Pset : Finset (Ideal (𝓞 K))),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ p ∈ pairs, ColAdm (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal (𝓞 K)) (cset : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)))
      (coef : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
      (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubAdm J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubAdm P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        q k (B * (p.1 * p.2)) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * κ P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (A * X * N) ^ ε * (A + X) * Cbound * (Hset.card : ℝ) *
        sieveNorm N L * Ebound := by
  obtain ⟨Cq', hCq', hquad⟩ :=
    hybrid_quadratic_reduction q κ RowAdm ColAdm hCol hmul hnorm ε hε Cq hCq hsieve
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm κ CubAdm hCub sieveNorm hcubic ε hε
  refine ⟨Cq' * D, mul_pos hCq' hD, ?_⟩
  intro A X N L hA hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal (𝓞 K)) := ‖∑ P ∈ Pset,
    coef h P * κ P (c * (mBad * m))‖ ^ 2
  have hnorm' : 0 ≤ sieveNorm N L := hsieveNorm N L
  have he := hquad A X hA hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm')
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq' * (A * X) ^ ε * (A + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ A * X by positivity) (show 0 ≤ N by linarith)]
      ring

end HeckePort.Moments

end
