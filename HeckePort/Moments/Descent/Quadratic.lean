import HeckePort.Moments.Descent.IdealMasks
import HeckePort.Moments.Descent.SieveComposition

/-!
# Quadratic energy for product columns

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Quadratic.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai derives the product-column energy bounds from the quadratic large sieve of
`ℤ[ω]` (`sieveNorm_sharp`, `family_squared_norm_le`, `FiniteSieveOperator`), for the row
function `quadraticRow k (primaryGenerator J)` and the predicate `Admissible`.  Those objects
(QuadraticSieve/*, obligation MI-M-QUADRATIC-SIEVE) are not part of S0.  Here the quadratic row is
an arbitrary function `q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ` of the pair (row ideal, column ideal)
(`q k J = quadraticRow k (primaryGenerator J)`; for the project it is the value of the
quadratic symbol of `k` at the allowed generator of `J`), `RowAdm`/`ColAdm` are arbitrary
admissibility predicates, and the sieve itself is the hypothesis `ColumnEnergy`, which is
exactly the statement of openai's `finite_squarefree_quadratic_energy` (for `ColAdm = Squarefree`)
resp. `finite_family_quadratic_hybrid_orientation` (for `ColAdm = Admissible`), in finset form.
`columnEnergy_of_family` converts the indexed-family form into the finset form.

Everything derived from the sieve is ported: `quadratic_product_column_energy` (with the
divisor-fiber step through `column_fiber_sieve`), `quadratic_fixed_factor_energy` (multiplicativity
of the row, norm bound by one) and the two fixed-factor corollaries.  The divisor constant is from
the upstream `ideal_divisor_count_le_rpow`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open DedekindZetaZeroFree.LargeSieve

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The quadratic large sieve for columns satisfying `ColAdm`, in finset form
(openai `finite_squarefree_quadratic_energy` for `ColAdm = Squarefree`). -/
def ColumnEnergy (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm : Ideal (𝓞 K) → Prop) (ε C : ℝ) : Prop :=
  ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
    ∀ (rows cols : Finset (Ideal (𝓞 K))),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ J ∈ cols, ColAdm J ∧ (Ideal.absNorm J : ℝ) ≤ B) →
    ∀ a : Ideal (𝓞 K) → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, q k J * a J‖ ^ 2) ≤
        C * (A * B) ^ ε * (A + B) * ∑ J ∈ cols, ‖a J‖ ^ 2

/-- The indexed-family form of the sieve (openai
`finite_family_quadratic_hybrid_orientation`) gives the finset form; this is the
`Subtype`/`sum_coe_sort` step in openai's proof of `quadratic_product_column_energy`. -/
theorem columnEnergy_of_family (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm : Ideal (𝓞 K) → Prop) (ε C : ℝ)
    (hfam : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
      ∀ {m n : Type u} [Fintype m] [Fintype n]
        (rows : m → Ideal (𝓞 K)) (cols : n → Ideal (𝓞 K)),
        Function.Injective rows → Function.Injective cols →
        (∀ i, RowAdm (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ A) →
        (∀ j, ColAdm (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ B) →
        ∀ a : n → ℂ,
          (∑ i, ‖∑ j, q (rows i) (cols j) * a j‖ ^ 2) ≤
            C * (A * B) ^ ε * (A + B) * ∑ j, ‖a j‖ ^ 2) :
    ColumnEnergy q RowAdm ColAdm ε C := by
  intro A B hA hB rows cols hrows hcols f
  have he := hfam A B hA hB (fun k : rows => k.val) (fun J : cols => J.val)
    Subtype.val_injective Subtype.val_injective
    (fun k : rows => hrows k.val k.property) (fun J : cols => hcols J.val J.property)
    (fun J : cols => f J.val)
  have hi (k : rows) :
      (∑ J : cols, q k.val J.val * f J.val) = ∑ J ∈ cols, q k.val J * f J :=
    Finset.sum_coe_sort cols (fun J => q k.val J * f J)
  simp_rw [hi] at he
  rw [Finset.sum_coe_sort rows (fun k => ‖∑ J ∈ cols, q k J * f J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖f J‖ ^ 2)] at he
  exact he

theorem quadratic_product_column_energy (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm : Ideal (𝓞 K) → Prop) (hCol : ∀ J, ColAdm J → J ≠ ⊥)
    (ε : ℝ) (hε : 0 < ε) (Cq : ℝ) (hCq : 0 < Cq)
    (hsieve : ColumnEnergy q RowAdm ColAdm (ε / 2) Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
    ∀ (rows : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ p ∈ pairs, ColAdm (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ B) →
    ∀ a : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs, q k (p.1 * p.2) * a p‖ ^ 2) ≤
      C * (A * B) ^ ε * (A + B) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cd, hCd1, hdiv⟩ := ideal_divisor_count_le_rpow K (ε / 2) hhalf
  have hCd : 0 < Cd := by linarith
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro A B hA hB rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal (𝓞 K)) (hJ : J ∈ target) :
      ColAdm J ∧ (Ideal.absNorm J : ℝ) ≤ B := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hquad (f : Ideal (𝓞 K) → ℂ) :
      (∑ k ∈ rows, ‖∑ J ∈ target, q k J * f J‖ ^ 2) ≤
        (Cq * (A * B) ^ (ε / 2) * (A + B)) * ∑ J ∈ target, ‖f J‖ ^ 2 :=
    hsieve A B hA hB rows target hrows ht f
  have hfiber (J : Ideal (𝓞 K)) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * B ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (ideal_product_fiber_card pairs J (hCol J (ht J hJ).1))).trans
    exact (hdiv J).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => q k J) a
    (Cq * (A * B) ^ (ε / 2) * (A + B)) (Cd * B ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber hquad
  apply he.trans
  have hAB : 0 < A * B := mul_pos (by linarith) (by linarith)
  have hpow : (A * B) ^ (ε / 2) * B ^ (ε / 2) ≤ (A * B) ^ ε := by
    calc
      _ ≤ (A * B) ^ (ε / 2) * (A * B) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hAB.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hA) hhalf.le
      _ = _ := by rw [← Real.rpow_add hAB]; congr 1; ring
  calc
    _ = (Cq * Cd) * ((A * B) ^ (ε / 2) * B ^ (ε / 2)) * (A + B) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (rows : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (hmul : ∀ k ∈ rows, ∀ B J : Ideal (𝓞 K), q k (B * J) = q k B * q k J)
    (hnorm : ∀ k ∈ rows, ∀ J, ‖q k J‖ ≤ 1) (B : Ideal (𝓞 K))
    (a : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs, q k (B * (p.1 * p.2)) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs, q k (p.1 * p.2) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs, q k (B * (p.1 * p.2)) * a p) =
      q k B * ∑ p ∈ pairs, q k (p.1 * p.2) * a p := by
    simp only [hmul k hk, Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hnorm k hk B)

theorem quadratic_product_column_energy_fixed_factor
    (q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (RowAdm ColAdm : Ideal (𝓞 K) → Prop) (hCol : ∀ J, ColAdm J → J ≠ ⊥)
    (hmul : ∀ k, RowAdm k → ∀ B J : Ideal (𝓞 K), q k (B * J) = q k B * q k J)
    (hnorm : ∀ k, RowAdm k → ∀ J, ‖q k J‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (Cq : ℝ) (hCq : 0 < Cq)
    (hsieve : ColumnEnergy q RowAdm ColAdm (ε / 2) Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ A X : ℝ, 1 ≤ A → 1 ≤ X →
    ∀ (rows : Finset (Ideal (𝓞 K))) (pairs : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))),
      (∀ k ∈ rows, RowAdm k ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∀ p ∈ pairs, ColAdm (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal (𝓞 K)) (a : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs, q k (B * (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (A * X) ^ ε * (A + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_product_column_energy q RowAdm ColAdm hCol ε hε Cq hCq hsieve
  refine ⟨C, hC, ?_⟩
  intro A X hA hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy q rows pairs
    (fun k hk => hmul k (hrows k hk).1) (fun k hk => hnorm k (hrows k hk).1) B a).trans
    (hb A X hA hX rows pairs hrows hpairs a)

end HeckePort.Moments

end
