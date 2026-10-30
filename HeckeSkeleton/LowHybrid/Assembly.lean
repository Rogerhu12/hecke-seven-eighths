import HeckeSkeleton.LowHybrid.SieveComposition

/-!
# Row-localBlocks divisor Cauchy and weighted block assembly

This file supplies the outer finite-sum operations used before and after the
fixed-block quadratic--cubic composition. In particular, the divisor set is
allowed to depend on the row: the cost is its row-local cardinal bound, not
the cardinality of the union of all divisor sets.

The weighted column theorem records the identity behind
sum_D (1 / q(D)) * A_D = sum_P tau(P) * |a(P)|^2 / q(P).
Its hypotheses are a product map, norm multiplicativity and a fiber bound.
No hybrid energy estimate is assumed by that theorem.

The arithmetic divisor maps and their norm/counting estimates remain separate
from these purely finite results.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators

noncomputable section

/-- Cauchy on row-dependent index sets. This is the operation required by
each of the two complete moving coprimality-mask expansions. -/
theorem row_local_cauchy {K D : Type*}
    (rows : Finset K) (localBlocks : K → Finset D)
    (mu value : K → D → ℂ) (Delta : ℝ)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta) :
    (∑ k ∈ rows, ‖∑ d ∈ localBlocks k, mu k d * value k d‖ ^ 2) ≤
      Delta * ∑ k ∈ rows, ∑ d ∈ localBlocks k, ‖value k d‖ ^ 2 := by
  calc
    _ ≤ ∑ k ∈ rows, Delta * ∑ d ∈ localBlocks k, ‖value k d‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact bounded_coefficient_sum_sq_of_card (localBlocks k) (mu k) (value k)
        Delta (hmu k hk) (hcard k hk)
    _ = _ := (Finset.mul_sum ..).symm

/-- Exact transposition of a row-dependent finite support. The new row
restriction is explicit and is fixed once the outer block is fixed. -/
theorem row_local_positive_transpose {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (E : K → D → ℝ)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks) :
    (∑ k ∈ rows, ∑ d ∈ localBlocks k, E k d) =
      ∑ d ∈ blocks, ∑ k ∈ rows with d ∈ localBlocks k, E k d := by
  classical
  calc
    _ = ∑ k ∈ rows, ∑ d ∈ blocks, if d ∈ localBlocks k then E k d else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hf : blocks.filter (fun d => d ∈ localBlocks k) = localBlocks k := by
        ext d
        simp only [Finset.mem_filter]
        exact ⟨fun hd => hd.2, fun hd => ⟨hmap k hk d hd, hd⟩⟩
      rw [← Finset.sum_filter, hf]
    _ = ∑ d ∈ blocks, ∑ k ∈ rows, if d ∈ localBlocks k then E k d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter]

/-- The scalar column normalization stays inside each divisor term until
Cauchy is taken. Its squared norm then occurs exactly once. -/
theorem row_local_weighted_cauchy {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
    (Delta : ℝ)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks) :
    (∑ k ∈ rows,
      ‖∑ d ∈ localBlocks k, mu k d * (weight d * value k d)‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks,
        ‖weight d‖ ^ 2 * ∑ k ∈ rows with d ∈ localBlocks k, ‖value k d‖ ^ 2 := by
  classical
  calc
    _ ≤ Delta * ∑ k ∈ rows, ∑ d ∈ localBlocks k,
        ‖weight d * value k d‖ ^ 2 :=
      row_local_cauchy rows localBlocks mu (fun k d => weight d * value k d)
        Delta hmu hcard
    _ = Delta * ∑ d ∈ blocks, ∑ k ∈ rows with d ∈ localBlocks k,
        ‖weight d * value k d‖ ^ 2 := by
      rw [row_local_positive_transpose rows localBlocks blocks
        (fun k d => ‖weight d * value k d‖ ^ 2) hmap]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      simp_rw [norm_mul, mul_pow]
      exact (Finset.mul_sum ..).symm

/-- Combine previously proved fixed-block estimates without reintroducing
a moving mask. The bound function is only an outer assembly parameter. -/
theorem row_local_weighted_cauchy_of_block_bounds {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
    (Delta : ℝ) (bound : D → ℝ) (hDelta : 0 ≤ Delta)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks)
    (hblock : ∀ d ∈ blocks,
      (∑ k ∈ rows with d ∈ localBlocks k, ‖value k d‖ ^ 2) ≤ bound d) :
    (∑ k ∈ rows,
      ‖∑ d ∈ localBlocks k, mu k d * (weight d * value k d)‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks, ‖weight d‖ ^ 2 * bound d := by
  apply (row_local_weighted_cauchy rows localBlocks blocks mu weight value Delta
    hmu hcard hmap).trans
  apply mul_le_mul_of_nonneg_left _ hDelta
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (hblock d hd) (sq_nonneg _)

/-- Two row-local Cauchy steps keep both changing divisor sets visible.
The second set may depend on the row and on the first divisor. -/
theorem two_row_local_cauchy {K D R : Type*}
    (rows : Finset K) (outer : K → Finset D) (inner : K → D → Finset R)
    (mu : K → D → ℂ) (nu value : K → D → R → ℂ)
    (DeltaD DeltaR : ℝ) (hDeltaD : 0 ≤ DeltaD)
    (hmu : ∀ k ∈ rows, ∀ d ∈ outer k, ‖mu k d‖ ≤ 1)
    (hnu : ∀ k ∈ rows, ∀ d ∈ outer k, ∀ r ∈ inner k d, ‖nu k d r‖ ≤ 1)
    (hcardD : ∀ k ∈ rows, ((outer k).card : ℝ) ≤ DeltaD)
    (hcardR : ∀ k ∈ rows, ∀ d ∈ outer k, ((inner k d).card : ℝ) ≤ DeltaR) :
    (∑ k ∈ rows, ‖∑ d ∈ outer k, mu k d *
      (∑ r ∈ inner k d, nu k d r * value k d r)‖ ^ 2) ≤
      DeltaD * DeltaR *
        ∑ k ∈ rows, ∑ d ∈ outer k, ∑ r ∈ inner k d, ‖value k d r‖ ^ 2 := by
  have hfirst := row_local_cauchy rows outer mu
    (fun k d => ∑ r ∈ inner k d, nu k d r * value k d r)
    DeltaD hmu hcardD
  have hsecond :
      (∑ k ∈ rows, ∑ d ∈ outer k,
        ‖∑ r ∈ inner k d, nu k d r * value k d r‖ ^ 2) ≤
      DeltaR * ∑ k ∈ rows, ∑ d ∈ outer k,
        ∑ r ∈ inner k d, ‖value k d r‖ ^ 2 := by
    calc
      _ ≤ ∑ k ∈ rows, ∑ d ∈ outer k,
          DeltaR * ∑ r ∈ inner k d, ‖value k d r‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro d hd
        exact bounded_coefficient_sum_sq_of_card (inner k d) (nu k d) (value k d)
          DeltaR (hnu k hk d hd) (hcardR k hk d hd)
      _ = _ := by simp_rw [← Finset.mul_sum]
  apply hfirst.trans
  calc
    _ ≤ DeltaD * (DeltaR * ∑ k ∈ rows, ∑ d ∈ outer k,
        ∑ r ∈ inner k d, ‖value k d r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsecond hDeltaD
    _ = _ := by ring

/-- A weighted version of positive fiber regrouping. The actual total
coefficient mass on a fiber can replace its cardinality. -/
theorem weighted_positive_fiber_sum_le {X Y : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (phi : X → Y)
    (weight : X → ℝ) (E : Y → ℝ) (W : ℝ)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hE : ∀ y ∈ target, 0 ≤ E y)
    (hfiber : ∀ y ∈ target, (∑ x ∈ source with phi x = y, weight x) ≤ W) :
    (∑ x ∈ source, weight x * E (phi x)) ≤ W * ∑ y ∈ target, E y := by
  classical
  calc
    _ = ∑ y ∈ target, ∑ x ∈ source with phi x = y, weight x * E (phi x) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ y ∈ target, (∑ x ∈ source with phi x = y, weight x) * E y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ ∑ y ∈ target, W * E y := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right (hfiber y hy) (hE y hy)
    _ = _ := (Finset.mul_sum ..).symm

/-- Weighted column masses decrease under a pointwise norm contraction.
This absorbs the frozen zero-extended symbol and coprimality masks. -/
theorem weighted_column_mass_mono {D Q : Type*}
    (blocks : Finset D) (columns : D → Finset Q)
    (weight : D → ℝ) (normQ : Q → ℝ) (a b : D → Q → ℂ)
    (hw : ∀ d ∈ blocks, 0 ≤ weight d)
    (hn : ∀ d ∈ blocks, ∀ q ∈ columns d, 0 ≤ normQ q)
    (hab : ∀ d ∈ blocks, ∀ q ∈ columns d, ‖a d q‖ ≤ ‖b d q‖) :
    (∑ d ∈ blocks, weight d * ∑ q ∈ columns d, ‖a d q‖ ^ 2 / normQ q) ≤
      ∑ d ∈ blocks, weight d * ∑ q ∈ columns d, ‖b d q‖ ^ 2 / normQ q := by
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (hw d hd)
  apply Finset.sum_le_sum
  intro q hq
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hab d hd q hq) 2) (hn d hd q hq)

/-- Aggregate all divisor-column masses at once. The product normalization
uses multiplicativity, and each original column is charged only by its
factorization fiber size. This is the finite version of the divisor-weighted
original coefficient mass calculation after the two sieve steps. -/
theorem factorized_column_mass_le {D Q P : Type*}
    [DecidableEq D] [DecidableEq Q] [DecidableEq P]
    (blocks : Finset D) (columns : D → Finset Q) (target : Finset P)
    (product : D → Q → P) (normD : D → ℝ) (normQ : Q → ℝ) (normP : P → ℝ)
    (a : P → ℂ) (multiplicity : ℝ)
    (hD : ∀ d ∈ blocks, 0 < normD d)
    (hQ : ∀ d ∈ blocks, ∀ q ∈ columns d, 0 < normQ q)
    (hP : ∀ p ∈ target, 0 < normP p)
    (hmap : ∀ d ∈ blocks, ∀ q ∈ columns d, product d q ∈ target)
    (hnorm : ∀ d ∈ blocks, ∀ q ∈ columns d,
      normP (product d q) = normD d * normQ q)
    (hfiber : ∀ p ∈ target,
      (((blocks.sigma columns).filter fun dq => product dq.1 dq.2 = p).card : ℝ) ≤
        multiplicity) :
    (∑ d ∈ blocks, (1 / normD d) *
      ∑ q ∈ columns d, ‖a (product d q)‖ ^ 2 / normQ q) ≤
      multiplicity * ∑ p ∈ target, ‖a p‖ ^ 2 / normP p := by
  classical
  have hsmap : ∀ dq ∈ blocks.sigma columns, product dq.1 dq.2 ∈ target := by
    intro dq hdq
    have hm := Finset.mem_sigma.mp hdq
    exact hmap dq.1 hm.1 dq.2 hm.2
  calc
    _ = ∑ dq ∈ blocks.sigma columns,
        ‖a (product dq.1 dq.2)‖ ^ 2 / normP (product dq.1 dq.2) := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hnorm d hd q hq]
      field_simp [ne_of_gt (hD d hd), ne_of_gt (hQ d hd q hq)] <;> ring
    _ ≤ _ := positive_fiber_sum_le (blocks.sigma columns) target
      (fun dq => product dq.1 dq.2) (fun p => ‖a p‖ ^ 2 / normP p)
      multiplicity hsmap
      (fun p hp => div_nonneg (sq_nonneg _) (le_of_lt (hP p hp))) hfiber

/-- A positive pullback may use the coefficient mass on each fiber.
This is useful when the full beta coefficient is smaller than its uniform bound. -/
theorem weighted_row_fiber_sieve {X Y P : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (columns : Finset P)
    (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (beta : X → ℂ)
    (W S : ℝ) (hW : 0 ≤ W)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, (∑ x ∈ source with phi x = y, ‖beta x‖ ^ 2) ≤ W)
    (hsieve : ∀ u : P → ℂ,
      (∑ y ∈ target, ‖∑ p ∈ columns, u p * chi p y‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖u p‖ ^ 2) :
    (∑ x ∈ source,
      ‖beta x * (∑ p ∈ columns, a p * chi p (phi x))‖ ^ 2) ≤
      W * S * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
  have h := weighted_positive_fiber_sum_le source target phi
    (fun x => ‖beta x‖ ^ 2)
    (fun y => ‖∑ p ∈ columns, a p * chi p y‖ ^ 2) W
    hmap (fun _ _ => sq_nonneg _) hfiber
  simp_rw [norm_mul, mul_pow]
  apply h.trans
  calc
    _ ≤ W * (S * ∑ p ∈ columns, ‖a p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hsieve a) hW
    _ = _ := by ring

/-- Assemble a family of actual quadratic--cubic blocks through a row-local
divisor expansion. Every block estimate is derived here from two operator
sieve bounds, the Cauchy count, the product fiber count, and column mass.

The index d may include fixed arithmetic data, but its row-dependent support
is kept in localBlocks. The quadratic rows are exactly the corresponding
filtered rows. No hybrid conclusion is among the hypotheses. -/
theorem assembled_blocks_energy_of_two_sieves
    {K D M H C J P : Type*}
    [DecidableEq K] [DecidableEq D] [DecidableEq M]
    [DecidableEq H] [DecidableEq C] [DecidableEq J]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (pairs : D → Finset (M × H)) (cset : D → M → Finset C)
    (hset : D → Finset H) (mc : D → Finset (M × C))
    (jset : D → Finset J) (pset : D → Finset P)
    (q : D → K → M × H → ℂ) (phi : D → M × C → J)
    (chi : D → P → J → ℂ)
    (a : D → H → P → ℂ) (beta : D → C → M → H → ℂ)
    (mu : K → D → ℂ) (weight : D → ℂ)
    (Q S Cbound Fbound Ebound : D → ℝ) (Delta : ℝ)
    (hDelta : 0 ≤ Delta)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hblockMap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks)
    (hQ : ∀ d ∈ blocks, 0 ≤ Q d)
    (hS : ∀ d ∈ blocks, 0 ≤ S d)
    (hC : ∀ d ∈ blocks, 0 ≤ Cbound d)
    (hF : ∀ d ∈ blocks, 0 ≤ Fbound d)
    (hcount : ∀ d ∈ blocks, ∀ u ∈ pairs d,
      ((cset d u.1).card : ℝ) ≤ Cbound d)
    (hbeta : ∀ d ∈ blocks, ∀ u ∈ pairs d, ∀ c ∈ cset d u.1,
      ‖beta d c u.1 u.2‖ ≤ 1)
    (hh : ∀ d ∈ blocks, ∀ u ∈ pairs d, u.2 ∈ hset d)
    (hmc : ∀ d ∈ blocks, ∀ u ∈ pairs d, ∀ c ∈ cset d u.1,
      (u.1, c) ∈ mc d)
    (hmap : ∀ d ∈ blocks, ∀ u ∈ mc d, phi d u ∈ jset d)
    (hfiber : ∀ d ∈ blocks, ∀ j ∈ jset d,
      (((mc d).filter fun u => phi d u = j).card : ℝ) ≤ Fbound d)
    (hcoef : ∀ d ∈ blocks, ∀ h ∈ hset d,
      (∑ p ∈ pset d, ‖a d h p‖ ^ 2) ≤ Ebound d)
    (hquadratic : ∀ d ∈ blocks, ∀ f : M × H → ℂ,
      (∑ k ∈ rows with d ∈ localBlocks k,
        ‖∑ u ∈ pairs d, q d k u * f u‖ ^ 2) ≤
        Q d * ∑ u ∈ pairs d, ‖f u‖ ^ 2)
    (hcubic : ∀ d ∈ blocks, ∀ u : P → ℂ,
      (∑ j ∈ jset d, ‖∑ p ∈ pset d, u p * chi d p j‖ ^ 2) ≤
        S d * ∑ p ∈ pset d, ‖u p‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ d ∈ localBlocks k, mu k d * (weight d *
      (∑ u ∈ pairs d, q d k u *
        (∑ c ∈ cset d u.1, beta d c u.1 u.2 *
          (∑ p ∈ pset d, a d u.2 p * chi d p (phi d (u.1, c))))))‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks, ‖weight d‖ ^ 2 *
        (Q d * Cbound d * ((hset d).card : ℝ) * Fbound d * S d * Ebound d) := by
  classical
  let value : K → D → ℂ := fun k d =>
    ∑ u ∈ pairs d, q d k u *
      (∑ c ∈ cset d u.1, beta d c u.1 u.2 *
        (∑ p ∈ pset d, a d u.2 p * chi d p (phi d (u.1, c))))
  have hblock (d : D) (hd : d ∈ blocks) :
      (∑ k ∈ rows with d ∈ localBlocks k, ‖value k d‖ ^ 2) ≤
        Q d * Cbound d * ((hset d).card : ℝ) * Fbound d * S d * Ebound d := by
    simpa only [value] using
      fixed_block_energy_of_two_sieves
        (rows.filter fun k => d ∈ localBlocks k)
        (pairs d) (cset d) (hset d) (mc d) (jset d) (pset d)
        (q d) (phi d) (chi d) (a d) (beta d)
        (Q d) (S d) (Cbound d) (Fbound d) (Ebound d)
        (hQ d hd) (hS d hd) (hC d hd) (hF d hd)
        (hcount d hd) (hbeta d hd) (hh d hd) (hmc d hd)
        (hmap d hd) (hfiber d hd) (hcoef d hd)
        (hquadratic d hd) (hcubic d hd)
  exact row_local_weighted_cauchy_of_block_bounds
    rows localBlocks blocks mu weight value Delta
    (fun d => Q d * Cbound d * ((hset d).card : ℝ) * Fbound d * S d * Ebound d)
    hDelta hmu hcard hblockMap hblock


#print axioms row_local_cauchy
#print axioms row_local_positive_transpose
#print axioms row_local_weighted_cauchy
#print axioms row_local_weighted_cauchy_of_block_bounds
#print axioms two_row_local_cauchy
#print axioms weighted_positive_fiber_sum_le
#print axioms weighted_column_mass_mono
#print axioms factorized_column_mass_le
#print axioms weighted_row_fiber_sieve
#print axioms assembled_blocks_energy_of_two_sieves

end
end HeckeSkeleton.LowHybrid

