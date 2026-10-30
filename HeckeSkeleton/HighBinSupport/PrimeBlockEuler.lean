import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Euler summation with several exponents and finitely many marked primes

The local exponent type may be a product, so all four ideal variables can
remain in one prime block. A fixed finite mark set is included in every
finite product. Its local value at exponent zero may vanish; only primes
outside that set are required to have value one at zero.

The finite-support exhaustion is the same unconditional-series argument
used by `HeckeGeneral.Analysis.FiniteSupportEuler`, with arbitrary local
series in place of geometric powers. Absolute convergence is an explicit
analytic premise of this general lemma, discharged by the actual four-ideal
majorant in the arithmetic application.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
noncomputable section

namespace HighBin.PrimeBlockEuler

open Filter
open scoped Classical BigOperators Topology

variable {ι κ : Type*} [AddCommMonoid κ]

abbrev Supported (S : Finset ι) := {e : ι →₀ κ // e.support ⊆ S}

/-- A finite product includes every prime in its specified finite set. -/
def finiteWeight (g : ι → κ → ℂ) (S : Finset ι) (e : ι →₀ κ) : ℂ :=
  ∏ p ∈ S, g p (e p)

/-- The fixed marks are inspected even when their exponent is zero. -/
def weight (g : ι → κ → ℂ) (Q : Finset ι) (e : ι →₀ κ) : ℂ :=
  finiteWeight g (e.support ∪ Q) e

def insertEquiv (S : Finset ι) (p : ι) (hp : p ∉ S) :
    κ × Supported (κ := κ) S ≃ Supported (κ := κ) (insert p S) where
  toFun x := ⟨Finsupp.single p x.1 + x.2.val, by
    intro q hq
    by_cases hqp : q = p
    · simp [hqp]
    apply Finset.mem_insert_of_mem
    apply x.2.property
    rw [Finsupp.mem_support_iff] at hq ⊢
    simpa [Finsupp.single_apply, hqp] using hq⟩
  invFun e := (e.val p, ⟨e.val.erase p, by
    intro q hq
    rw [Finsupp.support_erase, Finset.mem_erase] at hq
    exact (Finset.mem_insert.mp (e.property hq.2)).resolve_left hq.1⟩)
  left_inv x := by
    apply Prod.ext
    · have hp0 : x.2.val p = 0 :=
        Finsupp.notMem_support_iff.mp (fun h => hp (x.2.property h))
      simp [hp0]
    · apply Subtype.ext
      ext q
      by_cases hqp : q = p
      · subst q
        have hp0 : x.2.val p = 0 :=
          Finsupp.notMem_support_iff.mp (fun h => hp (x.2.property h))
        simp [hp0]
      · simp [hqp]
  right_inv e := by
    apply Subtype.ext
    ext q
    by_cases hqp : q = p
    · subst q
      simp
    · simp [hqp]

theorem finiteWeight_insertEquiv (g : ι → κ → ℂ)
    (S : Finset ι) (p : ι) (hp : p ∉ S) (x : κ × Supported (κ := κ) S) :
    finiteWeight g (insert p S) (insertEquiv S p hp x).val =
      g p x.1 * finiteWeight g S x.2.val := by
  have hp0 : x.2.val p = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hp (x.2.property h))
  unfold finiteWeight
  rw [Finset.prod_insert hp]
  congr 1
  · change g p ((Finsupp.single p x.1 + x.2.val) p) = g p x.1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hp0, add_zero]
  · apply Finset.prod_congr rfl
    intro q hq
    have hqp : q ≠ p := fun h => hp (h ▸ hq)
    change g q ((Finsupp.single p x.1 + x.2.val) q) = g q (x.2.val q)
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hqp, zero_add]

set_option maxHeartbeats 1200000 in
/-- A finite prime set sums all local exponent blocks, with no truncation. -/
theorem hasSum_supported (g : ι → κ → ℂ)
    (hg : ∀ p, Summable (fun n : κ => ‖g p n‖)) (S : Finset ι) :
    Summable (fun e : Supported (κ := κ) S => ‖finiteWeight g S e.val‖) ∧
      HasSum (fun e : Supported (κ := κ) S => finiteWeight g S e.val)
        (∏ p ∈ S, ∑' n : κ, g p n) := by
  induction S using Finset.induction with
  | empty =>
    let : Unique (Supported (κ := κ) (∅ : Finset ι)) :=
      { default := ⟨0, by simp⟩
        uniq := by
          intro e
          apply Subtype.ext
          apply Finsupp.support_eq_empty.mp
          exact Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => by
            simpa using e.property hp) }
    constructor
    · exact Summable.of_finite
    · rw [Finset.prod_empty]
      have h : (∑ e : Supported (κ := κ) (∅ : Finset ι),
          finiteWeight g ∅ e.val) = 1 := by simp [finiteWeight]
      exact h ▸ hasSum_fintype (fun e : Supported (κ := κ) (∅ : Finset ι) =>
        finiteWeight g ∅ e.val)
  | insert p S hp ih =>
    constructor
    · apply (insertEquiv (κ := κ) S p hp).summable_iff.mp
      change Summable (fun x : κ × Supported (κ := κ) S =>
        ‖finiteWeight g (insert p S) (insertEquiv S p hp x).val‖)
      simp only [finiteWeight_insertEquiv, norm_mul]
      exact (hg p).mul_of_nonneg ih.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    · rw [Finset.prod_insert hp]
      apply (insertEquiv (κ := κ) S p hp).hasSum_iff.mp
      change HasSum (fun x : κ × Supported (κ := κ) S =>
        finiteWeight g (insert p S) (insertEquiv S p hp x).val) _
      simp only [finiteWeight_insertEquiv]
      have habs : Summable (fun x : κ × Supported (κ := κ) S =>
          ‖g p x.1‖ * ‖finiteWeight g S x.2.val‖) :=
        (hg p).mul_of_nonneg ih.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hprod : Summable (fun x : κ × Supported (κ := κ) S =>
          g p x.1 * finiteWeight g S x.2.val) :=
        Summable.of_norm (by simpa only [norm_mul] using habs)
      have hval : (∑' n : κ, g p n) *
          (∑' e : Supported (κ := κ) S, finiteWeight g S e.val) =
          ∑' x : κ × Supported (κ := κ) S, g p x.1 * finiteWeight g S x.2.val :=
        tsum_mul_tsum_of_summable_norm (hg p) ih.1
      rw [ih.2.tsum_eq] at hval
      exact hval.symm ▸ hprod.hasSum

/-- Enlarging beyond the support and the marks adds only unit factors. -/
theorem weight_eq_finiteWeight (g : ι → κ → ℂ) (Q S : Finset ι)
    (hg0 : ∀ p ∉ Q, g p 0 = 1) (e : ι →₀ κ)
    (he : e.support ⊆ S) (hQ : Q ⊆ S) :
    weight g Q e = finiteWeight g S e := by
  unfold weight finiteWeight
  apply Finset.prod_subset (Finset.union_subset he hQ)
  intro p _ hp
  have hpe : p ∉ e.support := fun h => hp (Finset.mem_union_left Q h)
  have hpQ : p ∉ Q := fun h => hp (Finset.mem_union_right e.support h)
  rw [Finsupp.notMem_support_iff.mp hpe, hg0 p hpQ]

/-- Absolute convergence justifies the complete Euler rearrangement,
including primes whose marked local constant coefficient vanishes. -/
theorem hasProd_of_summable_weight (g : ι → κ → ℂ) (Q : Finset ι)
    (hg0 : ∀ p ∉ Q, g p 0 = 1)
    (hg : ∀ p, Summable (fun n : κ => ‖g p n‖))
    (hw : Summable (fun e : ι →₀ κ => ‖weight g Q e‖)) :
    HasProd (fun p => ∑' n : κ, g p n) (∑' e : ι →₀ κ, weight g Q e) := by
  change Tendsto (fun S : Finset ι => ∏ p ∈ S, ∑' n : κ, g p n)
    atTop (𝓝 (∑' e : ι →₀ κ, weight g Q e))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := hw.of_norm.tsum_vanishing (Metric.ball_mem_nhds 0 hε)
  let S : Finset ι := Q ∪ T.biUnion Finsupp.support
  refine ⟨S, fun U hU => ?_⟩
  have hQU : Q ⊆ U := (Finset.subset_union_left).trans hU
  have hdisj : Disjoint (↑T : Set (ι →₀ κ)) {e : ι →₀ κ | e.support ⊆ U}ᶜ := by
    refine Set.disjoint_left.mpr ?_
    intro e he hnot
    apply hnot
    intro p hp
    apply hU
    exact Finset.mem_union_right Q (Finset.mem_biUnion.mpr ⟨e, he, hp⟩)
  have htail := hT _ hdisj.symm
  rw [Metric.mem_ball, dist_zero_right] at htail
  have hsum := hw.of_norm.tsum_subtype_add_tsum_subtype_compl
    {e : ι →₀ κ | e.support ⊆ U}
  change (∑' e : Supported (κ := κ) U, weight g Q e.val) +
    (∑' e : ↑({e : ι →₀ κ | e.support ⊆ U}ᶜ), weight g Q e.val) =
      ∑' e : ι →₀ κ, weight g Q e at hsum
  have hfinite : (∑' e : Supported (κ := κ) U, weight g Q e.val) =
      ∏ p ∈ U, ∑' n : κ, g p n := by
    calc
      _ = ∑' e : Supported (κ := κ) U, finiteWeight g U e.val :=
        tsum_congr (fun e => weight_eq_finiteWeight g Q U hg0 e.val e.property hQU)
      _ = _ := (hasSum_supported g hg U).2.tsum_eq
  rw [dist_eq_norm, norm_sub_rev, ← hfinite, ← hsum, add_sub_cancel_left]
  exact htail

/-- The application form preserves an already defined, absolutely
convergent coefficient function. Its finite factorization is used as an
equality, so no replacement series is introduced. -/
theorem hasProd_of_term_factorization (g : ι → κ → ℂ) (Q : Finset ι)
    (f : (ι →₀ κ) → ℂ) (hf : ∀ e, f e = weight g Q e)
    (hg0 : ∀ p ∉ Q, g p 0 = 1)
    (hg : ∀ p, Summable (fun n : κ => ‖g p n‖))
    (habs : Summable (fun e => ‖f e‖)) :
    HasProd (fun p => ∑' n : κ, g p n) (∑' e, f e) := by
  have hw : Summable (fun e => ‖weight g Q e‖) :=
    habs.congr (fun e => congrArg norm (hf e))
  have h := hasProd_of_summable_weight g Q hg0 hg hw
  rwa [show (∑' e, weight g Q e) = ∑' e, f e from
    tsum_congr (fun e => (hf e).symm)] at h

#print axioms hasProd_of_summable_weight
#print axioms hasProd_of_term_factorization

end HighBin.PrimeBlockEuler
