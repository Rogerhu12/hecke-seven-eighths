import HeckeSkeleton.LowHybrid.CanonicalSupport
import HeckeSkeleton.LowHybrid.NormalFormBound
import HeckeSkeleton.LowHybrid.DivisorEnvelope

/-!
# All finite normal-form inputs from the original arithmetic supports

The sets used by the proof are actual complete norm cutoffs. The completed
support, both good product rectangles, both squarefree target sets, and every
product multiplicity are constructed here. In particular, applications do
not supply a `FiniteInputs` certificate independently.
-/

namespace HeckeSkeleton.LowHybrid.PrimeArithmetic

open scoped BigOperators Classical
open HeckeSkeleton.LowHybrid.NormalForm

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def squarefreeCutoff (cutoff : ℝ → Finset A) (X : ℝ) : Finset A :=
  (cutoff X).filter (Squarefree coords)

def quadraticPairs (S : Arithmetic A) (cutoff : ℝ → Finset A) (N B : ℝ) :
    Finset (A × A) :=
  (cutoff N ×ˢ cutoff B).filter fun u =>
    Squarefree coords (u.1 * u.2) ∧ S.normI (u.1 * u.2) ≤ N * B

def cubicPairs (S : Arithmetic A) (cutoff : ℝ → Finset A) (N : ℝ) :
    Finset (A × A) :=
  (cutoff N ×ˢ cutoff N).filter fun u =>
    Squarefree coords (u.2 * u.1) ∧ S.normI (u.2 * u.1) ≤ N

def cutoffHarmonic (S : Arithmetic A) (cutoff : ℝ → Finset A) (X : ℝ) : ℝ :=
  ∑ a ∈ cutoff X, 1 / S.normI a

theorem arithmetic_quotient_dvd (S : Arithmetic A) (d k : A) (hd : d ∣ k) :
    S.quotient d k ∣ k := by
  refine ⟨d, ?_⟩
  rw [mul_comm]
  exact (S.quotient_spec d k hd).symm

theorem divisor_pair_norms (S : Arithmetic A) (hnorm : ∀ x, 1 ≤ S.normI x)
    {d r k : A} (h : (d, r) ∈ S.divisorPairs k) :
    S.normI d ≤ S.normI k ∧ S.normI r ≤ S.normI k := by
  obtain ⟨hd, hr⟩ := (S.mem_divisorPairs k d r).mp h
  have hdk := S.divisor_dvd k d hd
  have hqk := arithmetic_quotient_dvd S d k hdk
  exact ⟨arithmetic_norm_le_of_dvd S hnorm hdk,
    arithmetic_norm_le_of_dvd S hnorm ((S.divisor_dvd _ r hr).trans hqk)⟩

theorem divisor_pair_count_le (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hdiv : S.divisors = divisors coords)
    (cutoff : ℝ → Finset A)
    (hmem : ∀ X a, a ∈ cutoff X ↔ S.normI a ≤ X)
    (K : ℝ) (k : A) (hk : S.normI k ≤ K) :
    ((S.divisorPairs k).card : ℝ) ≤
      divisorCountEnvelope cutoff (divisors coords) K ^ 2 := by
  let D := divisorCountEnvelope cutoff (divisors coords) K
  have hD : 0 ≤ D := divisorCountEnvelope_nonneg _ _ _
  have hcount (a : A) (ha : S.normI a ≤ K) : ((S.divisors a).card : ℝ) ≤ D := by
    rw [hdiv]
    exact divisor_count_le_envelope cutoff (divisors coords) K a ((hmem K a).mpr ha)
  rw [S.card_divisorPairs, Nat.cast_sum]
  calc
    (∑ d ∈ S.divisors k, ((S.divisors (S.quotient d k)).card : ℝ)) ≤
        ∑ _d ∈ S.divisors k, D := by
      apply Finset.sum_le_sum
      intro d hd
      exact hcount _ ((arithmetic_norm_le_of_dvd S hnorm
        (arithmetic_quotient_dvd S d k (S.divisor_dvd k d hd))).trans hk)
    _ = ((S.divisors k).card : ℝ) * D := by simp
    _ ≤ D * D := mul_le_mul_of_nonneg_right (hcount k hk) hD
    _ = _ := (pow_two D).symm

theorem canonical_finite_inputs
    (S : Arithmetic A) (hnorm : ∀ x, 1 ≤ S.normI x)
    (hdiv : S.divisors = divisors coords)
    (cutoff : ℝ → Finset A)
    (hmem : ∀ X a, a ∈ cutoff X ↔ S.normI a ≤ X)
    (K N B L : ℝ) (rows marks columns cubes : Finset A)
    (hrows : ∀ k ∈ rows, Squarefree coords k ∧ S.normI k ≤ K)
    (hmarks : ∀ p ∈ marks, Squarefree coords p ∧ S.normI p ≤ L)
    (hcolumns : ∀ n ∈ columns, Squarefree coords n ∧ S.normI n ≤ N)
    (hcubes : ∀ b ∈ cubes, S.normI b ≤ B) :
    S.FiniteInputs (Squarefree coords) rows marks columns cubes
      (cutoff K) (cutoff K) (completion coords columns cubes)
      (fun _ _ => cutoff B) (fun _ _ => cutoff N)
      (fun _ _ => cutoff N) (fun _ _ => cutoff B)
      (fun _ _ => quadraticPairs coords S cutoff N B)
      (fun _ _ => cubicPairs coords S cutoff N)
      (squarefreeCutoff coords cutoff (N * B)) (squarefreeCutoff coords cutoff N)
      K (N * B) N L
      (divisorCountEnvelope cutoff (divisors coords) K ^ 2)
      (divisorCountEnvelope cutoff (divisors coords) (N * B))
      (divisorCountEnvelope cutoff (divisors coords) N)
      (cutoffHarmonic S cutoff B) (cutoffHarmonic S cutoff N)
      (cutoffHarmonic S cutoff B) := by
  have hcount (X : ℝ) (j : A) (hj : S.normI j ≤ X) :
      ((divisors coords j).card : ℝ) ≤ divisorCountEnvelope cutoff (divisors coords) X :=
    divisor_count_le_envelope cutoff (divisors coords) X j ((hmem X j).mpr hj)
  have hbds (r : A) (v : CompletedIndex A)
      (hv : v ∈ S.blockSupport (completion coords columns cubes).support r) :=
    canonical_block_bounds coords S hnorm N B hcolumns hcubes hv
  refine {
    local_pairs := ?_
    pair_count := ?_
    quotient_rows := ?_
    quadratic_support := ?_
    cubic_support := ?_
    mark_columns := ?_
    quadratic_rectangle := ?_
    cubic_rectangle := ?_
    quadratic_products := ?_
    quadratic_fibers := ?_
    cubic_products := ?_
    cubic_fibers := ?_
    box := ?_
    quadratic_completion := ?_
    cubic_completion := ?_
    t_harmonic := fun _ _ _ _ => le_rfl
    c_harmonic := fun _ _ _ _ => le_rfl
    h_harmonic := fun _ _ _ _ => le_rfl
  }
  · intro k hk dr hdr
    obtain ⟨hd, hr⟩ := divisor_pair_norms S hnorm hdr
    exact Finset.mem_product.mpr ⟨(hmem K dr.1).mpr (hd.trans (hrows k hk).2),
      (hmem K dr.2).mpr (hr.trans (hrows k hk).2)⟩
  · intro k hk
    exact divisor_pair_count_le coords S hnorm hdiv cutoff hmem K k (hrows k hk).2
  · intro d hd r hr k hk hdr
    obtain ⟨hdk, hrk⟩ := (S.mem_divisorPairs k d r).mp hdr
    have heq := S.quotientTwice_reconstruct d r k hdk hrk
    have hquot : S.quotientTwice d r k ∣ k :=
      ⟨d * r, by rw [mul_comm]; exact heq.symm⟩
    exact ⟨squarefree_of_dvd coords hquot (hrows k hk).1,
      (arithmetic_norm_le_of_dvd S hnorm hquot).trans (hrows k hk).2⟩
  · intro j hj
    have hm := Finset.mem_filter.mp hj
    exact ⟨hm.2, (hmem (N * B) j).mp hm.1⟩
  · intro j hj
    have hm := Finset.mem_filter.mp hj
    exact ⟨hm.2, (hmem N j).mp hm.1⟩
  · intro d hd p hp
    have hm := hmarks _ (S.markQuotients_mul_mem hp)
    have hpd : p ∣ d * p := ⟨d, mul_comm d p⟩
    exact ⟨squarefree_of_dvd coords hpd hm.1,
      (arithmetic_norm_le_of_dvd S hnorm hpd).trans hm.2⟩
  · intro d hd r hr u hu
    exact (Finset.mem_filter.mp hu).1
  · intro d hd r hr u hu
    exact (Finset.mem_filter.mp hu).1
  · intro d hd r hr u hu
    have hp := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨(hmem (N * B) _).mpr hp.2, hp.1⟩
  · intro d hd r hr j hj
    have hp := Finset.mem_filter.mp hj
    exact (product_fiber_card_le_squarefree_divisors coords _ j hp.2).trans
      (hcount (N * B) j ((hmem (N * B) j).mp hp.1))
  · intro d hd r hr u hu
    have hp := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨(hmem N _).mpr hp.2, hp.1⟩
  · intro d hd r hr j hj
    have hp := Finset.mem_filter.mp hj
    exact (swapped_product_fiber_card_le_squarefree_divisors coords _ j hp.2).trans
      (hcount N j ((hmem N j).mp hp.1))
  · intro d hd r hr v hv
    obtain ⟨ht, hc, hm, hh, hsf, hnb, hsfc, hcn⟩ := hbds r v hv
    exact Finset.mem_product.mpr ⟨(hmem B _).mpr ht,
      Finset.mem_product.mpr ⟨(hmem N _).mpr hc,
        Finset.mem_product.mpr ⟨(hmem N _).mpr hm, (hmem B _).mpr hh⟩⟩⟩
  · intro d hd r hr v hv
    obtain ⟨ht, hc, hm, hh, hsf, hnb, hsfc, hcn⟩ := hbds r v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(hmem N _).mpr hm, (hmem B _).mpr hh⟩, hsf, hnb⟩
  · intro d hd r hr v hv
    obtain ⟨ht, hc, hm, hh, hsf, hnb, hsfc, hcn⟩ := hbds r v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(hmem N _).mpr hm, (hmem N _).mpr hc⟩, hsfc, hcn⟩

#print axioms canonical_finite_inputs

end
end HeckeSkeleton.LowHybrid.PrimeArithmetic
