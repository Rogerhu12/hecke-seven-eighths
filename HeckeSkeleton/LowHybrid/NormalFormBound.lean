import HeckeSkeleton.LowHybrid.BlockAdmissible

/-!
# The original hybrid energy from its two sieve inputs

The hypotheses in `FiniteInputs` are only finite support, squarefreeness,
norm cutoffs, product-fiber counts, and scalar harmonic bounds. In particular,
the structure contains no operator estimate, block-energy estimate, or
normal-form row identity. The latter identities and the block bounds have
already been proved from the explicit original coefficients.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

structure FiniteInputs (sf : I → Prop)
    (rows marks columns cubes ds rs : Finset I) (C : Completion columns cubes)
    (ts cs ms hs : I → I → Finset I)
    (goodPairs goodMC : I → I → Finset (I × I)) (qset jset : Finset I)
    (K Y N L Delta Dq Dc Ht Hc Hh : ℝ) : Prop where
  local_pairs : ∀ k ∈ rows, S.divisorPairs k ⊆ ds ×ˢ rs
  pair_count : ∀ k ∈ rows, ((S.divisorPairs k).card : ℝ) ≤ Delta
  quotient_rows : ∀ d ∈ ds, ∀ r ∈ rs, ∀ k ∈ rows,
    (d, r) ∈ S.divisorPairs k →
      sf (S.quotientTwice d r k) ∧ S.normI (S.quotientTwice d r k) ≤ K
  quadratic_support : ∀ j ∈ qset, sf j ∧ S.normI j ≤ Y
  cubic_support : ∀ j ∈ jset, sf j ∧ S.normI j ≤ N
  mark_columns : ∀ d ∈ ds, ∀ p ∈ S.markQuotients marks d, sf p ∧ S.normI p ≤ L
  quadratic_rectangle : ∀ d ∈ ds, ∀ r ∈ rs, goodPairs d r ⊆ ms d r ×ˢ hs d r
  cubic_rectangle : ∀ d ∈ ds, ∀ r ∈ rs, goodMC d r ⊆ ms d r ×ˢ cs d r
  quadratic_products : ∀ d ∈ ds, ∀ r ∈ rs, ∀ u ∈ goodPairs d r, u.1 * u.2 ∈ qset
  quadratic_fibers : ∀ d ∈ ds, ∀ r ∈ rs, ∀ j ∈ qset,
    (((goodPairs d r).filter fun u => u.1 * u.2 = j).card : ℝ) ≤ Dq
  cubic_products : ∀ d ∈ ds, ∀ r ∈ rs, ∀ u ∈ goodMC d r, u.2 * u.1 ∈ jset
  cubic_fibers : ∀ d ∈ ds, ∀ r ∈ rs, ∀ j ∈ jset,
    (((goodMC d r).filter fun u => u.2 * u.1 = j).card : ℝ) ≤ Dc
  box : ∀ d ∈ ds, ∀ r ∈ rs,
    S.blockSupport C.support r ⊆ completedBox (ts d r) (cs d r) (ms d r) (hs d r)
  quadratic_completion : ∀ d ∈ ds, ∀ r ∈ rs, ∀ v ∈ S.blockSupport C.support r,
    (v.2.2.1, v.2.2.2) ∈ goodPairs d r
  cubic_completion : ∀ d ∈ ds, ∀ r ∈ rs, ∀ v ∈ S.blockSupport C.support r,
    (v.2.2.1, v.2.1) ∈ goodMC d r
  t_harmonic : ∀ d ∈ ds, ∀ r ∈ rs, (∑ t ∈ ts d r, 1 / S.normI t) ≤ Ht
  c_harmonic : ∀ d ∈ ds, ∀ r ∈ rs, (∑ c ∈ cs d r, 1 / S.normI c) ≤ Hc
  h_harmonic : ∀ d ∈ ds, ∀ r ∈ rs, (∑ h ∈ hs d r, 1 / S.normI h) ≤ Hh

/-- A complete finite bound for the literal original normalized hybrid
energy. The sole analytic hypotheses are the quadratic and cubic sieve
inputs. All combinatorial costs and the original column mass remain visible,
ready for arithmetic epsilon absorption. The constant is uniform in every
scale, finite support, divisor, and coefficient family. -/
theorem hybridEnergy_finite_bound (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hmu : ∀ x, ‖S.mu x‖ ≤ 1)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol) (eta : ℝ) (heta : 0 < eta) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K Y N L : ℝ, 1 ≤ K → 1 ≤ Y → 1 ≤ N → 1 ≤ L →
    ∀ (rows marks columns cubes ds rs : Finset I) (C : Completion columns cubes)
      (ts cs ms hs : I → I → Finset I)
      (goodPairs goodMC : I → I → Finset (I × I)) (qset jset : Finset I)
      (a : I → ℂ) (beta : I → I → ℂ) (B Delta Dq Dc Ht Hc Hh : ℝ),
      0 ≤ B → 0 ≤ Delta → 0 ≤ Dq → 0 ≤ Dc → 0 ≤ Ht → 0 ≤ Hc → 0 ≤ Hh →
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      S.FiniteInputs sf rows marks columns cubes ds rs C ts cs ms hs goodPairs goodMC
        qset jset K Y N L Delta Dq Dc Ht Hc Hh →
      hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes ≤
        C0 * Delta * Dq * Dc * (K * Y * N * L) ^ eta * (K + Y) * B *
          (N + L + (N * L) ^ (2 / 3 : ℝ)) * Ht ^ 2 * Hc * Hh *
          (∑ d ∈ ds, S.columnMass a marks d / S.normI d) *
          (∑ r ∈ rs, 1 / S.normI r) := by
  obtain ⟨Cq, Cc, hCq, hCc, hadmissible⟩ :=
    S.weightedBlock_admissible_from_sieves sf hnorm hq hc eta heta
  refine ⟨Cq * Cc, mul_pos hCq hCc, ?_⟩
  intro K Y N L hK hY hN hL rows marks columns cubes ds rs C ts cs ms hs
    goodPairs goodMC qset jset a beta B Delta Dq Dc Ht Hc Hh
    hB hDelta hDq hDc hHt hHc hHh hbeta hcubes H
  let Q := Cq * (K * Y) ^ eta * (K + Y) * Dq
  let V := Cc * (N * L) ^ eta * (N + L + (N * L) ^ (2 / 3 : ℝ)) * Dc
  let block := fun d r => S.weightedBlock a beta marks C.support
    (ts d r) (cs d r) (ms d r) (hs d r) (goodPairs d r) (goodMC d r) d r
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hpos (x : I) : 0 < S.normI x := lt_of_lt_of_le zero_lt_one (hnorm x)
  have hloc (k : I) (hk : k ∈ rows) (d : I) (hd : d ∈ S.divisors k)
      (r : I) (hr : r ∈ S.divisors (S.quotient d k)) : d ∈ ds ∧ r ∈ rs := by
    exact Finset.mem_product.mp (H.local_pairs k hk ((S.mem_divisorPairs k d r).mpr ⟨hd, hr⟩))
  have hnormal (k : I) (hk : k ∈ rows) :
      hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
        ∑ dr ∈ S.divisorPairs k, (S.mu dr.1 * S.mu dr.2) *
          (((1 : ℂ) / (Real.sqrt (S.normI dr.1) : ℂ)) * (block dr.1 dr.2).row k) := by
    apply S.hybridRow_eq_weightedBlocks a beta marks columns cubes C ts cs ms hs goodPairs goodMC k
    · intro d hd r hr
      have hm := hloc k hk d hd r hr
      exact H.box d hm.1 r hm.2
    · intro d hd r hr
      have hm := hloc k hk d hd r hr
      exact H.quadratic_completion d hm.1 r hm.2
    · intro d hd r hr
      have hm := hloc k hk d hd r hr
      exact H.cubic_completion d hm.1 r hm.2
  have hblocks (d : I) (hd : d ∈ ds) (r : I) (hr : r ∈ rs) :
      (block d r).Admissible (rows.filter fun k => (d, r) ∈ S.divisorPairs k)
        Q V (B / S.normI r) (S.columnMass a marks d) := by
    apply hadmissible K Y N L hK hY hN hL
      (rows.filter fun k => (d, r) ∈ S.divisorPairs k) marks columns cubes
      (ts d r) (cs d r) (ms d r) (hs d r) qset jset C
      (goodPairs d r) (goodMC d r) a beta d r B Dq Dc hB hDq hDc
    · intro k hk
      exact (S.mem_divisorPairs k d r).mp (Finset.mem_filter.mp hk).2
    · intro k hk
      exact H.quotient_rows d hd r hr k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    · exact H.quadratic_support
    · exact H.cubic_support
    · exact H.mark_columns d hd
    · exact H.quadratic_rectangle d hd r hr
    · exact H.cubic_rectangle d hd r hr
    · exact H.quadratic_products d hd r hr
    · exact H.quadratic_fibers d hd r hr
    · exact H.cubic_products d hd r hr
    · exact H.cubic_fibers d hd r hr
    · exact hbeta
    · exact hcubes
  have hmubound (k : I) (hk : k ∈ rows) (dr : I × I) (hdr : dr ∈ S.divisorPairs k) :
      ‖S.mu dr.1 * S.mu dr.2‖ ≤ 1 := by
    rw [_root_.norm_mul]
    exact (mul_le_mul (hmu dr.1) (hmu dr.2) (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb := hybrid_energy_of_weighted_blocks rows ds rs S.divisorPairs block
    (fun _ dr => S.mu dr.1 * S.mu dr.2) S.normI S.normI (S.columnMass a marks)
    Delta Q V B Ht Hc Hh hDelta hQ hV hB hHt hHc hHh
    (fun d hd => hpos d) (fun r hr => hpos r)
    (fun d hd => S.columnMass_nonneg a marks d) H.local_pairs hmubound H.pair_count hblocks
    (fun d hd r hr => H.t_harmonic d hd r hr)
    (fun d hd r hr => H.c_harmonic d hd r hr)
    (fun d hd r hr => H.h_harmonic d hd r hr)
  have hpow : (K * Y * N * L) ^ eta = (K * Y) ^ eta * (N * L) ^ eta := by
    rw [show K * Y * N * L = (K * Y) * (N * L) by ring]
    exact Real.mul_rpow (by positivity) (by positivity)
  calc
    hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes =
        ∑ k ∈ rows, ‖∑ dr ∈ S.divisorPairs k, (S.mu dr.1 * S.mu dr.2) *
          (((1 : ℂ) / (Real.sqrt (S.normI dr.1) : ℂ)) * (block dr.1 dr.2).row k)‖ ^ 2 := by
      unfold hybridEnergy
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnormal k hk]
    _ ≤ _ := hb.trans_eq (by dsimp only [Q, V]; rw [hpow]; ring)

end Arithmetic

#print axioms Arithmetic.hybridEnergy_finite_bound

end
end HeckeSkeleton.LowHybrid.NormalForm
