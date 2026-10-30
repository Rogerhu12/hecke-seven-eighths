import HeckeSkeleton.LowHybrid.NormalFormSupport
import HeckeSkeleton.LowHybrid.ProductBounds

/-!
# Admissibility of the actual normal-form block from the two sieve inputs

The block coefficients and supports are those constructed from the original
hybrid row. The coefficient budget follows from the inherited original cube
support. The two operator bounds are derived from the original arithmetic
sieves, including the quotient-row pullback and both product fibers.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

theorem norm_quadratic_le_one (x y : I) : ‖S.quadratic x y‖ ≤ 1 := by
  unfold quadratic
  rw [norm_pow]
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _)
    (norm_symbol_le_one S.symbol S.cop S.six x y) 3).trans_eq (one_pow 3)

theorem norm_cubic_le_one (x y : I) : ‖S.cubic x y‖ ≤ 1 :=
  norm_symbol_neg_two_le_one S.symbol S.cop S.six x y

theorem norm_mask_le_one (x y : I) : ‖S.mask x y‖ ≤ 1 :=
  complex_mask_norm_le_one (S.cop x y)

theorem norm_firstBeta_le (beta : I → I → ℂ) (d n b : I) :
    ‖S.firstBeta beta d n b‖ ≤ ‖beta n b‖ := by
  exact twisted_beta_norm_le (beta n b) (S.symbol d (n * b)) (S.cubic d n)
    (S.cop d b) (norm_symbol_le_one S.symbol S.cop S.six d (n * b))
    (S.norm_cubic_le_one d n)

theorem norm_blockBetaCore_le (beta : I → I → ℂ) (d r t c m h : I) :
    ‖S.blockBetaCore beta d r t c m h‖ ≤ ‖beta (r * c * m) (r * c * h * t ^ 2)‖ :=
  (mul_contraction_norm _ _ (S.norm_quadratic_le_one r (m * h))).trans
    (S.norm_firstBeta_le beta d _ _)

theorem norm_blockBeta_le_one {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) (d r t c m h : I) :
    ‖S.blockBeta beta C.support d r t c m h‖ ≤ 1 := by
  by_cases hv : (t, c, m, h) ∈ S.blockSupport C.support r
  · rw [blockBeta, if_pos hv]
    have hm := S.blockSupport_original_mem C hv
    exact (S.norm_blockBetaCore_le beta d r t c m h).trans (hbeta _ hm.1 _ hm.2)
  · simp only [blockBeta, if_neg hv, norm_zero, zero_le_one]

def columnMass (a : I → ℂ) (marks : Finset I) (d : I) : ℝ :=
  ∑ p ∈ S.markQuotients marks d, ‖a (d * p)‖ ^ 2 / S.normI p

theorem columnMass_nonneg (a : I → ℂ) (marks : Finset I) (d : I) :
    0 ≤ S.columnMass a marks d := by
  exact Finset.sum_nonneg fun p hp => div_nonneg (sq_nonneg _) (S.norm_nonneg p)

theorem blockA_mass_le (hnorm : ∀ x, 1 ≤ S.normI x)
    (a : I → ℂ) (marks : Finset I) (d r t h : I) :
    (∑ p ∈ S.markQuotients marks d, ‖S.blockA a d r t h p‖ ^ 2) ≤
      S.columnMass a marks d := by
  have hu (p : I) : ‖S.cubic p r * S.mask p (h * t)‖ ≤ 1 :=
    (mul_contraction_norm _ _ (S.norm_mask_le_one p (h * t))).trans (S.norm_cubic_le_one p r)
  have h := twisted_column_mass_le (S.markQuotients marks d)
    (fun p => a (d * p)) (fun p => S.cubic p r * S.mask p (h * t)) S.normI
    (fun p hp => hu p) (fun p hp => lt_of_lt_of_le zero_lt_one (hnorm p))
  simpa only [blockA, columnMass, mul_assoc] using h

theorem blockBeta_budget {columns cubes : Finset I}
    (C : Completion columns cubes) (hnorm : ∀ x, 1 ≤ S.normI x)
    (beta : I → I → ℂ)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hcubes : ∀ b ∈ cubes, S.normI b ≤ B)
    (d r t c m h : I) :
    S.normI t * S.normI c * ‖S.blockBeta beta C.support d r t c m h‖ ^ 2 ≤
      (B / S.normI r) / (S.normI t * S.normI h) := by
  apply cube_support_weight_budget
    (S.normI t) (S.normI c) (S.normI h) (S.normI r) B
    (S.blockBeta beta C.support d r t c m h)
  · exact lt_of_lt_of_le zero_lt_one (hnorm t)
  · exact S.norm_nonneg c
  · exact lt_of_lt_of_le zero_lt_one (hnorm h)
  · exact lt_of_lt_of_le zero_lt_one (hnorm r)
  · exact hB
  · exact S.norm_blockBeta_le_one C beta hbeta d r t c m h
  · exact S.blockBeta_cube_support C beta B hcubes d r t c m h

def quotientTwice (d r k : I) : I := S.quotient r (S.quotient d k)

theorem quotientTwice_reconstruct (d r k : I)
    (hd : d ∈ S.divisors k) (hr : r ∈ S.divisors (S.quotient d k)) :
    (d * r) * S.quotientTwice d r k = k := by
  unfold quotientTwice
  rw [mul_assoc, S.quotient_spec r _ (S.divisor_dvd _ r hr),
    S.quotient_spec d _ (S.divisor_dvd _ d hd)]

theorem quotientTwice_injOn (rows : Finset I) (d r : I)
    (hdiv : ∀ k ∈ rows, d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k)) :
    Set.InjOn (S.quotientTwice d r) (rows : Set I) := by
  intro k hk l hl hkl
  have hk' := hdiv k hk
  have hl' := hdiv l hl
  rw [← S.quotientTwice_reconstruct d r k hk'.1 hk'.2,
    ← S.quotientTwice_reconstruct d r l hl'.1 hl'.2, hkl]

/-- The genuine block operator inputs follow from the supplied arithmetic
quadratic and cubic sieves. Both constants are chosen before the scales and
all finite sets, coefficients, divisors, and support reconstruction data. -/
theorem weightedBlock_admissible_from_sieves (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ Cq Cc : ℝ, 0 < Cq ∧ 0 < Cc ∧
    ∀ K Y N L : ℝ, 1 ≤ K → 1 ≤ Y → 1 ≤ N → 1 ≤ L →
    ∀ (rows marks columns cubes ts cs ms hs qset jset : Finset I)
      (C : Completion columns cubes)
      (goodPairs goodMC : Finset (I × I)) (a : I → ℂ) (beta : I → I → ℂ)
      (d r : I) (B Dq Dc : ℝ),
      0 ≤ B → 0 ≤ Dq → 0 ≤ Dc →
      (∀ k ∈ rows, d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k)) →
      (∀ k ∈ rows, sf (S.quotientTwice d r k) ∧ S.normI (S.quotientTwice d r k) ≤ K) →
      (∀ j ∈ qset, sf j ∧ S.normI j ≤ Y) →
      (∀ j ∈ jset, sf j ∧ S.normI j ≤ N) →
      (∀ p ∈ S.markQuotients marks d, sf p ∧ S.normI p ≤ L) →
      goodPairs ⊆ ms ×ˢ hs → goodMC ⊆ ms ×ˢ cs →
      (∀ u ∈ goodPairs, u.1 * u.2 ∈ qset) →
      (∀ j ∈ qset, ((goodPairs.filter fun u => u.1 * u.2 = j).card : ℝ) ≤ Dq) →
      (∀ u ∈ goodMC, u.2 * u.1 ∈ jset) →
      (∀ j ∈ jset, ((goodMC.filter fun u => u.2 * u.1 = j).card : ℝ) ≤ Dc) →
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      (S.weightedBlock a beta marks C.support ts cs ms hs goodPairs goodMC d r).Admissible
        rows (Cq * (K * Y) ^ eta * (K + Y) * Dq)
        (Cc * (N * L) ^ eta * (N + L + (N * L) ^ (2 / 3 : ℝ)) * Dc)
        (B / S.normI r) (S.columnMass a marks d) := by
  obtain ⟨Cq, hCq, hquadratic⟩ := quadratic_sieve_input_transpose S.normI sf S.symbol hq eta heta
  obtain ⟨Cc, hCc, hcubic⟩ := hc eta heta
  refine ⟨Cq, Cc, hCq, hCc, ?_⟩
  intro K Y N L hK hY hN hL rows marks columns cubes ts cs ms hs qset jset C
    goodPairs goodMC a beta d r B Dq Dc hB hDq hDc hdiv hrows hqset hjset hps
    hgp hgc hqmap hqfiber hcmap hcfiber hbeta hcubes
  let qrows := rows.image (S.quotientTwice d r)
  let Q := Cq * (K * Y) ^ eta * (K + Y)
  let V := Cc * (N * L) ^ eta * (N + L + (N * L) ^ (2 / 3 : ℝ))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hqrows : ∀ k ∈ qrows, sf k ∧ S.normI k ≤ K := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact hrows i hi
  refine {
    wt_pos := fun t ht => lt_of_lt_of_le zero_lt_one (hnorm t)
    wc_pos := fun c hc => lt_of_lt_of_le zero_lt_one (hnorm c)
    wh_pos := fun h hh => lt_of_lt_of_le zero_lt_one (hnorm h)
    mask := fun k hk t ht => S.norm_mask_le_one (S.quotient d k) t
    budget := fun t ht c hc m hm h hh => S.blockBeta_budget C hnorm beta hbeta B hB hcubes d r t c m h
    column_mass := fun t ht h hh => S.blockA_mass_le hnorm a marks d r t h
    quadratic := ?_
    cubic := ?_
  }
  · intro f
    have hsieve : ∀ z : I → ℂ,
        (∑ k ∈ qrows, ‖∑ j ∈ qset, S.quadratic k j * z j‖ ^ 2) ≤
          Q * ∑ j ∈ qset, ‖z j‖ ^ 2 := by
      intro z
      simpa only [quadratic, Q, mul_comm] using
        hquadratic K Y hK hY qrows qset hqrows hqset z
    have hrectangle := zero_extended_column_fiber_sieve qrows ms hs goodPairs qset
      (fun u => u.1 * u.2) S.quadratic Q Dq hQ hDq hgp hqmap hqfiber hsieve f
    have hpull := row_pullback_le rows qrows (S.quotientTwice d r)
      (fun k => ‖∑ m ∈ ms, ∑ h ∈ hs,
        zeroExtendedQuadratic goodPairs (fun u => u.1 * u.2) S.quadratic k m h * f m h‖ ^ 2)
      (S.quotientTwice_injOn rows d r hdiv)
      (fun k hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩) (fun _ _ => sq_nonneg _)
    exact hpull.trans hrectangle
  · intro f
    apply zero_extended_row_fiber_sieve ms cs goodMC jset (S.markQuotients marks d)
      (fun u => u.2 * u.1) S.cubic V Dc hDc hgc hcmap hcfiber (a := f)
    intro z
    exact hcubic N L hN hL jset (S.markQuotients marks d) hjset hps z (-2) (Or.inr rfl)

end Arithmetic

#print axioms Arithmetic.weightedBlock_admissible_from_sieves

end
end HeckeSkeleton.LowHybrid.NormalForm
