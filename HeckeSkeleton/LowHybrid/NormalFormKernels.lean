import HeckeSkeleton.LowHybrid.NormalForm
import HeckeSkeleton.LowHybrid.WeightedSieveBounds
import HeckeSkeleton.LowHybrid.Global

/-!
# Exact squarefree zero extensions and the actual weighted block

The arithmetic block is constructed from the original coefficients and the
two explicit quotient maps. Neither coefficient has a moving-row argument.
The row equality below is established before invoking any sieve bound.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

namespace Arithmetic

variable (S : Arithmetic I)

def blockRowZero (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r k : I) : ℂ :=
  ∑ t ∈ ts, ∑ c ∈ cs, S.mask k t *
    ∑ m ∈ ms, ∑ h ∈ hs,
      zeroExtendedQuadratic goodPairs (fun u => u.1 * u.2) S.quadratic
        (S.quotient r k) m h *
      (S.blockBeta beta support d r t c m h *
        ∑ p ∈ S.markQuotients marks d, S.blockA a d r t h p *
          zeroExtendedCubic goodMC (fun u => u.2 * u.1) S.cubic m c p)

theorem blockRowBox_eq_zero (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r k : I)
    (hq : ∀ v ∈ S.blockSupport support r, (v.2.2.1, v.2.2.2) ∈ goodPairs)
    (hc : ∀ v ∈ S.blockSupport support r, (v.2.2.1, v.2.1) ∈ goodMC) :
    S.blockRowBox a beta marks support ts cs ms hs d r k =
      S.blockRowZero a beta marks support ts cs ms hs goodPairs goodMC d r k := by
  unfold blockRowBox blockRowZero
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro c hc'
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hv : (t, c, m, h) ∈ S.blockSupport support r
  · have hq' := hq (t, c, m, h) hv
    have hc' := hc (t, c, m, h) hv
    simp only [zeroExtendedQuadratic, zeroExtendedCubic, if_pos hq', if_pos hc',
      blockColumn]
  · simp only [blockBeta, if_neg hv, zero_mul, mul_zero]

/-- The concrete block used by the global weighted-energy theorem. -/
def weightedBlock (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r : I) :
    WeightedBlock I where
  T := I
  C := I
  M := I
  H := I
  P := I
  ts := ts
  cs := cs
  ms := ms
  hs := hs
  ps := S.markQuotients marks d
  q := fun k m h =>
    zeroExtendedQuadratic goodPairs (fun u => u.1 * u.2) S.quadratic
      (S.quotient r (S.quotient d k)) m h
  chi := zeroExtendedCubic goodMC (fun u => u.2 * u.1) S.cubic
  a := S.blockA a d r
  beta := S.blockBeta beta support d r
  rowMask := fun k t => S.mask (S.quotient d k) t
  wt := S.normI
  wc := S.normI
  wh := S.normI

theorem weightedBlock_row (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r k : I) :
    (S.weightedBlock a beta marks support ts cs ms hs goodPairs goodMC d r).row k =
      S.blockRowZero a beta marks support ts cs ms hs goodPairs goodMC
        d r (S.quotient d k) := rfl

def divisorPairs (k : I) : Finset (I × I) :=
  (S.divisors k).biUnion fun d =>
    (S.divisors (S.quotient d k)).image fun r => (d, r)

theorem mem_divisorPairs (k d r : I) :
    (d, r) ∈ S.divisorPairs k ↔
      d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k) := by
  simp only [divisorPairs, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨d', hd', r', hr', h1, h2⟩
    subst d'
    subst r'
    exact ⟨hd', hr'⟩
  · rintro ⟨hd, hr⟩
    exact ⟨d, hd, r, hr, rfl, rfl⟩

theorem divisorPairs_disjoint (k : I) :
    Set.PairwiseDisjoint (↑(S.divisors k))
      (fun d => (S.divisors (S.quotient d k)).image fun r => (d, r)) := by
  intro d hd e he hde
  apply Finset.disjoint_left.mpr
  intro v hvd hve
  obtain ⟨r, hr, hrv⟩ := Finset.mem_image.mp hvd
  obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hve
  apply hde
  exact congrArg Prod.fst (hrv.trans hsv.symm)

theorem sum_divisorPairs (k : I) (F : I × I → ℂ) :
    (∑ dr ∈ S.divisorPairs k, F dr) =
      ∑ d ∈ S.divisors k, ∑ r ∈ S.divisors (S.quotient d k), F (d, r) := by
  unfold divisorPairs
  rw [Finset.sum_biUnion (S.divisorPairs_disjoint k)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_image]
  intro r hr s hs h
  exact (Prod.mk.inj h).2

theorem card_divisorPairs (k : I) :
    (S.divisorPairs k).card =
      ∑ d ∈ S.divisors k, (S.divisors (S.quotient d k)).card := by
  unfold divisorPairs
  rw [Finset.card_biUnion (S.divisorPairs_disjoint k)]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)

/-- The literal original row equals the precise weighted-block sum consumed
by `hybrid_energy_of_weighted_blocks`. No row equality or block energy bound
is assumed. The hypotheses concern only finite support and reconstruction. -/
theorem hybridRow_eq_weightedBlocks (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes)
    (ts cs ms hs : I → I → Finset I)
    (goodPairs goodMC : I → I → Finset (I × I)) (k : I)
    (hbox : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      S.blockSupport C.support r ⊆ completedBox (ts d r) (cs d r) (ms d r) (hs d r))
    (hq : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      ∀ v ∈ S.blockSupport C.support r, (v.2.2.1, v.2.2.2) ∈ goodPairs d r)
    (hc : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      ∀ v ∈ S.blockSupport C.support r, (v.2.2.1, v.2.1) ∈ goodMC d r) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ dr ∈ S.divisorPairs k, (S.mu dr.1 * S.mu dr.2) *
        (((1 : ℂ) / (Real.sqrt (S.normI dr.1) : ℂ)) *
          (S.weightedBlock a beta marks C.support
            (ts dr.1 dr.2) (cs dr.1 dr.2) (ms dr.1 dr.2) (hs dr.1 dr.2)
            (goodPairs dr.1 dr.2) (goodMC dr.1 dr.2) dr.1 dr.2).row k) := by
  rw [S.sum_divisorPairs, S.hybridRow_normal_form a beta marks columns cubes C]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro r hr
  rw [S.blockRowSupport_eq_box a beta marks C.support
    (ts d r) (cs d r) (ms d r) (hs d r) d r (S.quotient d k) (hbox d hd r hr)]
  rw [S.blockRowBox_eq_zero a beta marks C.support
    (ts d r) (cs d r) (ms d r) (hs d r) (goodPairs d r) (goodMC d r)
    d r (S.quotient d k) (hq d hd r hr) (hc d hd r hr)]
  simp only [weightedBlock_row, weight, one_div]

end Arithmetic

#print axioms Arithmetic.hybridRow_eq_weightedBlocks

end
end HeckeSkeleton.LowHybrid.NormalForm
