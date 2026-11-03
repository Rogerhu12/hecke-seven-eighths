import HeckeSkeleton.LowHybrid.NormalFormFinite

/-!
# The original hybrid row equals the double-divisor normal form

This file performs both entire Mobius expansions, both quotient reindexings,
the completed-square decomposition, and the zero-preserving cubic mask
simplification. All coefficients are defined explicitly. Their signatures
exclude the moving row and (for beta) the moving mark.
-/

namespace HeckeSkeleton.LowHybrid.NormalForm

open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [CommMonoid I]

private theorem rotate_three_sums {A B C : Type*}
    (as : Finset A) (bs : Finset B) (cs : Finset C) (F : A → B → C → ℂ) :
    (∑ a ∈ as, ∑ b ∈ bs, ∑ c ∈ cs, F a b c) =
      ∑ b ∈ bs, ∑ c ∈ cs, ∑ a ∈ as, F a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  exact Finset.sum_comm

namespace Arithmetic

variable (S : Arithmetic I)

def firstBeta (beta : I → I → ℂ) (d n b : I) : ℂ :=
  beta n b * S.quadratic d (n * b) * S.cubic d n * S.mask d b

def firstColumn (a : I → ℂ) (marks : Finset I) (d n b : I) : ℂ :=
  ∑ p ∈ S.markQuotients marks d,
    (a (d * p) / (Real.sqrt (S.normI p) : ℂ)) * S.cubic p n * S.mask p b

def firstRow (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (d k : I) : ℂ :=
  ∑ n ∈ columns, ∑ b ∈ cubes,
    S.firstBeta beta d n b * S.quadratic k (n * b) * S.firstColumn a marks d n b

theorem first_divisor_summand (a : I → ℂ) (beta : I → I → ℂ)
    (d k p n b : I) :
    (a (d * p) / (Real.sqrt (S.normI (d * p)) : ℂ)) *
      (beta n b * (S.quadratic (d * k) (n * b) *
        S.cubic (d * p) n * S.mask (d * p) b)) =
    S.weight d * (S.firstBeta beta d n b * S.quadratic k (n * b) *
      ((a (d * p) / (Real.sqrt (S.normI p) : ℂ)) * S.cubic p n * S.mask p b)) := by
  rw [S.normalization_mul, S.quadratic_mul_left, S.cubic_mul_left, S.mask_mul_left]
  unfold firstBeta
  ring

theorem first_divisor_column_sum (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (d k : I) :
    (∑ p ∈ S.markQuotients marks d,
      (a (d * p) / (Real.sqrt (S.normI (d * p)) : ℂ)) *
        ∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
          (S.quadratic (d * k) (n * b) * S.cubic (d * p) n * S.mask (d * p) b)) =
      S.weight d * S.firstRow a beta marks columns cubes d k := by
  simp_rw [Finset.mul_sum]
  rw [rotate_three_sums]
  unfold firstRow firstColumn
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro p hp
  exact S.first_divisor_summand a beta d k p n b

/-- First full moving-mask expansion and mark/row quotient extraction. -/
theorem hybridRow_first_expansion (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (k : I) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ d ∈ S.divisors k, S.mu d *
        (S.weight d * S.firstRow a beta marks columns cubes d (S.quotient d k)) := by
  let F : I → ℂ := fun p => (a p / (Real.sqrt (S.normI p) : ℂ)) *
    ∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
      (S.quadratic k (n * b) * S.cubic p n * S.mask p b)
  calc
    _ = ∑ p ∈ marks, S.mask p k * F p := by
      unfold hybridRow F quadratic cubic mask
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ d ∈ S.divisors k, S.mu d * ∑ p ∈ marks with d ∣ p, F p :=
      S.mask_sum_expansion marks k F
    _ = ∑ d ∈ S.divisors k, S.mu d *
        ∑ p ∈ S.markQuotients marks d, F (d * p) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [S.sum_divisor_reindex]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      have hk : d * S.quotient d k = k :=
        S.quotient_spec d k (S.divisor_dvd k d hd)
      dsimp only [F]
      conv_lhs => rw [← hk]
      exact S.first_divisor_column_sum a beta marks columns cubes d (S.quotient d k)

/-- The moving-row-free coefficient after both divisor extractions. -/
def blockBetaCore (beta : I → I → ℂ) (d r t c m h : I) : ℂ :=
  S.firstBeta beta d (r * c * m) (r * c * h * t ^ 2) * S.quadratic r (m * h)

/-- The common cubic column coefficient. Its type excludes both the moving
row and the joint cubic row `(c,m)`. -/
def blockA (a : I → ℂ) (d r t h p : I) : ℂ :=
  (a (d * p) / (Real.sqrt (S.normI p) : ℂ)) * S.cubic p r * S.mask p (h * t)

def blockColumn (a : I → ℂ) (marks : Finset I) (d r t c m h : I) : ℂ :=
  ∑ p ∈ S.markQuotients marks d, S.blockA a d r t h p * S.cubic p (c * m)

theorem firstColumn_completed (a : I → ℂ) (marks : Finset I) (d r t c m h : I) :
    S.firstColumn a marks d (r * c * m) (r * c * h * t ^ 2) =
      S.blockColumn a marks d r t c m h := by
  unfold firstColumn blockColumn blockA
  apply Finset.sum_congr rfl
  intro p hp
  calc
    _ = (a (d * p) / (Real.sqrt (S.normI p) : ℂ)) *
        (S.cubic p (r * c * m) * S.mask p (r * c * h * t ^ 2)) := by ring
    _ = _ := by rw [S.completed_cubic]; ring

def blockRowSupport (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I)) (d r k : I) : ℂ :=
  ∑ v ∈ S.blockSupport support r,
    S.mask k v.1 * S.quadratic (S.quotient r k) (v.2.2.1 * v.2.2.2) *
      (S.blockBetaCore beta d r v.1 v.2.1 v.2.2.1 v.2.2.2 *
        S.blockColumn a marks d r v.1 v.2.1 v.2.2.1 v.2.2.2)

theorem firstRow_completed (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (d k : I) :
    S.firstRow a beta marks columns cubes d k =
      ∑ v ∈ C.support, S.mask k v.2.1 *
        (S.mask k v.1 * S.quadratic k (v.2.2.1 * v.2.2.2) *
          (S.firstBeta beta d (recombine v).1 (recombine v).2 *
            S.firstColumn a marks d (recombine v).1 (recombine v).2)) := by
  unfold firstRow
  rw [C.sum_reindex]
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with ⟨t, c, m, h⟩
  simp only [recombine]
  rw [S.completed_quadratic]
  ring

/-- Second full moving-mask expansion and common-factor quotient extraction. -/
theorem firstRow_second_expansion (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (d k : I) :
    S.firstRow a beta marks columns cubes d k =
      ∑ r ∈ S.divisors k, S.mu r * S.blockRowSupport a beta marks C.support d r k := by
  rw [S.firstRow_completed a beta marks columns cubes C]
  rw [S.mask_common_expansion]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  rw [S.sum_common_reindex]
  unfold blockRowSupport
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with ⟨t, c, m, h⟩
  simp only [restoreCommon, recombine]
  have hq : S.quadratic k (m * h) =
      S.quadratic r (m * h) * S.quadratic (S.quotient r k) (m * h) := by
    conv_lhs => rw [← S.quotient_spec r k (S.divisor_dvd k r hr)]
    rw [S.quadratic_mul_left]
  rw [hq, S.firstColumn_completed]
  unfold blockBetaCore
  ring

/-- Exact normal form of the original normalized hybrid row. Both complete
Mobius expansions and all original support and collision conditions remain
present. The only decomposition data are the explicit finite reconstruction
map in `Completion`; the row equality is the conclusion, not an input. -/
theorem hybridRow_normal_form (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (k : I) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ d ∈ S.divisors k, ∑ r ∈ S.divisors (S.quotient d k),
        (S.mu d * S.mu r) * (S.weight d *
          S.blockRowSupport a beta marks C.support d r (S.quotient d k)) := by
  rw [S.hybridRow_first_expansion a beta marks columns cubes]
  apply Finset.sum_congr rfl
  intro d hd
  rw [S.firstRow_second_expansion a beta marks columns cubes C]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Joint-support zero extension; this coefficient still has no row or mark
argument. It is the beta used by the rectangular weighted sieve. -/
def blockBeta (beta : I → I → ℂ) (support : Finset (CompletedIndex I))
    (d r t c m h : I) : ℂ :=
  if (t, c, m, h) ∈ S.blockSupport support r then S.blockBetaCore beta d r t c m h else 0

def blockRowBox (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (d r k : I) : ℂ :=
  ∑ t ∈ ts, ∑ c ∈ cs, S.mask k t *
    ∑ m ∈ ms, ∑ h ∈ hs, S.quadratic (S.quotient r k) (m * h) *
      (S.blockBeta beta support d r t c m h * S.blockColumn a marks d r t c m h)

theorem blockRowSupport_eq_box (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (d r k : I)
    (hbox : S.blockSupport support r ⊆ completedBox ts cs ms hs) :
    S.blockRowSupport a beta marks support d r k =
      S.blockRowBox a beta marks support ts cs ms hs d r k := by
  unfold blockRowSupport
  rw [sum_zero_extend_box _ ts cs ms hs hbox]
  unfold blockRowBox
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hv : (t, c, m, h) ∈ S.blockSupport support r
  · simp only [blockBeta, if_pos hv]
    ring
  · simp only [blockBeta, if_neg hv, zero_mul, mul_zero]

end Arithmetic

#print axioms Arithmetic.hybridRow_normal_form
#print axioms Arithmetic.blockRowSupport_eq_box

end
end HeckeSkeleton.LowHybrid.NormalForm
