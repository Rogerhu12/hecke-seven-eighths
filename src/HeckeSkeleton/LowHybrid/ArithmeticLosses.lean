import HeckeSkeleton.LowHybrid.PrimeDivisorBounds
import HeckeSkeleton.LowHybrid.CountingBridge
import HeckeSkeleton.LowHybrid.NaturalLosses

/-!
# The actual divisor and harmonic losses from linear ideal counting

A linear count for all finite norm-bounded subsets implies that every norm
cutoff is finite. Thus no independent finite-cutoff or divisor-asymptotic
assumption is needed. The actual maximum squarefree divisor count and the
logarithmic harmonic envelope both have uniform small-power bounds.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical

noncomputable section

/-- A bound on every finite subset forces the entire natural-norm cutoff
to be finite. Otherwise an arbitrarily large finite subset contradicts it. -/
theorem finite_nat_norms_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C)
    (N : ℕ) : Set.Finite {i : I | q i ≤ N} := by
  by_contra hnot
  have hinf : Set.Infinite {i : I | q i ≤ N} := hnot
  obtain ⟨m, hm⟩ := exists_nat_gt (C * (N : ℝ))
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq m
  have hb := hcount N s (fun i hi => hs hi)
  rw [hcard] at hb
  exact (not_le_of_gt hm) hb

/-- Naturality of the real norm transfers finite natural-norm cutoffs to
every real cutoff, including scales below one. -/
theorem finite_real_norms_of_linear_counting
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ)
    (hcount : LinearNormCounting q C) (X : ℝ) :
    Set.Finite {i : I | normI i ≤ X} := by
  apply (finite_nat_norms_of_linear_counting q C hcount (Nat.floor X)).subset
  intro i hi
  apply Nat.le_floor
  change normI i ≤ X at hi
  simpa only [hnorm] using hi

/-- A positive natural norm is at least one as a real norm. -/
theorem one_le_real_norm_of_natural
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (hq : ∀ i, 1 ≤ q i) :
    ∀ i, 1 ≤ normI i := by
  intro i
  rw [hnorm i]
  exact_mod_cast hq i

/-- The common harmonic envelope, controlling every actual bounded finite
support by the linear-counting theorem. -/
def harmonicEnvelope (C X : ℝ) : ℝ := C * (1 + Real.log X)

theorem harmonicEnvelope_nonneg (C : ℝ) (hC : 0 ≤ C) (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ harmonicEnvelope C X := by
  unfold harmonicEnvelope
  exact mul_nonneg hC (add_nonneg zero_le_one (Real.log_nonneg hX))

theorem harmonicEnvelope_subpower (C : ℝ) (hC : 0 < C) :
    SubpowerBound (harmonicEnvelope C) := by
  apply subpower_of_logarithmic_bound (harmonicEnvelope C) C hC
  intro X hX
  exact le_rfl

theorem reciprocal_sum_le_harmonicEnvelope
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 1 ≤ X) (s : Finset I)
    (hs : ∀ i ∈ s, normI i ≤ X) :
    (∑ i ∈ s, 1 / normI i) ≤ harmonicEnvelope C X := by
  have hs' : ∀ i ∈ s, (q i : ℝ) ≤ X := by
    intro i hi
    simpa only [hnorm] using hs i hi
  simpa only [hnorm, harmonicEnvelope] using
    reciprocal_sum_le_log_of_linear_counting q C hC hq hcount X hX s hs'

section PrimeCoordinates

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))
variable (normI : A →* ℝ) (q : A → ℕ)
variable (hnorm : ∀ a, normI a = (q a : ℝ)) (Ccount : ℝ)
variable (hcount : LinearNormCounting q Ccount)

/-- The actual Delta envelope, with finite cutoffs derived solely from the
linear norm count. -/
def divisorEnvelopeOfCounting : ℝ → ℝ :=
  PrimeArithmetic.actualDivisorEnvelope coords normI
    (finite_real_norms_of_linear_counting q normI hnorm Ccount hcount)

theorem divisorEnvelopeOfCounting_nonneg (X : ℝ) :
    0 ≤ divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount X :=
  PrimeArithmetic.actualDivisorEnvelope_nonneg coords normI _ X

theorem divisor_count_le_envelopeOfCounting (X : ℝ) (a : A) (ha : normI a ≤ X) :
    ((PrimeArithmetic.divisors coords a).card : ℝ) ≤
      divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount X :=
  PrimeArithmetic.divisor_count_le_actual_envelope coords normI _ X a ha

theorem divisorEnvelopeOfCounting_subpower (hq : ∀ a : A, 1 ≤ q a) :
    SubpowerBound (divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount) := by
  exact PrimeArithmetic.actualDivisorEnvelope_subpower coords normI
    (one_le_real_norm_of_natural q normI hnorm hq)
    (finite_real_norms_of_linear_counting q normI hnorm Ccount hcount)

/-- All twelve arithmetic losses are absorbed by the prescribed epsilon.
Only prime coordinates, a multiplicative positive natural norm, and linear
norm counting enter this arithmetic theorem. The auxiliary exponent and
constant are selected before K, N, B, and L. -/
theorem natural_arithmetic_loss_subpower_of_counting
    (hCcount : 0 < Ccount) (hq : ∀ a : A, 1 ≤ q a)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        naturalHybridArithmeticLoss
          (divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount)
          (harmonicEnvelope Ccount) eta K N B L ≤ C * (K * N * B * L) ^ eps := by
  exact natural_hybrid_arithmetic_loss_subpower
    (divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount)
    (harmonicEnvelope Ccount)
    (fun X _ => divisorEnvelopeOfCounting_nonneg coords normI q hnorm Ccount hcount X)
    (harmonicEnvelope_nonneg Ccount (le_of_lt hCcount))
    (divisorEnvelopeOfCounting_subpower coords normI q hnorm Ccount hcount hq)
    (harmonicEnvelope_subpower Ccount hCcount) eps heps

end PrimeCoordinates

#print axioms finite_nat_norms_of_linear_counting
#print axioms finite_real_norms_of_linear_counting
#print axioms reciprocal_sum_le_harmonicEnvelope
#print axioms divisorEnvelopeOfCounting_subpower
#print axioms natural_arithmetic_loss_subpower_of_counting

end
end HeckeSkeleton.LowHybrid
