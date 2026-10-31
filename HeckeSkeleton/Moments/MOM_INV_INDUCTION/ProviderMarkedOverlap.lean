import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionOverlap

/-!
# The actual first overlap change of squarefree column

For a fixed selected common prime product `j` and remaining prime product
`P`, the source condition is `gcd n (j * P) = j`.  The new column is
`(n / j) * P`.  Its exact image consists of squarefree columns divisible
by `P` and coprime to `j`; the inverse is `j * (c / P)`.

This is an arithmetic equivalence, before any Cauchy inequality or source
energy estimate.  The coefficient and puncture identities use the actual
zero-extended character.  All ramification zeros are therefore retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOverlap

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem idealQuotient_self_mul {D : Ideal (𝓞 K)} (hD : D ≠ ⊥)
    (I : Ideal (𝓞 K)) : idealQuotient D (D * I) = I := by
  apply mul_left_cancel₀ hD
  exact idealQuotient_mul (dvd_mul_right D I)

theorem ideal_coprime_of_relPrime {I J : Ideal (𝓞 K)} (h : IsRelPrime I J) :
    IsCoprime I J := by
  apply Ideal.isCoprime_iff_gcd.mpr
  exact associated_iff_eq.mp
    (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr h))

/-- Source columns in the fixed, actual gcd fiber. -/
def Source (j P : Ideal (𝓞 K)) :=
  {n : Ideal (𝓞 K) // Squarefree n ∧ gcd n (j * P) = j}

/-- The new column includes every remaining selected prime, while the
extracted primes become an additional puncture. -/
def Target (j P : Ideal (𝓞 K)) :=
  {c : Ideal (𝓞 K) // Squarefree c ∧ P ∣ c ∧ IsCoprime c j}

def forward (j P n : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  idealQuotient j n * P

def backward (j P c : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  j * idealQuotient P c

theorem source_common_dvd (j P : Ideal (𝓞 K)) (n : Source j P) : j ∣ n.val := by
  rw [← n.property.2]
  exact gcd_dvd_left _ _

theorem forward_mem (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P))
    (n : Source j P) :
    Squarefree (forward j P n.val) ∧ P ∣ forward j P n.val ∧
      IsCoprime (forward j P n.val) j := by
  obtain ⟨hjPc, hj, hP⟩ := squarefree_mul_iff.mp hjP
  have hn : n.val = j * idealQuotient j n.val :=
    (idealQuotient_mul (source_common_dvd j P n)).symm
  obtain ⟨hjn, _, hnq⟩ := squarefree_mul_iff.mp (hn ▸ n.property.1)
  have hq : IsCoprime (idealQuotient j n.val) P := by
    have hc := (gcd_eq_iff_quotient_coprime j n.val (j * P) hj.ne_zero
      (source_common_dvd j P n) (dvd_mul_right _ _)).mp n.property.2
    simpa only [idealQuotient_self_mul hj.ne_zero] using hc
  refine ⟨squarefree_mul_iff.mpr ⟨hq.isRelPrime, hnq, hP⟩,
    dvd_mul_left _ _, ?_⟩
  exact (ideal_coprime_of_relPrime hjn).symm.mul_left
    (ideal_coprime_of_relPrime hjPc).symm

theorem backward_mem (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P))
    (c : Target j P) :
    Squarefree (backward j P c.val) ∧ gcd (backward j P c.val) (j * P) = j := by
  obtain ⟨_, hj, hP⟩ := squarefree_mul_iff.mp hjP
  have hc : c.val = P * idealQuotient P c.val :=
    (idealQuotient_mul c.property.2.1).symm
  obtain ⟨hPq, _, hq⟩ := squarefree_mul_iff.mp (hc ▸ c.property.1)
  have hjq : IsCoprime j (idealQuotient P c.val) := by
    have h := c.property.2.2
    rw [hc, IsCoprime.mul_left_iff] at h
    exact h.2.symm
  refine ⟨squarefree_mul_iff.mpr ⟨hjq.isRelPrime, hj, hq⟩, ?_⟩
  apply (gcd_eq_iff_quotient_coprime j _ _ hj.ne_zero
    (dvd_mul_right _ _) (dvd_mul_right _ _)).mpr
  simpa only [backward, idealQuotient_self_mul hj.ne_zero] using
    (ideal_coprime_of_relPrime hPq).symm

theorem backward_forward (j P : Ideal (𝓞 K)) (hP : P ≠ ⊥)
    (n : Source j P) : backward j P (forward j P n.val) = n.val := by
  rw [backward, forward, mul_comm (idealQuotient j n.val) P,
    idealQuotient_self_mul hP]
  exact idealQuotient_mul (source_common_dvd j P n)

theorem forward_backward (j P : Ideal (𝓞 K)) (hj : j ≠ ⊥)
    (c : Target j P) : forward j P (backward j P c.val) = c.val := by
  rw [forward, backward, idealQuotient_self_mul hj,
    mul_comm (idealQuotient P c.val) P]
  exact idealQuotient_mul c.property.2.1

/-- A genuine equivalence of the two arithmetic source classes. -/
def columnEquiv (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P)) :
    Source j P ≃ Target j P where
  toFun n := ⟨forward j P n.val, forward_mem j P hjP n⟩
  invFun c := ⟨backward j P c.val, backward_mem j P hjP c⟩
  left_inv n := Subtype.ext (backward_forward j P
    (squarefree_mul_iff.mp hjP).2.2.ne_zero n)
  right_inv c := Subtype.ext (forward_backward j P
    (squarefree_mul_iff.mp hjP).2.1.ne_zero c)

/-- Exact finite reindexing of the original gcd fiber, with no loss
and with the actual finite source carried through the equivalence. -/
theorem sum_source_eq_target (j P : Ideal (𝓞 K))
    (hjP : Squarefree (j * P)) (N : Finset (Source j P))
    (f : Source j P → ℂ) :
    ∑ n ∈ N, f n =
      ∑ c ∈ N.map (columnEquiv j P hjP).toEmbedding,
        f ((columnEquiv j P hjP).symm c) := by
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

/-- The fixed-fiber norm identity is the exact new column scale. -/
theorem forward_norm (j P : Ideal (𝓞 K)) (n : Source j P) :
    (j.absNorm : ℝ) * ((forward j P n.val).absNorm : ℝ) =
      (n.val.absNorm : ℝ) * (P.absNorm : ℝ) := by
  have hn := congrArg (fun I : Ideal (𝓞 K) => (I.absNorm : ℝ))
    (idealQuotient_mul (source_common_dvd j P n))
  simp only [map_mul, Nat.cast_mul] at hn ⊢
  dsimp only [forward]
  simp only [map_mul, Nat.cast_mul]
  rw [← mul_assoc, hn]

/-- The original Mobius sign becomes exactly the residual Mobius
coefficient, a fixed extracted sign, and one sign per residual prime. -/
theorem coefficient_identity (j P : Ideal (𝓞 K)) (hjP : Squarefree (j * P))
    (n : Source j P) (χ : HeckeCharacter K) :
    (moebius n.val : ℂ) * idealCoefficient (primeCoefficient K χ) n.val *
        idealCoefficient (primeCoefficient K χ) (j * P) =
      (moebius j : ℂ) * (moebius P : ℂ) *
        (moebius (forward j P n.val) : ℂ) *
        idealCoefficient (primeCoefficient K χ) j ^ 2 *
        idealCoefficient (primeCoefficient K χ) (forward j P n.val) := by
  have hn : n.val = j * idealQuotient j n.val :=
    (idealQuotient_mul (source_common_dvd j P n)).symm
  obtain ⟨hjn, _, _⟩ := squarefree_mul_iff.mp (hn ▸ n.property.1)
  have hq : IsCoprime (idealQuotient j n.val) P := by
    have hc := (gcd_eq_iff_quotient_coprime j n.val (j * P)
      (squarefree_mul_iff.mp hjP).2.1.ne_zero (source_common_dvd j P n)
      (dvd_mul_right _ _)).mp n.property.2
    simpa only [idealQuotient_self_mul (squarefree_mul_iff.mp hjP).2.1.ne_zero]
      using hc
  have h := moebius_character_overlap
    (idealCoefficientHom (primeCoefficient K χ)).toMonoidHom hjn hq.isRelPrime
      (squarefree_mul_iff.mp hjP).2.2
  rw [← hn] at h
  exact h

/-- The extracted character square is a contraction also at its zeros. -/
theorem extracted_character_norm_le (j : Ideal (𝓞 K)) (χ : HeckeCharacter K) :
    ‖idealCoefficient (primeCoefficient K χ) j ^ 2‖ ≤ 1 :=
  overlap_scalar_norm_le
    (norm_idealCoefficient_le_one _ (norm_primeCoefficient_le_one K χ) _)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOverlap
