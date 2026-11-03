import ActualExteriorGcdMobiusSum

/-!
UNCOMPILED / native 0. A factorized expression may be valid only on the
coprime residual columns. It is extended to all residual columns before
Mobius insertion, but equality with the original expression is required
ONLY where the coprimality indicator is one. This prevents using a
coprime factorization theorem on the new noncoprime Mobius summands.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Arithmetic.IdealMobiusMask
open ActualPairDivisorDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "E" => ExteriorIdeal K S

/-- The supplied extension H need only agree on the actual coprime part
of each full residual family. The input is a pointwise algebraic identity,
not a Gram estimate, support bound, or equality on noncoprime columns. -/
theorem sum_pair_eq_gcd_mobius_of_coprime_extension
    (A B : Finset E) (F : E → E → ℂ) (H : E → E × E → ℂ)
    (hH : ∀ C ∈ finiteCommonParts K S A B,
      ∀ mn ∈ fullResidualPairs K S C A B,
        IsCoprime mn.1.val.val mn.2.val.val →
          H C mn = F (exteriorMul K S C mn.1) (exteriorMul K S C mn.2)) :
    (∑ I ∈ A, ∑ J ∈ B, F I J) =
      ∑ C ∈ finiteCommonParts K S A B,
        ∑ T ∈ (residualPrimeEnvelope K S C A B).powerset.attach,
          (moebius (primeProduct T.val) : ℂ) *
            ∑ mn ∈ mobiusResidualPairs K S C (residualMobiusDivisor K S C A B T) A B,
              H C (exteriorPairDilation K S (residualMobiusDivisor K S C A B T) mn) := by
  rw [sum_pair_eq_commonParts_fullResidual K S A B F]
  apply Finset.sum_congr rfl
  intro C hC
  calc
    _ = ∑ mn ∈ fullResidualPairs K S C A B,
        H C mn * (if IsCoprime mn.1.val.val mn.2.val.val then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro mn hmn
      by_cases hcop : IsCoprime mn.1.val.val mn.2.val.val
      · simp only [if_pos hcop, mul_one]
        exact (hH C hC mn hmn hcop).symm
      · simp only [if_neg hcop, mul_zero]
    _ = _ := finite_coprime_exterior_pair_sum_mobius_reindexed K S
      (fullResidualPairs K S C A B) (H C)

end HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
