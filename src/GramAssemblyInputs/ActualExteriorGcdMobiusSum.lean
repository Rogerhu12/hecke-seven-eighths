import ActualExteriorGcdFiberSum

/-!
One actual finite double sum is first partitioned by its gcd and then
expanded over common squarefree divisors of the FULL residual family.
Both original cutoffs stay on C*(D*M_i). No chosen generator or analytic
condition is added. UNCOMPILED SOURCE CANDIDATE / native 0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Arithmetic.ActualIdealPairMobiusDraft
open ActualPairDivisorDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "E" => ExteriorIdeal K S

def residualPrimeEnvelope (C : E) (A B : Finset E) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  finiteIdealPrimeEnvelope (fullResidualPairs K S C A B) (fun mn => mn.1.val)

def residualMobiusDivisor (C : E) (A B : Finset E)
    (T : {T : Finset (HeightOneSpectrum (𝓞 K)) //
      T ∈ (residualPrimeEnvelope K S C A B).powerset}) : E :=
  pairMobiusDivisor K S (fullResidualPairs K S C A B) T

/-- Exact two-stage preimage, without a residual coprimality restriction. -/
def mobiusResidualPairs (C D : E) (A B : Finset E) : Finset (E × E) :=
  divisorResidualPairs K S D (fullResidualPairs K S C A B)

@[simp] theorem mem_mobiusResidualPairs (C D : E) (A B : Finset E) (mn : E × E) :
    mn ∈ mobiusResidualPairs K S C D A B ↔
      exteriorMul K S C (exteriorMul K S D mn.1) ∈ A ∧
      exteriorMul K S C (exteriorMul K S D mn.2) ∈ B :=
  (mem_divisorResidualPairs K S D (fullResidualPairs K S C A B) mn).trans
    (mem_fullResidualPairs K S C A B (exteriorPairDilation K S D mn))

/-- Actual gcd regrouping followed by actual two-column Mobius insertion
and simultaneous divisor removal on the enlarged residual family. -/
theorem sum_pair_eq_gcd_mobius_residual (A B : Finset E) (F : E → E → ℂ) :
    (∑ I ∈ A, ∑ J ∈ B, F I J) =
      ∑ C ∈ finiteCommonParts K S A B,
        ∑ T ∈ (residualPrimeEnvelope K S C A B).powerset.attach,
          (moebius (primeProduct T.val) : ℂ) *
            ∑ mn ∈ mobiusResidualPairs K S C (residualMobiusDivisor K S C A B T) A B,
              F (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.1))
                (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.2)) := by
  rw [sum_pair_eq_commonParts_fullResidual K S A B F]
  apply Finset.sum_congr rfl
  intro C _
  exact finite_coprime_exterior_pair_sum_mobius_reindexed K S
    (fullResidualPairs K S C A B)
    (fun mn => F (exteriorMul K S C mn.1) (exteriorMul K S C mn.2))

end HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
