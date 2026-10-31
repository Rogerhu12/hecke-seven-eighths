import ActualThetaOriginalFullFactorization
import ActualCoprimeFactorizationExtension

/-!
UNCOMPILED / native 0. An actual extension of the raw/R/residual formula
to every residual ideal pair. It agrees with the original full correlation
on coprime pairs, which is the exact obligation before Mobius insertion.
No equality on noncoprime pairs is claimed or used. The actual quotient
generators retain their unit discrepancies and all frequencies include zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Global.ActualPairDivisorDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "E" => ExteriorIdeal K S
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "χ" => sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
  (probeArithmetic_six_support K S D)

/-- The literal factorized expression is defined even for noncoprime
residual columns, without supplying Bezout data or a coprimality proof. -/
def thetaResidualCorrelationExpression (C N₁ N₂ : E) (k : OS) : ℂ :=
  let n₁ : NZ := thetaGeneratorDivision K S D C N₁ (exteriorMul K S C N₁) rfl
  let n₂ : NZ := thetaGeneratorDivision K S D C N₂ (exteriorMul K S C N₂) rfl
  (χ k n₁ * conj (χ (-k) n₂)) *
    sIntegerSexticRCorrection K S D.root6 D.primitive6 D.embedding n₁ n₂ *
    sIntegerSexticFiniteCorrelation K S D.root6 D.primitive6 D.embedding
      C.val.val (nonZeroDivisors.coe_ne_zero C.val) C.property
      (fun p hp => D.away_six p (C.property p hp))
      (Ideal.Quotient.mk _ n₁.val) (Ideal.Quotient.mk _ n₂.val) (Ideal.Quotient.mk _ k)

/-- Frequency support is tested against the actual common generator.
The ring quotient is selected only from a genuine divisibility witness. -/
def thetaCoprimeCorrelationExtension (C : E) (mn : E × E) (j : OS) : ℂ :=
  if h : D.generator C ∣ j then
    thetaResidualCorrelationExpression K S D C mn.1 mn.2 (Classical.choose h)
  else 0

theorem thetaCoprimeCorrelationExtension_eq_of_isCoprime
    (C N₁ N₂ : E) (j : OS) (hcop : IsCoprime N₁.val.val N₂.val.val) :
    thetaCoprimeCorrelationExtension K S D C (N₁, N₂) j =
      sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D)
        (probeGenerator K S D (exteriorMul K S C N₁))
        (probeGenerator K S D (exteriorMul K S C N₂)) j := by
  by_cases hd : D.generator C ∣ j
  · rw [thetaCoprimeCorrelationExtension, dif_pos hd]
    have hf := thetaOriginalFullCorrelation_factorization K S D C N₁ N₂
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl hcop (Classical.choose hd)
    exact hf.symm.trans (congrArg
      (fun a => sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D)
        (probeGenerator K S D (exteriorMul K S C N₁))
        (probeGenerator K S D (exteriorMul K S C N₂)) a)
      (Classical.choose_spec hd).symm)
  · rw [thetaCoprimeCorrelationExtension, dif_neg hd]
    exact (thetaOriginalFullCorrelation_eq_zero_of_not_dvd K S D C N₁ N₂
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl j hd).symm

/-- Actual full correlations may now be replaced by the defined extension
before the exact gcd/Mobius expansion. Every enlarged residual family uses
that same extension; its noncoprime values are never equated to the original. -/
theorem sum_weighted_originalFullCorrelation_eq_gcd_mobius_extension
    (A B : Finset E) (b : E → E → ℂ) (j : OS) :
    (∑ I ∈ A, ∑ J ∈ B,
      b I J * sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D I)
        (probeGenerator K S D J) j) =
      ∑ C ∈ finiteCommonParts K S A B,
        ∑ T ∈ (residualPrimeEnvelope K S C A B).powerset.attach,
          (moebius (primeProduct T.val) : ℂ) *
            ∑ mn ∈ mobiusResidualPairs K S C (residualMobiusDivisor K S C A B T) A B,
              b (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.1))
                (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.2)) *
              thetaCoprimeCorrelationExtension K S D C
                (exteriorPairDilation K S (residualMobiusDivisor K S C A B T) mn) j := by
  apply sum_pair_eq_gcd_mobius_of_coprime_extension K S A B
    (fun I J => b I J * sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D) (probeGenerator K S D I)
      (probeGenerator K S D J) j)
    (fun C mn => b (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) *
      thetaCoprimeCorrelationExtension K S D C mn j)
  intro C _ mn _ hcop
  exact congrArg (b (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) * ·)
    (thetaCoprimeCorrelationExtension_eq_of_isCoprime K S D C mn.1 mn.2 j hcop)

end HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
