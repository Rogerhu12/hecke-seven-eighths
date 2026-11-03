import ActualThetaResidualCorrelationToChart

/-!
UNCOMPILED / native 0. The actual nonzero frequency is divided only when
the real common generator divides it. The resulting quotient is proved
nonzero. The artificial chart coefficient is defined on every residual
ideal pair, identified with the original correlation only on coprime
residual pairs, then consumed by the genuine finite gcd/Mobius theorem.
All general generator units and all original zero extensions remain.
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
open HeckeGeneral.Characters.ActualGramJointChartCoverDraft
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "E" => ExteriorIdeal K S
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS

/-- Literal division of a nonzero frequency by an actual common generator.
The nonzero quotient is a consequence, not an extra arithmetic premise. -/
def thetaChartFrequencyQuotient (C : E) (j : NZ) (h : D.generator C ∣ j.val) : NZ :=
  ⟨Classical.choose h, by
    intro hk
    apply j.property
    calc
      j.val = D.generator C * Classical.choose h := Classical.choose_spec h
      _ = 0 := by rw [hk, mul_zero]⟩

@[simp] theorem thetaChartFrequencyQuotient_val
    (C : E) (j : NZ) (h : D.generator C ∣ j.val) :
    (thetaChartFrequencyQuotient K S D C j h).val = Classical.choose h := rfl

theorem thetaChartFrequencyQuotient_factor
    (C : E) (j : NZ) (h : D.generator C ∣ j.val) :
    D.generator C * (thetaChartFrequencyQuotient K S D C j h).val = j.val :=
  (Classical.choose_spec h).symm

/-- The artificial residual extension is supplied on ALL residual columns.
No coprimality is built into the definition after Mobius reindexing. -/
def thetaChartCorrelationExtension (C : E) (mn : E × E) (j : NZ) : ℂ :=
  if h : D.generator C ∣ j.val then
    originalChartCoefficient K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D) (probeGenerator K S D C)
      (thetaChartFrequencyQuotient K S D C j h) (⟨1, one_ne_zero⟩ : NZ)
      (thetaGeneratorDivision K S D C mn.1 (exteriorMul K S C mn.1) rfl)
      (thetaGeneratorDivision K S D C mn.2 (exteriorMul K S C mn.2) rfl)
  else 0

theorem thetaChartCorrelationExtension_eq_of_dvd
    (C : E) (mn : E × E) (j : NZ) (h : D.generator C ∣ j.val) :
    thetaChartCorrelationExtension K S D C mn j =
      originalChartCoefficient K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D C)
        (thetaChartFrequencyQuotient K S D C j h) (⟨1, one_ne_zero⟩ : NZ)
        (thetaGeneratorDivision K S D C mn.1 (exteriorMul K S C mn.1) rfl)
        (thetaGeneratorDivision K S D C mn.2 (exteriorMul K S C mn.2) rfl) := by
  rw [thetaChartCorrelationExtension, dif_pos h]

theorem thetaChartCorrelationExtension_eq_zero_of_not_dvd
    (C : E) (mn : E × E) (j : NZ) (hj : ¬ D.generator C ∣ j.val) :
    thetaChartCorrelationExtension K S D C mn j = 0 := by
  rw [thetaChartCorrelationExtension, dif_neg hj]

/-- The only equality with the original full correlation is on the
coprime residual locus required by the generic gcd/Mobius theorem. -/
theorem thetaChartCorrelationExtension_eq_of_isCoprime
    (C N₁ N₂ : E) (j : NZ) (hcop : IsCoprime N₁.val.val N₂.val.val) :
    thetaChartCorrelationExtension K S D C (N₁, N₂) j =
      sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D)
        (probeGenerator K S D (exteriorMul K S C N₁))
        (probeGenerator K S D (exteriorMul K S C N₂)) j.val := by
  by_cases hd : D.generator C ∣ j.val
  · rw [thetaChartCorrelationExtension, dif_pos hd]
    have hf := thetaOriginalFullCorrelation_eq_originalChartCoefficient
      K S D C N₁ N₂ hcop (thetaChartFrequencyQuotient K S D C j hd)
    exact hf.symm.trans (congrArg
      (fun a => sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D)
        (probeGenerator K S D (exteriorMul K S C N₁))
        (probeGenerator K S D (exteriorMul K S C N₂)) a)
      (thetaChartFrequencyQuotient_factor K S D C j hd))
  · rw [thetaChartCorrelationExtension, dif_neg hd]
    exact (thetaOriginalFullCorrelation_eq_zero_of_not_dvd K S D C N₁ N₂
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl j.val hd).symm

/-- Real weighted full-correlation double sum, regrouped through the
artificial chart extension before enlarging to all Mobius residual pairs.
No equality at noncoprime residual pairs is asserted or used. -/
theorem sum_weighted_originalFullCorrelation_eq_gcd_mobius_chart
    (A B : Finset E) (b : E → E → ℂ) (j : NZ) :
    (∑ I ∈ A, ∑ J ∈ B,
      b I J * sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D I)
        (probeGenerator K S D J) j.val) =
      ∑ C ∈ finiteCommonParts K S A B,
        ∑ T ∈ (residualPrimeEnvelope K S C A B).powerset.attach,
          (moebius (primeProduct T.val) : ℂ) *
            ∑ mn ∈ mobiusResidualPairs K S C (residualMobiusDivisor K S C A B T) A B,
              b (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.1))
                (exteriorMul K S C
                  (exteriorMul K S (residualMobiusDivisor K S C A B T) mn.2)) *
              thetaChartCorrelationExtension K S D C
                (exteriorPairDilation K S (residualMobiusDivisor K S C A B T) mn) j := by
  apply sum_pair_eq_gcd_mobius_of_coprime_extension K S A B
    (fun I J => b I J * sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
      (probeArithmetic_six_support K S D) (probeGenerator K S D I)
      (probeGenerator K S D J) j.val)
    (fun C mn => b (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) *
      thetaChartCorrelationExtension K S D C mn j)
  intro C _ mn _ hcop
  exact congrArg (b (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) * ·)
    (thetaChartCorrelationExtension_eq_of_isCoprime K S D C mn.1 mn.2 j hcop)

end HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
