import ActualThetaCoprimeCorrelationExtension
import ActualSexticOriginalChartMean

/-!
UNCOMPILED / native 0. Genuine composite finite correlation is identified
with the actual prime-power residual extension on coprime literal columns.
The final specialization uses the real quotient generators, including
their general unit factors, and a real nonzero frequency. This does not
identify the two finite correlations on arbitrary noncoprime columns.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ActualGramJointChartDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

local notation "OS" => S.integer K
local notation "h6" => jointAwaySix K S C J hC hJ hCS hJS hS6

/-- Real CRT product and local coprime-column evaluation, with the extra
frequency-prime factors contributing one rather than a zero mask. -/
theorem sIntegerSexticFiniteCorrelation_eq_actualResidualExtension_of_isCoprime
    (n₁ n₂ k : OS) (hn : IsCoprime n₁ n₂) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ C hC hCS
        (fun p hp hp6 => hCS p hp (hS6 hp6))
        (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k) =
      actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 1 k n₁ n₂ := by
  let PC := sexticIdealPlaces K C hC
  let PJ := jointPlaces K C J hC hJ
  let f (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
    if hp : p ∈ PC then
      primePowerResidualExtension K S ζ hζ σ p
        (hCS p ((mem_sexticIdealPlaces_iff K C hC p).mp hp))
        (idealPrimeMultiplicity K p C)
        (sexticIdealPlaces_multiplicity_pos K C hC ⟨p, hp⟩)
        (jointAwaySix K S C J hC hJ hCS hJS hS6
          ⟨p, Finset.mem_union_left _ hp⟩)
        (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
    else 1
  have hlocal (p : PC) :
      sIntegerSexticFiniteCorrelation K S ζ hζ σ
          (p.val.asIdeal ^ idealPrimeMultiplicity K p.val C)
          (pow_ne_zero _ p.val.ne_bot)
          (sexticIdealPlacePower_exterior K S C hC hCS p)
          (sexticIdealPlacePower_away_six K C hC
            (fun q hq hq6 => hCS q hq (hS6 hq6)) p)
          (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k) =
        f p.val := by
    dsimp only [f]
    rw [dif_pos p.property]
    exact (primePowerResidualExtension_eq_genuine K S ζ hζ σ p.val
      (hCS p.val ((mem_sexticIdealPlaces_iff K C hC p.val).mp p.property))
      (idealPrimeMultiplicity K p.val C)
      (sexticIdealPlaces_multiplicity_pos K C hC p)
      (h6 ⟨p.val, Finset.mem_union_left _ p.property⟩)
      (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
      (hn.map (Ideal.Quotient.mk _))).symm
  have hprod :
      sIntegerSexticFiniteCorrelation K S ζ hζ σ C hC hCS
          (fun p hp hp6 => hCS p hp (hS6 hp6))
          (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k) =
        ∏ p ∈ PC, f p := by
    rw [sIntegerSexticFiniteCorrelation_eq_prod_primePower]
    simp only [sIntegerSexticIdealCRT_mk]
    rw [← Finset.prod_coe_sort PC f]
    exact Finset.prod_congr rfl (fun p _ => hlocal p)
  have hsub : PC ⊆ PJ := Finset.subset_union_left
  have hextend : (∏ p ∈ PC, f p) = ∏ p ∈ PJ, f p :=
    Finset.prod_subset hsub (fun p _ hp => by simp only [f, dif_neg hp])
  rw [hprod, hextend, ← Finset.prod_coe_sort PJ f]
  unfold actualResidualExtension
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hpc : p.val ∈ PC
  · have he : idealPrimeMultiplicity K p.val C ≠ 0 :=
      Nat.one_le_iff_ne_zero.mp (sexticIdealPlaces_multiplicity_pos K C hC ⟨p.val, hpc⟩)
    simp only [f, dif_pos hpc, primePowerResidualExtension,
      residualColumnFactor, if_neg he, sIntegerPrimePowerReduction_mk,
      jointReduction, map_one, one_mul]
  · have he : idealPrimeMultiplicity K p.val C = 0 := by
      by_contra hne
      apply hpc
      change p.val ∈ (sexticIdealPrimeExponents K C hC).support
      exact Finsupp.mem_support_iff.mpr (by
        simpa only [sexticIdealPrimeExponents_apply] using hne)
    simp only [f, dif_neg hpc, residualColumnFactor, if_pos he]

end HeckeGeneral.Characters.ActualGramJointChartDraft

namespace HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
open HeckeGeneral.Characters.ActualGramJointChartDraft
open HeckeGeneral.Characters.ActualGramJointChartCoverDraft
open scoped Classical ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- The actual coprime residual expression is the literal chart coefficient.
The quotient generators retain both independently chosen general units. -/
theorem thetaResidualCorrelationExpression_eq_originalChartCoefficient
    (C N₁ N₂ : E) (hcop : IsCoprime N₁.val.val N₂.val.val) (k : NZ) :
    let n₁ := thetaGeneratorDivision K S D C N₁ (exteriorMul K S C N₁) rfl
    let n₂ := thetaGeneratorDivision K S D C N₂ (exteriorMul K S C N₂) rfl
    thetaResidualCorrelationExpression K S D C N₁ N₂ k.val =
      originalChartCoefficient K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D C) k
        (⟨1, one_ne_zero⟩ : NZ) n₁ n₂ := by
  let n₁ := thetaGeneratorDivision K S D C N₁ (exteriorMul K S C N₁) rfl
  let n₂ := thetaGeneratorDivision K S D C N₂ (exteriorMul K S C N₂) rfl
  have hn : IsCoprime n₁.val n₂.val :=
    thetaGeneratorDivision_isCoprime K S D C N₁ N₂
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl hcop
  have hf := sIntegerSexticFiniteCorrelation_eq_actualResidualExtension_of_isCoprime
    K S D.root6 D.primitive6 D.embedding C.val.val
    (actualFrequencyIdeal K S k) (nonZeroDivisors.coe_ne_zero C.val)
    (actualFrequencyIdeal_ne_zero K S k) C.property
    (actualFrequencyIdeal_exterior K S k) (probeArithmetic_six_support K S D)
    n₁.val n₂.val k.val hn
  simpa only [thetaResidualCorrelationExpression, originalChartCoefficient,
    sIntegerSexticRawCoefficient, divisorColumn, one_mul, actualFrequencyIdeal,
    probeGenerator_contraction] using
    congrArg (fun z : ℂ =>
      (sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
          (probeArithmetic_six_support K S D) k.val n₁ *
        conj (sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
          (probeArithmetic_six_support K S D) (-k.val) n₂)) *
        sIntegerSexticRCorrection K S D.root6 D.primitive6 D.embedding n₁ n₂ * z) hf

/-- Direct consumption by first Poisson on the actual original generators.
This is only on the coprime residual locus, before Mobius removes it. -/
theorem thetaOriginalFullCorrelation_eq_originalChartCoefficient
    (C N₁ N₂ : E) (hcop : IsCoprime N₁.val.val N₂.val.val) (k : NZ) :
    let n₁ := thetaGeneratorDivision K S D C N₁ (exteriorMul K S C N₁) rfl
    let n₂ := thetaGeneratorDivision K S D C N₂ (exteriorMul K S C N₂) rfl
    sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D)
        (probeGenerator K S D (exteriorMul K S C N₁))
        (probeGenerator K S D (exteriorMul K S C N₂)) (D.generator C * k.val) =
      originalChartCoefficient K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) (probeGenerator K S D C) k
        (⟨1, one_ne_zero⟩ : NZ) n₁ n₂ := by
  have hf :
      sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
          (probeArithmetic_six_support K S D)
          (probeGenerator K S D (exteriorMul K S C N₁))
          (probeGenerator K S D (exteriorMul K S C N₂)) (D.generator C * k.val) =
        thetaResidualCorrelationExpression K S D C N₁ N₂ k.val := by
    simpa only [thetaResidualCorrelationExpression] using
      thetaOriginalFullCorrelation_factorization K S D C N₁ N₂
        (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl hcop k.val
  exact hf.trans (thetaResidualCorrelationExpression_eq_originalChartCoefficient
    K S D C N₁ N₂ hcop k)

end HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
