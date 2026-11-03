import ActualSexticOriginalChartMean

/-!
UNCOMPILED / native 0. The literal original chart coefficient depends on
the divisor and its two columns only through their two products. This is
an identity on the stipulated residual extension, including noncoprime
columns. No genuine-correlation identification, unit invariance, nonzero
residue, or coprimality hypothesis is used. The local absent-prime branch
and the common-zero extension are left unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ActualOriginalChartProductDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS

section GeneralIdeals

variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The same two reduced products occur on both sides, before evaluating
any residual character or its common-zero branch. All four inputs may be
zero S-integers; only the ideals have their defining nonzero premises. -/
theorem actualResidualExtension_eq_one_products (d k m₁ m₂ : OS) :
    actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 d k m₁ m₂ =
      actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6
        1 k (d * m₁) (d * m₂) := by
  unfold actualResidualExtension
  apply Finset.prod_congr rfl
  intro p _
  simp only [residualColumnFactor, jointReduction, map_mul, map_one, one_mul]

end GeneralIdeals

variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- Product-only reduction of the actual raw-symbol times actual R
correction times residual extension. The frequency and both defining
ideals remain fixed; the divisor need not be a unit. -/
theorem originalChartCoefficient_eq_one_products (c k d m₁ m₂ : NZ) :
    originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂ =
      originalChartCoefficient K S ζ hζ σ hS6 c k (⟨1, one_ne_zero⟩ : NZ)
        (divisorColumn K S d m₁) (divisorColumn K S d m₂) := by
  have hone (m : NZ) : divisorColumn K S (⟨1, one_ne_zero⟩ : NZ) m = m := by
    apply Subtype.ext
    exact one_mul m.val
  unfold originalChartCoefficient
  rw [hone, hone]
  congr 1
  exact actualResidualExtension_eq_one_products K S ζ hζ σ
    (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
    (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
    (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k) hS6
    d.val k.val m₁.val m₂.val

end HeckeGeneral.Characters.ActualOriginalChartProductDraft
