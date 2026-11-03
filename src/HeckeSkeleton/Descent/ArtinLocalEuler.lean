import HeckeSkeleton.Descent.FiniteCircleEuler
import HeckeSkeleton.Descent.ArtinFrobenius
import HeckeGeneral.Analysis.HeckeSeries

/-! The local Euler polynomial of the complete family of Artin twists.
The actual norm quotient and uniformizer class supply its degree and exponent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.ArtinLocalEuler

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.Descent.Artin
open HeckeSkeleton.Descent.ArtinFrobenius
open HeckeSkeleton.Descent.FiniteCircleEuler
open scoped NumberField Classical BigOperators IsMulCommutative

@[instance_reducible]
private def eulerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (_root_.IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (_root_.IdeleGroup.principalSubgroup F)

attribute [local instance] eulerIdeleClassCommGroup

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

local instance eulerArtinNormQuotientFinite : Finite (ArtinNormQuotient F K) :=
  Finite.of_equiv (K ≃ₐ[F] K)
    (GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv F K).symm.toEquiv

local instance eulerArtinIndexFintype : Fintype (ArtinFactorIndex F K) :=
  Fintype.ofFinite _

theorem natCard_artinNormQuotient :
    Nat.card (ArtinNormQuotient F K) = Module.finrank F K := by
  calc
    Nat.card (ArtinNormQuotient F K) = Nat.card (K ≃ₐ[F] K) :=
      Nat.card_congr
        (GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv F K).toEquiv
    _ = Module.finrank F K := IsGalois.card_aut_eq_finrank F K

/-- Downstairs Euler denominator over the entire actual family, once each. -/
theorem prod_artinEulerPolynomial (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (hχ : UnramifiedAt F χ v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (s : ℂ) :
    (∏ ψ ∈ artinFactors F K χ,
      eulerPolynomial (residueCard F v) (primeCoefficient F ψ v) s) =
      (1 - (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s)) ^
        orderOf (qprime F K v)) ^ (Module.finrank F K / orderOf (qprime F K v)) := by
  rw [artinFactors, Finset.prod_image (artinTwist_injective F K χ).injOn]
  calc
    (∏ ρ : ArtinFactorIndex F K,
        eulerPolynomial (residueCard F v)
          (primeCoefficient F (χ * artinHeckeCharacter F K ρ) v) s) =
        ∏ ρ : ArtinFactorIndex F K,
          (1 - (ρ (qprime F K v) : ℂ) *
            (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s))) := by
      apply Finset.prod_congr rfl
      intro ρ _
      rw [primeCoefficient_artinTwist F K χ ρ v hχ hunram, eulerPolynomial]
      ring
    _ = _ := by
      rw [prod_fullCircleDual_one_sub_mul, natCard_artinNormQuotient]

/-- Taking reciprocals preserves the full-dual identity, including zero factors. -/
theorem prod_artinLocalEulerFactors (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (hχ : UnramifiedAt F χ v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (s : ℂ) :
    (∏ ψ ∈ artinFactors F K χ, heckeLocalEulerFactor F ψ v s) =
      ((1 - (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s)) ^
        orderOf (qprime F K v))⁻¹) ^ (Module.finrank F K / orderOf (qprime F K v)) := by
  simp only [heckeLocalEulerFactor, Finset.prod_inv_distrib]
  rw [prod_artinEulerPolynomial F K χ v hχ hunram, inv_pow]

end HeckeSkeleton.Descent.ArtinLocalEuler
