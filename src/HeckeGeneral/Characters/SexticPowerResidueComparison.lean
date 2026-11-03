import HeckeGeneral.Characters.SexticResidueCharacter
import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal

/-! The upstream symbol and the complex
character use the same literal quotient power residue. No completion
comparison or reciprocity theorem is used. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
variable (σ : K →+* ℂ) (p : HeightOneSpectrum (𝓞 K))

local instance specifiedSexticComparisonResidueField : Field (𝓞 K ⧸ p.asIdeal) :=
  Ideal.Quotient.field _
local instance specifiedSexticComparisonResidueFintype : Fintype (𝓞 K ⧸ p.asIdeal) :=
  Fintype.ofFinite _

include hζ in
private theorem specifiedSexticPrimitiveRoots :
    (primitiveRoots ((6 : ℕ+) : ℕ) K).Nonempty :=
  ⟨ζ, (mem_primitiveRoots (by norm_num)).mpr hζ⟩

include hζ in
theorem specifiedSexticNormCoprime (hp : (6 : 𝓞 K) ∉ p.asIdeal) :
    (Ideal.absNorm p.asIdeal).Coprime ((6 : ℕ+) : ℕ) := by
  have hdiv := six_dvd_card_residue_sub_one K ζ hζ p hp
  have hcard : Fintype.card (𝓞 K ⧸ p.asIdeal) = Ideal.absNorm p.asIdeal :=
    card_primeIdealResidueField K p
  have hpos : 1 ≤ Fintype.card (𝓞 K ⧸ p.asIdeal) :=
    Nat.le_of_lt Fintype.one_lt_card
  have hcop : (Fintype.card (𝓞 K ⧸ p.asIdeal)).Coprime
      (Fintype.card (𝓞 K ⧸ p.asIdeal) - 1) :=
    (Nat.coprime_self_sub_right hpos).mpr (Nat.coprime_one_right _)
  simpa only [hcard, PNat.val_ofNat] using hcop.of_dvd_right hdiv

/-- At a prime-unit argument, the actual complex character is the image
of the upstream integral root of unity, with the specified normalization. -/
theorem sexticResidueEvaluation_eq_powerResidueSymbol
    (hp : (6 : 𝓞 K) ∉ p.asIdeal) (a : 𝓞 K) (ha : a ∉ p.asIdeal) :
    sexticResidueEvaluation K ζ hζ σ p hp a =
      σ (algebraMap (𝓞 K) K
        ((primeIdealPowerResidueSymbol K p (6 : ℕ+)
          (specifiedSexticPrimitiveRoots K ζ hζ)
          (specifiedSexticNormCoprime K ζ hζ p hp) a ha).val : 𝓞 K)) := by
  let r : rootsOfUnity 6 (𝓞 K) :=
    primeIdealPowerResidueSymbol K p (6 : ℕ+)
      (specifiedSexticPrimitiveRoots K ζ hζ)
      (specifiedSexticNormCoprime K ζ hζ p hp) a ha
  obtain ⟨i, _hi, hpow⟩ :=
    (isPrimitiveRoot_sexticIntegerRootUnit K ζ hζ).eq_pow_of_mem_rootsOfUnity r.property
  have hred := congrArg
    (fun z : rootsOfUnity 6 (𝓞 K ⧸ p.asIdeal) =>
      ((z : (𝓞 K ⧸ p.asIdeal)ˣ) : 𝓞 K ⧸ p.asIdeal))
    (rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol K p (6 : ℕ+)
      (specifiedSexticPrimitiveRoots K ζ hζ)
      (specifiedSexticNormCoprime K ζ hζ p hp) a ha)
  change Ideal.Quotient.mk p.asIdeal (r.val : 𝓞 K) =
    (Ideal.Quotient.mk p.asIdeal a) ^
      ((Fintype.card (𝓞 K ⧸ p.asIdeal) - 1) / 6) at hred
  have hroot := congrArg
    (fun w : (𝓞 K)ˣ => Ideal.Quotient.mk p.asIdeal (w : 𝓞 K)) hpow
  have hresiduePower :
      (primeIdealResidueUnit K p a ha) ^
          ((Fintype.card (𝓞 K ⧸ p.asIdeal) - 1) / 6) =
        sexticResidueRootUnit K ζ hζ p ^ i := by
    apply Units.ext
    have h := hred.symm.trans hroot.symm
    simpa only [Units.val_pow_eq_pow_val, map_pow,
      val_sexticIntegerRootUnit, val_sexticResidueRootUnit,
      primeIdealResidueUnit, Units.val_mk0] using h
  have hcomplex := congrArg
    (fun w : (𝓞 K)ˣ => σ (algebraMap (𝓞 K) K (w : 𝓞 K))) hpow
  have hcomplex' : (σ ζ) ^ i = σ (algebraMap (𝓞 K) K (r.val : 𝓞 K)) := by
    simpa only [Units.val_pow_eq_pow_val, map_pow,
      val_sexticIntegerRootUnit, coe_sexticIntegerRoot] using hcomplex
  calc
    sexticResidueEvaluation K ζ hζ σ p hp a = (σ ζ) ^ i :=
      sexticResidueCharacter_of_power_residue K ζ hζ σ p hp
        (primeIdealResidueUnit K p a ha) i hresiduePower
    _ = _ := hcomplex'

/-- The only extension at a prime-divisible argument is the actual zero
extension; no upstream symbol with an invalid prime-unit argument is used. -/
theorem sexticResidueEvaluation_eq_zeroExtended_powerResidueSymbol
    (hp : (6 : 𝓞 K) ∉ p.asIdeal) (a : 𝓞 K) :
    sexticResidueEvaluation K ζ hζ σ p hp a =
      if ha : a ∈ p.asIdeal then 0 else
        σ (algebraMap (𝓞 K) K
          ((primeIdealPowerResidueSymbol K p (6 : ℕ+)
            (specifiedSexticPrimitiveRoots K ζ hζ)
            (specifiedSexticNormCoprime K ζ hζ p hp) a ha).val : 𝓞 K)) := by
  split_ifs with ha
  · exact sexticResidueEvaluation_eq_zero_of_mem K ζ hζ σ p hp a ha
  · exact sexticResidueEvaluation_eq_powerResidueSymbol K ζ hζ σ p hp a ha

end HeckeGeneral.Characters
