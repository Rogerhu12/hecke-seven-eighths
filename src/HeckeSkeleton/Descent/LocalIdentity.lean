import HeckeSkeleton.Descent.ArtinLocalEuler
import HeckeSkeleton.Descent.PrimeAssembly
import HeckeSkeleton.Descent.ArtinPrimeArithmetic
import HeckeSkeleton.Descent.LocalNormCoefficients

/-! Actual Euler factors at primes unramified for the character and extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.LocalIdentity

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Characters.NormPullbackDraft
open HeckeSkeleton.Descent.LocalNorm
open HeckeSkeleton.Descent.Artin
open HeckeSkeleton.Descent.ArtinFrobenius
open HeckeSkeleton.Descent.ArtinPrimeArithmetic
open HeckeSkeleton.Descent.ArtinLocalEuler
open HeckeSkeleton.Descent.PrimeAssembly
open scoped Classical BigOperators

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

/-- The actual local factor upstairs depends on v and its actual Artin
order. Complex powers are handled with the positive integral norm base. -/
theorem normPullback_localEulerFactor (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (W : PrimeFiber F K v)
    (hχ : UnramifiedAt F χ v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (s : ℂ) :
    heckeLocalEulerFactor K (heckeNormPullback F K χ) W.val s =
      (1 - (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s)) ^
        orderOf (qprime F K v))⁻¹ := by
  have hcoeff : primeCoefficient K (heckeNormPullback F K χ) W.val =
      primeCoefficient F χ v ^ orderOf (qprime F K v) := by
    rw [primeCoefficient_heckeNormPullback F K χ v W hχ,
      orderOf_qprime_eq_inertiaDeg F K v W hunram]
  have hweight : ((residueCard K W.val : ℝ) : ℂ) ^ (-s) =
      (((residueCard F v : ℝ) : ℂ) ^ (-s)) ^ orderOf (qprime F K v) := by
    simp only [Complex.ofReal_natCast]
    rw [residueCard_primeFiber_eq_pow_orderOf_qprime F K v W hunram,
      Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  simp only [heckeLocalEulerFactor, eulerPolynomial, hcoeff, hweight, ← mul_pow]

/-- The actual good-prime identity, with both character multiplicity and
prime multiplicity proved from the actual extension. -/
theorem good_prime_artin_euler_identity (χ : HeckeCharacter F)
    (v : HeightOneSpectrum (𝓞 F)) (hχ : UnramifiedAt F χ v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v)
    (s : ℂ) :
    (∏ W : PrimeFiber F K v,
      heckeLocalEulerFactor K (heckeNormPullback F K χ) W.val s) =
      ∏ ψ ∈ artinFactors F K χ, heckeLocalEulerFactor F ψ v s := by
  calc
    _ = ∏ _W : PrimeFiber F K v,
        (1 - (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s)) ^
          orderOf (qprime F K v))⁻¹ := by
      apply Finset.prod_congr rfl
      intro W _
      exact normPullback_localEulerFactor F K χ v W hχ hunram s
    _ = ((1 - (primeCoefficient F χ v * ((residueCard F v : ℝ) : ℂ) ^ (-s)) ^
          orderOf (qprime F K v))⁻¹) ^
          (Module.finrank F K / orderOf (qprime F K v)) := by
      rw [Finset.prod_const, Finset.card_univ,
        card_primeFiber_eq_finrank_div_orderOf_qprime F K v hunram]
    _ = _ := (prod_artinLocalEulerFactors F K χ v hχ hunram s).symm

end HeckeSkeleton.Descent.LocalIdentity
