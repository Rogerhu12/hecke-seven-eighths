import SIntegerExteriorHilbertValuation
import HeckeGeneral.Characters.SexticPowerResidueComparison

/-! SOURCE ONLY, UNRUN. The actual tame Hilbert factor with an integral
prime-unit numerator and an arbitrary nonzero S-integer denominator.
The exponent is the multiplicity in the literal exterior contraction.
Primitive-root and norm-coprime proofs are arbitrary proof parameters;
proof irrelevance connects them to the actual normalized sextic character.
No private main helper, reciprocity identity, or comparison assumption is used. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem sIntegerSextic_integralNumerator_hilbert_comparison
    (hmu : (primitiveRoots ((6 : ℕ+) : ℕ) K).Nonempty)
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (hcoprime : (Ideal.absNorm p.asIdeal).Coprime ((6 : ℕ+) : ℕ))
    (A : 𝓞 K) (hA : A ∉ p.asIdeal)
    (b : NonzeroRingElements (S.integer K)) :
    σ ((finitePlaceHilbertSymbol K (6 : ℕ+) (by norm_num) hmu p
      (primeAvoidingIntegralFieldUnit K p A hA)
      (nonzeroSIntegerFieldUnit K S b)).val : K) =
      (sexticResidueEvaluation K ζ hζ σ p hp6 A) ^
        idealPrimeMultiplicity K p (sIntegerModulusContraction K S b.val) := by
  have hpExponent : p ∉ powerResidueExponentFinitePlaces K (6 : ℕ+) := by
    simpa only [mem_powerResidueExponentFinitePlaces_iff, powerResidueExponentIdeal,
      Ideal.dvd_span_singleton, PNat.val_ofNat, Nat.cast_ofNat] using hp6
  rw [finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor_zpow
    K (6 : ℕ+) (by norm_num) hmu p hpExponent hcoprime A hA,
    neg_finitePlaceNormalizedValuation_sInteger_eq_contraction_multiplicity K S p hpS b,
    zpow_natCast]
  have hprime : sexticResidueEvaluation K ζ hζ σ p hp6 A =
      σ (algebraMap (𝓞 K) K
        ((primeIdealPowerResidueSymbol K p (6 : ℕ+) hmu hcoprime A hA).val : 𝓞 K)) := by
    simpa only using sexticResidueEvaluation_eq_powerResidueSymbol K ζ hζ σ p hp6 A hA
  rw [hprime]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, map_pow,
    integralRootsOfUnityToNthRoots_apply, Units.coe_map]
  rfl

end HeckeGeneral.Characters
