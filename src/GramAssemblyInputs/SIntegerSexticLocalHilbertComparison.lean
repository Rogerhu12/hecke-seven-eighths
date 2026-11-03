import SIntegerSexticSupportedDenominator
import FinitePlaceHilbertBilinear
import SIntegerSexticIntegralHilbertComparison

/-! SOURCE ONLY, UNRUN. Actual exterior tame comparison for arbitrary
nonzero S-integer inputs. A supported integral denominator clears only
the numerator; its nonzero residue character is cancelled multiplicatively.
The denominator exponent remains that of the literal contraction. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem sIntegerSextic_local_hilbert_comparison
    (hmu : (primitiveRoots ((6 : ℕ+) : ℕ) K).Nonempty)
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (hcoprime : (Ideal.absNorm p.asIdeal).Coprime ((6 : ℕ+) : ℕ))
    (a b : NonzeroRingElements (S.integer K))
    (ha : sIntegerSexticResidueMap K S p hpS a.val ≠ 0) :
    σ ((finitePlaceHilbertSymbol K (6 : ℕ+) (by norm_num) hmu p
      (nonzeroSIntegerFieldUnit K S a)
      (nonzeroSIntegerFieldUnit K S b)).val : K) =
      (sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 a.val) ^
        idealPrimeMultiplicity K p (sIntegerModulusContraction K S b.val) := by
  obtain ⟨t, A, _hA0, _hd0, heq, havoid⟩ :=
    exists_sIntegerSextic_supported_denominator K S a
  let d := finiteSIntegerDenominator K S ^ t
  obtain ⟨hd, hAof⟩ := havoid p hpS
  have hA : A ∉ p.asIdeal := hAof ha
  let m := idealPrimeMultiplicity K p (sIntegerModulusContraction K S b.val)
  let E := sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6
  let H := fun u : Kˣ => σ ((finitePlaceHilbertSymbol K (6 : ℕ+)
    (by norm_num) hmu p u (nonzeroSIntegerFieldUnit K S b)).val : K)
  have hunit : primeAvoidingIntegralFieldUnit K p A hA =
      primeAvoidingIntegralFieldUnit K p d hd * nonzeroSIntegerFieldUnit K S a := by
    apply Units.ext
    change (A : K) = (d : K) * (a.val : K)
    exact congrArg (fun x : S.integer K => (x : K)) heq
  have hAcomp : H (primeAvoidingIntegralFieldUnit K p A hA) =
      (sexticResidueEvaluation K ζ hζ σ p hp6 A) ^ m :=
    sIntegerSextic_integralNumerator_hilbert_comparison K S ζ hζ σ
      hmu p hpS hp6 hcoprime A hA b
  have hdcomp : H (primeAvoidingIntegralFieldUnit K p d hd) =
      (sexticResidueEvaluation K ζ hζ σ p hp6 d) ^ m :=
    sIntegerSextic_integralNumerator_hilbert_comparison K S ζ hζ σ
      hmu p hpS hp6 hcoprime d hd b
  have hmul : H (primeAvoidingIntegralFieldUnit K p A hA) =
      H (primeAvoidingIntegralFieldUnit K p d hd) * H (nonzeroSIntegerFieldUnit K S a) := by
    dsimp only [H]
    rw [hunit, finitePlaceHilbertSymbol_mul_left K (6 : ℕ+) (by norm_num) hmu p]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  have heval : sexticResidueEvaluation K ζ hζ σ p hp6 A =
      sexticResidueEvaluation K ζ hζ σ p hp6 d * E a.val := by
    have h := congrArg E heq
    simpa only [E, sIntegerSexticEvaluation_algebraMap, sIntegerSexticEvaluation_mul] using h
  have hdchar : sexticResidueEvaluation K ζ hζ σ p hp6 d ≠ 0 := by
    intro hz
    have hnorm := sexticResidueEvaluation_norm_of_not_mem K ζ hζ σ p hp6 d hd
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  change H (nonzeroSIntegerFieldUnit K S a) = E a.val ^ m
  apply mul_left_cancel₀ (pow_ne_zero m hdchar)
  calc
    (sexticResidueEvaluation K ζ hζ σ p hp6 d) ^ m *
        H (nonzeroSIntegerFieldUnit K S a) =
        H (primeAvoidingIntegralFieldUnit K p A hA) := by rw [← hdcomp, ← hmul]
    _ = (sexticResidueEvaluation K ζ hζ σ p hp6 A) ^ m := hAcomp
    _ = (sexticResidueEvaluation K ζ hζ σ p hp6 d) ^ m * E a.val ^ m := by
      rw [heval, mul_pow]

end HeckeGeneral.Characters
