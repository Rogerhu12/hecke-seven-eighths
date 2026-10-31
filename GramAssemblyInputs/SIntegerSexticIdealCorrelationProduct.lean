import SIntegerSexticIdealCRT
import SIntegerSexticFiniteCorrelation

/-! SOURCE ONLY, UNCOMPILED.

The actual sextic ideal quotient function factors through the actual
prime-power CRT, including nonunits and zero. Applying the proved finite
product theorem gives the genuine common-modulus affine correlation.
Every frequency and every pair of columns is retained. No residual
coprimality premise, field structure on a prime-power quotient, or
artificial extension is used in this product identity.
-/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

local notation "Q" => S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6
local notation "e" => sIntegerSexticIdealCRT K S I hI

include h6 in
theorem sexticIdealPlace_not_six (p : sexticIdealPlaces K I hI) :
    (6 : 𝓞 K) ∉ p.val.asIdeal :=
  h6 p.val ((mem_sexticIdealPlaces_iff K I hI p.val).mp p.property)

def sexticIdealPlacePower_exterior (p : sexticIdealPlaces K I hI) :
    ∀ q : HeightOneSpectrum (𝓞 K),
      q.asIdeal ∣ p.val.asIdeal ^ idealPrimeMultiplicity K p.val I → q ∉ S :=
  primePower_exterior K S p.val (sexticIdealPlaces_not_mem K S I hI hS p)
    (idealPrimeMultiplicity K p.val I)

def sexticIdealPlacePower_away_six (p : sexticIdealPlaces K I hI) :
    ∀ q : HeightOneSpectrum (𝓞 K),
      q.asIdeal ∣ p.val.asIdeal ^ idealPrimeMultiplicity K p.val I →
        (6 : 𝓞 K) ∉ q.asIdeal :=
  primePower_away_six K p.val (idealPrimeMultiplicity K p.val I)
    (sexticIdealPlace_not_six K I hI h6 p)

/-- The local weight is the existing actual ideal quotient function for
the actual prime-power factor, with its full zero extension. -/
abbrev sexticIdealLocalQuotientFunction (p : sexticIdealPlaces K I hI) :
    sIntegerPrimePowerQuotient K S p.val (idealPrimeMultiplicity K p.val I) → ℂ :=
  sIntegerSexticIdealQuotientFunction K S ζ hζ σ
    (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I)
    (pow_ne_zero _ p.val.ne_bot)
    (sexticIdealPlacePower_exterior K S I hI hS p)
    (sexticIdealPlacePower_away_six K I hI h6 p)

/-- Identification on every representative, including S-integers with
denominators and representatives divisible by the prime. The strictly
positive actual exponent allows the zero-extended MulChar power rule. -/
theorem sexticIdealLocalQuotientFunction_mk
    (p : sexticIdealPlaces K I hI) (a : S.integer K) :
    sexticIdealLocalQuotientFunction K S ζ hζ σ I hI hS h6 p
      (Ideal.Quotient.mk (sexticIdealLocalIdeal K S I hI p) a) =
      sIntegerSexticEvaluation K S p.val
        (sexticIdealPlaces_not_mem K S I hI hS p) ζ hζ σ
        (sexticIdealPlace_not_six K I hI h6 p) a ^
          idealPrimeMultiplicity K p.val I := by
  have hc := sexticIdealPlaces_multiplicity_pos K I hI p
  change sIntegerSexticIdealQuotientFunction K S ζ hζ σ
      (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I)
      (pow_ne_zero _ p.val.ne_bot)
      (primePower_exterior K S p.val (sexticIdealPlaces_not_mem K S I hI hS p)
        (idealPrimeMultiplicity K p.val I))
      (primePower_away_six K p.val (idealPrimeMultiplicity K p.val I)
        (sexticIdealPlace_not_six K I hI h6 p))
      (Ideal.Quotient.mk _ a) = _
  rw [sIntegerSexticPrimePowerQuotientFunction_eq_pullback K S p.val
    (sexticIdealPlaces_not_mem K S I hI hS p)
    (idealPrimeMultiplicity K p.val I) hc ζ hζ σ
    (sexticIdealPlace_not_six K I hI h6 p),
    sIntegerPrimePowerReduction_mk,
    MulChar.pow_apply' (sexticResidueCharacter K ζ hζ σ p.val
      (sexticIdealPlace_not_six K I hI h6 p)) (Nat.one_le_iff_ne_zero.mp hc)]
  rfl

/-- The global quotient weight is precisely the product of the genuine
prime-power weights in its CRT coordinates, with no restrictions on z. -/
theorem sIntegerSexticIdealQuotientFunction_eq_prod_primePower (z : Q) :
    Φ z = ∏ p : sexticIdealPlaces K I hI,
      sexticIdealLocalQuotientFunction K S ζ hζ σ I hI hS h6 p (e z p) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [sIntegerSexticIdealQuotientFunction_mk]
  symm
  calc
    _ = ∏ p : sexticIdealPlaces K I hI,
        sIntegerSexticEvaluation K S p.val
          (sexticIdealPlaces_not_mem K S I hI hS p) ζ hζ σ
          (sexticIdealPlace_not_six K I hI h6 p) a ^
            idealPrimeMultiplicity K p.val I := by
      apply Finset.prod_congr rfl
      intro p _
      rw [sIntegerSexticIdealCRT_mk, sexticIdealLocalQuotientFunction_mk]
    _ = sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a :=
      sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ I hI hS h6
        (sexticIdealPlaces K I hI)
        (fun p hp => hS p ((mem_sexticIdealPlaces_iff K I hI p).mp hp))
        (fun p hp => h6 p ((mem_sexticIdealPlaces_iff K I hI p).mp hp))
        (fun p hp => (mem_sexticIdealPlaces_iff K I hI p).mpr hp) a

/-- Genuine composite correlation = product of genuine local correlations.
This identity includes zero frequency, zero columns, and columns sharing
prime factors. Coprimality is only required by separate local evaluation
formulas, never by the CRT product identity itself. -/
theorem sIntegerSexticFiniteCorrelation_eq_prod_primePower (n₁ n₂ k : Q) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 n₁ n₂ k =
      ∏ p : sexticIdealPlaces K I hI,
        sIntegerSexticFiniteCorrelation K S ζ hζ σ
          (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I)
          (pow_ne_zero _ p.val.ne_bot)
          (sexticIdealPlacePower_exterior K S I hI hS p)
          (sexticIdealPlacePower_away_six K I hI h6 p)
          (e n₁ p) (e n₂ p) (e k p) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI : Fintype Q := Fintype.ofFinite Q
  letI : ∀ p : sexticIdealPlaces K I hI,
      Finite (sIntegerPrimePowerQuotient K S p.val (idealPrimeMultiplicity K p.val I)) :=
    fun p => finite_sIntegerSexticIdealQuotient K S
      (p.val.asIdeal ^ idealPrimeMultiplicity K p.val I)
      (pow_ne_zero _ p.val.ne_bot) (sexticIdealPlacePower_exterior K S I hI hS p)
  letI : ∀ p : sexticIdealPlaces K I hI,
      Fintype (sIntegerPrimePowerQuotient K S p.val (idealPrimeMultiplicity K p.val I)) :=
    fun _ => Fintype.ofFinite _
  change affineCorrelation Φ n₁ n₂ k =
    ∏ p : sexticIdealPlaces K I hI,
      affineCorrelation
        (sexticIdealLocalQuotientFunction K S ζ hζ σ I hI hS h6 p)
        (e n₁ p) (e n₂ p) (e k p)
  have hf : Φ = fun z => ∏ p : sexticIdealPlaces K I hI,
      sexticIdealLocalQuotientFunction K S ζ hζ σ I hI hS h6 p (e z p) :=
    funext (sIntegerSexticIdealQuotientFunction_eq_prod_primePower K S ζ hζ σ I hI hS h6)
  rw [hf]
  exact affineCorrelation_ringEquiv_pi e
    (sexticIdealLocalQuotientFunction K S ζ hζ σ I hI hS h6) n₁ n₂ k

end HeckeGeneral.Characters
