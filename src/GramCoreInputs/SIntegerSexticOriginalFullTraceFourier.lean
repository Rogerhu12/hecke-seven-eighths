import SIntegerSexticOriginalFullFourier
import HeckeGeneral.Characters.SIntegerModulusPhaseUnit

/-! SOURCE ONLY, UNRUN. Constructed standard-local and positive S-local
trace characters in the original full Fourier inversion. Every frequency
of the actual total quotient is retained, including zero and nonunits. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open NumberField.StandardAddChar
open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R
local notation "T" => (fun (u v : N) => R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) (Subtype.val u) (Subtype.val v))

def originalFullTotalPrincipalEquiv (u v : N) :
    T u v ≃+* (R ⧸ Ideal.span ({u.val * v.val} : Set R)) :=
  Ideal.quotEquivOfEq (by
    rw [commonFactorTotalIdeal, Ideal.top_mul, Ideal.span_singleton_mul_span_singleton])

local instance traceFull_columnFinite (u : N) :
    Finite (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := by
  rw [commonFactorColumnIdeal, Ideal.top_mul]
  exact finite_sIntegerPrincipalResidue K S u.val u.property
local instance traceFull_columnFintype (u : N) :
    Fintype (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := Fintype.ofFinite _
local instance traceFull_totalFinite (u v : N) : Finite (T u v) := by
  letI : Finite (R ⧸ Ideal.span ({u.val * v.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S _ (mul_ne_zero u.property v.property)
  exact Finite.of_equiv _ (originalFullTotalPrincipalEquiv K S u v).symm.toEquiv
local instance traceFull_totalFintype (u v : N) : Fintype (T u v) := Fintype.ofFinite _

/-- Actual primitive CRT character, with local different exponents. -/
def originalFullCanonicalTraceCharacter (u v : N) : AddChar (T u v) ℂ :=
  transportCharacter (originalFullTotalPrincipalEquiv K S u v)
    (sIntegerModulusAddCharacter K S (u.val * v.val) (mul_ne_zero u.property v.property))

theorem originalFullCanonicalTraceCharacter_isPrimitive (u v : N) :
    (originalFullCanonicalTraceCharacter K S u v).IsPrimitive :=
  transportCharacter_isPrimitive _ _ (sIntegerModulusAddCharacter_isPrimitive K S _ _)

/-- Canonical normalization: product of psi_v(pi_v^{-(n_v+d_v)}a). -/
theorem originalFullCanonicalTraceCharacter_mk (u v : N) (a : R) :
    originalFullCanonicalTraceCharacter K S u v (Ideal.Quotient.mk _ a) =
      ∏ p : sIntegerModulusPlaces K S (u.val * v.val) (mul_ne_zero u.property v.property),
        psiLocal K p.val
          (localUniformizer K p.val ^
            (-((sIntegerModulusPrimeExponents K S (u.val * v.val)
                (mul_ne_zero u.property v.property) p.val : ℤ) +
              localDifferentExponent K p.val)) *
            algebraMap K (p.val.adicCompletion K) a.val) := by
  change sIntegerModulusAddCharacter K S _ _
    ((originalFullTotalPrincipalEquiv K S u v) (Ideal.Quotient.mk _ a)) = _
  rw [originalFullTotalPrincipalEquiv, Ideal.quotEquivOfEq_mk]
  exact sIntegerModulusAddCharacter_mk K S _ _ a

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- No supplied additive-character or primitivity premise. The normalization
is exactly the reciprocal cardinality of OS/(u*v). -/
theorem sIntegerSexticOriginalFullCorrelation_canonical_trace_inverse (u v : N) (j : R) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j =
      (Fintype.card (T u v) : ℂ)⁻¹ *
        ∑ t : T u v,
          ((∑ x, originalColumnWeight K S ζ hζ σ hS6 u x *
            originalFullCanonicalTraceCharacter K S u v
              (t * commonFactorFirstMultiplier (⊤ : Ideal R) u.val v.val x)) *
           conj (∑ y, originalColumnWeight K S ζ hζ σ hS6 v y *
            originalFullCanonicalTraceCharacter K S u v
              (t * commonFactorSecondMultiplier (⊤ : Ideal R) u.val v.val y))) *
          originalFullCanonicalTraceCharacter K S u v (-(t * Ideal.Quotient.mk _ j)) :=
  sIntegerSexticOriginalFullCorrelation_inverse K S ζ hζ σ hS6 u v
    (originalFullCanonicalTraceCharacter K S u v)
    (originalFullCanonicalTraceCharacter_isPrimitive K S u v) j

variable (hDifferent : ∀ p : HeightOneSpectrum (𝓞 K),
  p ∉ S → localDifferentExponent K p = 0)

/-- The positive principal S-local phase, including its genuine unit shift. -/
def originalFullPositiveTraceCharacter (u v : N) : AddChar (T u v) ℂ :=
  transportCharacter (originalFullTotalPrincipalEquiv K S u v)
    (sIntegerActualModulusAddCharacter K S hDifferent (u.val * v.val)
      (mul_ne_zero u.property v.property))

theorem originalFullPositiveTraceCharacter_isPrimitive (u v : N) :
    (originalFullPositiveTraceCharacter K S hDifferent u v).IsPrimitive :=
  transportCharacter_isPrimitive _ _ (sIntegerActualModulusAddCharacter_isPrimitive K S hDifferent _ _)

/-- Positive exp(2*pi*i*Tr(a/(uv))) times the original S-local factors.
Consequently the inverse-sum phase has argument -t*j/(uv); the two
column phases have arguments t*v*x/(uv) and t*u*y/(uv), respectively. -/
theorem originalFullPositiveTraceCharacter_mk (u v : N) (a : R) :
    originalFullPositiveTraceCharacter K S hDifferent u v (Ideal.Quotient.mk _ a) =
      sLocalPrincipalPhase K S ((a : K) / ((u.val : K) * (v.val : K))) := by
  rw [originalFullPositiveTraceCharacter, transportCharacter_apply]
  rw [originalFullTotalPrincipalEquiv, Ideal.quotEquivOfEq_mk,
    sIntegerActualModulusAddCharacter_mk]
  rfl

theorem sIntegerSexticOriginalFullCorrelation_positive_trace_inverse (u v : N) (j : R) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j =
      (Fintype.card (T u v) : ℂ)⁻¹ *
        ∑ t : T u v,
          ((∑ x, originalColumnWeight K S ζ hζ σ hS6 u x *
            originalFullPositiveTraceCharacter K S hDifferent u v
              (t * commonFactorFirstMultiplier (⊤ : Ideal R) u.val v.val x)) *
           conj (∑ y, originalColumnWeight K S ζ hζ σ hS6 v y *
            originalFullPositiveTraceCharacter K S hDifferent u v
              (t * commonFactorSecondMultiplier (⊤ : Ideal R) u.val v.val y))) *
          originalFullPositiveTraceCharacter K S hDifferent u v (-(t * Ideal.Quotient.mk _ j)) :=
  sIntegerSexticOriginalFullCorrelation_inverse K S ζ hζ σ hS6 u v
    (originalFullPositiveTraceCharacter K S hDifferent u v)
    (originalFullPositiveTraceCharacter_isPrimitive K S hDifferent u v) j

end HeckeGeneral.Characters
