import FiniteMixedCorrelationFourier
import SIntegerSexticOriginalCorrelationDefinition

/-! SOURCE ONLY, UNRUN. Actual original sextic quotient sum identified
with its mixed-domain finite Fourier/Gauss product. The additive character
is supplied on the actual total quotient; primitivity is required only
for inversion, and no trace-character existence is asserted. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R

local instance originalFullFourier_columnFinite (u : N) :
    Finite (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := by
  rw [commonFactorColumnIdeal, Ideal.top_mul]
  exact finite_sIntegerPrincipalResidue K S u.val u.property

local instance originalFullFourier_columnFintype (u : N) :
    Fintype (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) := Fintype.ofFinite _

local instance originalFullFourier_totalFinite (u v : N) :
    Finite (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) := by
  rw [commonFactorTotalIdeal, Ideal.top_mul, Ideal.span_singleton_mul_span_singleton]
  exact finite_sIntegerPrincipalResidue K S (u.val * v.val) (mul_ne_zero u.property v.property)

local instance originalFullFourier_totalFintype (u v : N) :
    Fintype (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) := Fintype.ofFinite _

/-- The pullback to the total quotient is well defined by the proved
quotient multipliers. Its frequency domain is literally modulo u*v. -/
def sIntegerSexticOriginalFullQuotientCorrelation (u v : N)
    (j : R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) : ℂ :=
  mixedCorrelation (commonFactorFirstMultiplier (⊤ : Ideal R) u.val v.val)
    (commonFactorSecondMultiplier (⊤ : Ideal R) u.val v.val)
    (originalColumnWeight K S ζ hζ σ hS6 u)
    (originalColumnWeight K S ζ hζ σ hS6 v) j

@[simp] theorem sIntegerSexticOriginalFullQuotientCorrelation_mk (u v : N) (j : R) :
    sIntegerSexticOriginalFullQuotientCorrelation K S ζ hζ σ hS6 u v
        (Ideal.Quotient.mk _ j) =
      sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j := by
  unfold sIntegerSexticOriginalFullQuotientCorrelation sIntegerSexticOriginalFullCorrelation
  exact mixedCorrelation_eq_sum_fibre _ _ _ _ _

theorem fourier_sIntegerSexticOriginalFullQuotientCorrelation
    (u v : N)
    (ψ : AddChar (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) ℂ)
    (t : R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) :
    fourier ψ (sIntegerSexticOriginalFullQuotientCorrelation K S ζ hζ σ hS6 u v) t =
      (∑ x, originalColumnWeight K S ζ hζ σ hS6 u x *
        ψ (t * commonFactorFirstMultiplier (⊤ : Ideal R) u.val v.val x)) *
      conj (∑ y, originalColumnWeight K S ζ hζ σ hS6 v y *
        ψ (t * commonFactorSecondMultiplier (⊤ : Ideal R) u.val v.val y)) :=
  fourier_mixedCorrelation ψ _ _ _ _ t

/-- Exact inverse normalization for the actual original quotient sum.
All nonunit-frequency and character zero cases remain in the finite sums. -/
theorem sIntegerSexticOriginalFullCorrelation_inverse
    (u v : N)
    (ψ : AddChar (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) ℂ)
    (hψ : ψ.IsPrimitive) (j : R) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j =
      (Fintype.card (R ⧸ commonFactorTotalIdeal (⊤ : Ideal R) u.val v.val) : ℂ)⁻¹ *
        ∑ t, ((∑ x, originalColumnWeight K S ζ hζ σ hS6 u x *
          ψ (t * commonFactorFirstMultiplier (⊤ : Ideal R) u.val v.val x)) *
          conj (∑ y, originalColumnWeight K S ζ hζ σ hS6 v y *
            ψ (t * commonFactorSecondMultiplier (⊤ : Ideal R) u.val v.val y))) *
          ψ (-(t * Ideal.Quotient.mk _ j)) := by
  rw [← sIntegerSexticOriginalFullQuotientCorrelation_mk K S ζ hζ σ hS6 u v j]
  exact mixedCorrelation_eq_inverse_sum ψ hψ _ _ _ _ _
end HeckeGeneral.Characters
