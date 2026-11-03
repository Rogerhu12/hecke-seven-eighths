import FiniteAffineCorrelation
import HeckeGeneral.Characters.SIntegerSexticIdealEvaluation

/-! SOURCE ONLY, UNRUN. The genuine unnormalized L_C congruence sum on the
actual finite S-integer quotient. Its character is the actual normalized
sextic ideal quotient function, including all shared-prime zero masks.
Subgroup invariance is proved from the literal sixth-power theorem; no
abstract invariant coefficient, ray correction, or artificial extension is
substituted. No identification with the full correlation F is asserted. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
local notation "J" => I.map (algebraMap (𝓞 K) (S.integer K))
local notation "Q" => S.integer K ⧸ J
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6

/-- Reduction of an ORIGINAL S-unit is an actual quotient unit, even if
I is composite or the quotient is the zero ring. -/
def sIntegerSexticCorrelationQuotientUnit (u : S.unit K) : Qˣ :=
  Units.map (Ideal.Quotient.mk J).toMonoidHom (S.unitEquivUnitsInteger K u)

@[simp] theorem sIntegerSexticCorrelationQuotientUnit_val (u : S.unit K) :
    (sIntegerSexticCorrelationQuotientUnit K S I u : Q) =
      Ideal.Quotient.mk J (S.unitEquivUnitsInteger K u).val := rfl

variable (Γ : Subgroup (S.unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : S.unit K →* S.unit K).range)

include hΓ in
/-- Actual quotient-function invariance, derived by surjectivity and literal
ideal-evaluation invariance, with no numerator coprimality restriction. -/
theorem sIntegerSexticIdealQuotientFunction_literal_invariant
    (γ : Γ) (q : Q) :
    Φ ((sIntegerSexticCorrelationQuotientUnit K S I γ.val : Q) * q) = Φ q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Φ (Ideal.Quotient.mk J (S.unitEquivUnitsInteger K γ.val).val *
    Ideal.Quotient.mk J a) = Φ (Ideal.Quotient.mk J a)
  rw [← map_mul]
  simpa only [sIntegerSexticIdealQuotientFunction_mk] using
    sIntegerSexticIdealEvaluation_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ γ a

/-- Genuine unnormalized common-modulus lift coefficient:
sum_{x,y mod I_OS; n₂*x-n₁*y=k} χ_I(x) conj(χ_I(y)).
It remains the genuine congruence sum even when both residual columns
share a prime; it is NOT the artificial zero-on-common-prime extension. -/
def sIntegerSexticFiniteCorrelation (n₁ n₂ k : Q) : ℂ :=
  letI := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI := Fintype.ofFinite Q
  affineCorrelation Φ n₁ n₂ k

include hΓ in
/-- Independent original subgroup actions on both columns and the frequency. -/
theorem sIntegerSexticFiniteCorrelation_unit_covariance
    (u v : Γ) (n₁ n₂ k : Q) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6
      ((sIntegerSexticCorrelationQuotientUnit K S I u.val : Q) * n₁)
      ((sIntegerSexticCorrelationQuotientUnit K S I v.val : Q) * n₂)
      (((sIntegerSexticCorrelationQuotientUnit K S I u.val *
          sIntegerSexticCorrelationQuotientUnit K S I v.val : Qˣ) : Q) * k) =
      sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 n₁ n₂ k := by
  letI := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI := Fintype.ofFinite Q
  exact affineCorrelation_unit_covariance Φ
    (sIntegerSexticCorrelationQuotientUnit K S I u.val)
    (sIntegerSexticCorrelationQuotientUnit K S I v.val)
    (sIntegerSexticIdealQuotientFunction_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ u)
    (sIntegerSexticIdealQuotientFunction_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ v)
    n₁ n₂ k

include hΓ in
/-- Actual frequency-unit invariance at fixed columns, supplied separately
from joint covariance so that the latter can legitimately keep k fixed. -/
theorem sIntegerSexticFiniteCorrelation_frequency_unit_invariant
    (u : Γ) (n₁ n₂ k : Q) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 n₁ n₂
      ((sIntegerSexticCorrelationQuotientUnit K S I u.val : Q) * k) =
      sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 n₁ n₂ k := by
  letI := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI := Fintype.ofFinite Q
  exact affineCorrelation_frequency_unit_invariant Φ
    (sIntegerSexticCorrelationQuotientUnit K S I u.val)
    (sIntegerSexticIdealQuotientFunction_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ u)
    n₁ n₂ k

include hΓ in
/-- Fixed-frequency column invariance, explicitly combining JOINT covariance
with the separate frequency substitution. No conclusion is taken from joint
covariance alone. Both original subgroup elements remain independent. -/
theorem sIntegerSexticFiniteCorrelation_columns_invariant_at_fixed_frequency
    (u v : Γ) (n₁ n₂ k : Q) :
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6
      ((sIntegerSexticCorrelationQuotientUnit K S I u.val : Q) * n₁)
      ((sIntegerSexticCorrelationQuotientUnit K S I v.val : Q) * n₂) k =
      sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 n₁ n₂ k := by
  letI := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI := Fintype.ofFinite Q
  let U := sIntegerSexticCorrelationQuotientUnit K S I u.val
  let V := sIntegerSexticCorrelationQuotientUnit K S I v.val
  have hUV : ∀ q : Q, Φ (((U * V : Qˣ) : Q) * q) = Φ q := by
    intro q
    rw [Units.val_mul, mul_assoc]
    rw [sIntegerSexticIdealQuotientFunction_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ u,
      sIntegerSexticIdealQuotientFunction_literal_invariant K S ζ hζ σ I hI hS h6 Γ hΓ v]
  have hfreq := affineCorrelation_frequency_unit_invariant Φ (U * V) hUV
    ((U : Q) * n₁) ((V : Q) * n₂) k
  have hcov := sIntegerSexticFiniteCorrelation_unit_covariance K S ζ hζ σ I hI hS h6 Γ hΓ u v n₁ n₂ k
  exact hfreq.symm.trans hcov

end HeckeGeneral.Characters
