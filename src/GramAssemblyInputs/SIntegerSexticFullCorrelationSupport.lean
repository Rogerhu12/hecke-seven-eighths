import SIntegerSexticOriginalCorrelationDefinition

/-! SOURCE ONLY, UNRUN. Exact off-divisibility support of the original
genuine full quotient sum. The generic fibre statement does not require
a domain, nonzero common factor, coprime residuals, or a character. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical
variable {R : Type*} [CommRing R]

theorem originalFullFibre_frequency_dvd
    (c n₁ n₂ j : R)
    (p : commonFactorFullFibre (⊤ : Ideal R) (c * n₁) (c * n₂) j) : c ∣ j := by
  rcases p with ⟨⟨x, y⟩, hp⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have herr := (commonFactorFullFibre_relation_mk_iff
    (⊤ : Ideal R) (c * n₁) (c * n₂) j x y).mp hp
  have hspan : (c * n₂) * x - (c * n₁) * y - j ∈
      Ideal.span ({(c * n₁) * (c * n₂)} : Set R) := by
    simpa only [commonFactorTotalIdeal, Ideal.top_mul,
      Ideal.span_singleton_mul_span_singleton] using herr
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hspan
  refine ⟨n₂ * x - n₁ * y - t * (c * n₁ * n₂), ?_⟩
  calc
    j = (c * n₂) * x - (c * n₁) * y - t * ((c * n₁) * (c * n₂)) := by
      linear_combination ht
    _ = c * (n₂ * x - n₁ * y - t * (c * n₁ * n₂)) := by ring

theorem originalFullFibre_frequency_dvd_of_common_divisor
    (u v c j : R) (hu : c ∣ u) (hv : c ∣ v)
    (p : commonFactorFullFibre (⊤ : Ideal R) u v j) : c ∣ j := by
  obtain ⟨n₁, rfl⟩ := hu
  obtain ⟨n₂, rfl⟩ := hv
  exact originalFullFibre_frequency_dvd c n₁ n₂ j p

theorem originalFullFibre_isEmpty_of_not_dvd
    (u v c j : R) (hu : c ∣ u) (hv : c ∣ v) (hj : ¬ c ∣ j) :
    IsEmpty (commonFactorFullFibre (⊤ : Ideal R) u v j) :=
  ⟨fun p => hj (originalFullFibre_frequency_dvd_of_common_divisor u v c j hu hv p)⟩
end HeckeGeneral.Arithmetic.PeriodicFourier

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R

/-- Any actual common divisor forces support of the genuine original
coefficient. Frequency zero is included and is never excluded by this
test, since every common divisor divides zero. -/
theorem sIntegerSexticOriginalFullCorrelation_eq_zero_of_not_dvd
    (u v : N) (c j : R) (hu : c ∣ u.val) (hv : c ∣ v.val) (hj : ¬ c ∣ j) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j = 0 := by
  letI fullCorrelationSupport_empty :
      IsEmpty (commonFactorFullFibre (⊤ : Ideal R) u.val v.val j) :=
    originalFullFibre_isEmpty_of_not_dvd u.val v.val c j hu hv hj
  unfold sIntegerSexticOriginalFullCorrelation
  exact Finset.sum_eq_zero (fun p _ => isEmptyElim p)

theorem sIntegerSexticOriginalFullCorrelation_common_factor_support
    (u v c n₁ n₂ : N) (j : R)
    (hu : u.val = c.val * n₁.val) (hv : v.val = c.val * n₂.val)
    (hj : ¬ c.val ∣ j) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v j = 0 :=
  sIntegerSexticOriginalFullCorrelation_eq_zero_of_not_dvd K S ζ hζ σ hS6
    u v c.val j ⟨n₁.val, hu⟩ ⟨n₂.val, hv⟩ hj
end HeckeGeneral.Characters
