import SIntegerSexticOriginalFullCorrelation
import HeckeGeneral.Arithmetic.SIntegerPrincipalization
import Mathlib.RingTheory.PrincipalIdealDomain

/-! SOURCE ONLY, UNRUN. Actual PID common-factor decomposition and genuine
original quotient-sum factorization. The decomposition is chosen before
frequency k, which may be zero. No coprimality with the common factor and
no Fourier/Gauss-sum identification is assumed or claimed. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R

/-- This uses the actual PID instance on O_S. Its existence after finite
enlargement is supplied by SIntegerPrincipalization, not asserted here. -/
theorem exists_sIntegerSexticPID_common_factor [IsPrincipalIdealRing R]
    (u v : N) :
    ∃ c n₁ n₂ : N, ∃ a b : R,
      u.val = c.val * n₁.val ∧ v.val = c.val * n₂.val ∧
        a * n₂.val - b * n₁.val = 1 := by
  letI pidFullFactorization_gcdMonoid : GCDMonoid R := IsBezout.toGCDDomain R
  obtain ⟨x, y, hx, hy, hcop⟩ := extract_gcd u.val v.val
  have hg : GCDMonoid.gcd u.val v.val ≠ 0 := by
    intro hz
    exact u.property ((gcd_eq_zero_iff u.val v.val).mp hz).1
  have hx0 : x ≠ 0 := by
    intro hz
    apply u.property
    rw [hx, hz, mul_zero]
  have hy0 : y ≠ 0 := by
    intro hz
    apply v.property
    rw [hy, hz, mul_zero]
  have hxy : IsCoprime x y := (gcd_isUnit_iff x y).mp hcop
  obtain ⟨r, s, hrs⟩ := hxy
  refine ⟨⟨GCDMonoid.gcd u.val v.val, hg⟩, ⟨x, hx0⟩, ⟨y, hy0⟩, s, -r,
    hx, hy, ?_⟩
  change s * y - (-r) * x = 1
  calc
    s * y - (-r) * x = r * x + s * y := by ring
    _ = 1 := hrs

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6

include hS6 in
theorem sIntegerSexticCommonFactor_away_six (c : N)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val) : (6 : 𝓞 K) ∉ p.asIdeal :=
  fun h => sIntegerSexticCommonFactor_exterior K S c p hp (hS6 h)

/-- Exact original F factorization for any actual common-factor
decomposition with coprime residual columns. No PID is needed after such
a decomposition has been constructed. -/
theorem sIntegerSexticOriginalFullCorrelation_factorization
    (u v c n₁ n₂ : N) (a b k : R)
    (hu : u.val = c.val * n₁.val) (hv : v.val = c.val * n₂.val)
    (hbezout : a * n₂.val - b * n₁.val = 1) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v (c.val * k) =
      (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ *
        sIntegerSexticFiniteCorrelation K S ζ hζ σ
          (sIntegerModulusContraction K S c.val)
          (sIntegerModulusContraction_ne_bot K S c.val c.property)
          (sIntegerSexticCommonFactor_exterior K S c)
          (sIntegerSexticCommonFactor_away_six K S hS6 c)
          (Ideal.Quotient.mk _ n₁.val) (Ideal.Quotient.mk _ n₂.val) (Ideal.Quotient.mk _ k) := by
  have hc : IsCoprime n₁.val n₂.val := by
    refine ⟨-b, a, ?_⟩
    calc
      -b * n₁.val + a * n₂.val = a * n₂.val - b * n₁.val := by ring
      _ = 1 := hbezout
  have hab := (sInteger_isCoprime_iff_no_common_contracted_prime K S n₁ n₂).mp hc
  have hu' : u = ⟨c.val * n₁.val, mul_ne_zero c.property n₁.property⟩ := Subtype.ext hu
  have hv' : v = ⟨c.val * n₂.val, mul_ne_zero c.property n₂.property⟩ := Subtype.ext hv
  rw [hu', hv', sIntegerSexticOriginalFullCorrelation_common_factor K S ζ hζ σ hS6
    c n₁ n₂ a b k hbezout]
  exact sIntegerSexticReducedFullCorrelation_eq K S ζ hζ σ hS6
    (sIntegerModulusContraction K S c.val)
    (sIntegerModulusContraction_ne_bot K S c.val c.property)
    (sIntegerSexticCommonFactor_exterior K S c)
    (sIntegerSexticCommonFactor_away_six K S hS6 c)
    n₁ n₂ a b k hbezout hab

/-- For arbitrary nonzero literal u,v in the actual PID O_S, choose the
common factor and residual Bezout data once, then factor every divisible
frequency c*k, including k=0. -/
theorem exists_sIntegerSexticPID_originalFull_factorization [IsPrincipalIdealRing R]
    (u v : N) :
    ∃ c n₁ n₂ : N, ∃ a b : R,
      u.val = c.val * n₁.val ∧ v.val = c.val * n₂.val ∧
        a * n₂.val - b * n₁.val = 1 ∧
        ∀ k : R,
          sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6 u v (c.val * k) =
            (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
              sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ *
              sIntegerSexticFiniteCorrelation K S ζ hζ σ
                (sIntegerModulusContraction K S c.val)
                (sIntegerModulusContraction_ne_bot K S c.val c.property)
                (sIntegerSexticCommonFactor_exterior K S c)
                (sIntegerSexticCommonFactor_away_six K S hS6 c)
                (Ideal.Quotient.mk _ n₁.val) (Ideal.Quotient.mk _ n₂.val) (Ideal.Quotient.mk _ k) := by
  obtain ⟨c, n₁, n₂, a, b, hu, hv, hbezout⟩ := exists_sIntegerSexticPID_common_factor K S u v
  refine ⟨c, n₁, n₂, a, b, hu, hv, hbezout, ?_⟩
  intro k
  exact sIntegerSexticOriginalFullCorrelation_factorization K S ζ hζ σ hS6
    u v c n₁ n₂ a b k hu hv hbezout
end HeckeGeneral.Characters
