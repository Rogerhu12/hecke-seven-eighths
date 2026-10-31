import SIntegerSexticReciprocity
import HeckeGeneral.Characters.SIntegerSexticCorrelationCovariance
/-! SOURCE ONLY, UNRUN. The literal R candidate agrees with the actual
ALL-S reciprocity correction on the exterior-coprime locus. Its period is
restricted to pairs whose two endpoints remain on that locus. The unit
correction itself has an unrestricted active-column period. No full
correlation identity or congruence-sum identity is asserted. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "N" => NonzeroRingElements (S.integer K)
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6

/-- The actual unit-valued ray extension of R, rather than the literal
symbol product's zero extension. -/
def sIntegerSexticRCorrection (a b : N) : ℂ :=
  σ (((sIntegerSexticSPlaceCorrection K S ζ hζ
    (nonzeroSIntegerFieldUnit K S a) (nonzeroSIntegerFieldUnit K S b))⁻¹).val : K)

/-- The correction has norm one even on the common-prime zero locus. -/
theorem norm_sIntegerSexticRCorrection (a b : N) :
    ‖sIntegerSexticRCorrection K S ζ hζ σ a b‖ = 1 := by
  let r := (sIntegerSexticSPlaceCorrection K S ζ hζ
    (nonzeroSIntegerFieldUnit K S a) (nonzeroSIntegerFieldUnit K S b))⁻¹
  have hr : (r.val : Kˣ) ^ 6 = 1 := r.property
  have hK : (r.val : K) ^ 6 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : Kˣ => (u : K)) hr
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by norm_num)
  change σ (r.val : K) ^ 6 = 1
  rw [← map_pow, hK, map_one]

theorem norm_sIntegerSexticSymbol_le_one (a : S.integer K) (b : N) :
    ‖χ a b‖ ≤ 1 := by
  unfold sIntegerSexticSymbol
  exact norm_sIntegerSexticIdealEvaluation_le_one K S ζ hζ σ _ _ _ _ a

/-- Neither shared-prime zeros nor the unrestricted correction enlarge the
literal raw factor. The negative second numerator remains present. -/
theorem norm_sIntegerSexticRawCoefficient_mul_RCorrection_le_one (a b k : N) :
    ‖sIntegerSexticRawCoefficient K S ζ hζ σ hS6 a b k *
      sIntegerSexticRCorrection K S ζ hζ σ a b‖ ≤ 1 := by
  rw [norm_mul, norm_sIntegerSexticRCorrection, mul_one]
  change ‖χ k.val a * starRingEnd ℂ (χ (-k.val) b)‖ ≤ 1
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_one₀ (norm_sIntegerSexticSymbol_le_one K S ζ hζ σ hS6 k.val a)
    (norm_nonneg _) (norm_sIntegerSexticSymbol_le_one K S ζ hζ σ hS6 (-k.val) b)

theorem norm_sIntegerSexticSymbol_eq_one_of_no_common_prime (a b : N)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S b.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S a.val)) :
    ‖χ a.val b‖ = 1 := by
  unfold sIntegerSexticSymbol
  apply norm_sIntegerSexticIdealEvaluation_eq_one
  intro p hp ha
  exact hab p ⟨hp,
    (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p _ a.val).mp ha⟩

/-- This is the manuscript's R on genuine coprime residual columns.
The conjugate cancellation uses the actual character norm theorem. -/
theorem sIntegerSexticRCandidate_eq_RCorrection (a b : N)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S b.val)) :
    sIntegerSexticRCandidate K S ζ hζ σ hS6 a b =
      sIntegerSexticRCorrection K S ζ hζ σ a b := by
  have hn := norm_sIntegerSexticSymbol_eq_one_of_no_common_prime
    K S ζ hζ σ hS6 b a hab
  have hc : χ b.val a * starRingEnd ℂ (χ b.val a) = 1 := by
    change χ b.val a * starRingEnd ℂ (χ b.val a) = 1
    rw [Complex.mul_conj', hn]
    norm_num
  unfold sIntegerSexticRCandidate sIntegerSexticRCorrection
  rw [sIntegerSexticSymbol_reciprocity K S ζ hζ σ hS6 a b, mul_assoc, hc, mul_one]

theorem sIntegerSexticRCorrection_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (n₁ m₁ n₂ m₂ : N) (t₁ t₂ : 𝓞 K)
    (ht₁ : t₁ ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (ht₂ : t₂ ∈ sIntegerSexticSPlaceModulus K S ζ hζ)
    (he₁ : n₁.val - m₁.val = algebraMap (𝓞 K) (S.integer K) t₁)
    (he₂ : n₂.val - m₂.val = algebraMap (𝓞 K) (S.integer K) t₂)
    (hm₁ : (sLocalNonzeroIntegerDiagonal K S m₁).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hm₂ : (sLocalNonzeroIntegerDiagonal K S m₂).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ =
      sIntegerSexticRCorrection K S ζ hζ σ m₁ m₂ := by
  have h := (sIntegerSexticSPlaceCorrection_periodic K S ζ hζ Γ
    n₁ m₁ n₂ m₂ t₁ t₂ ht₁ ht₂ he₁ he₂ hm₁ hm₂).2
  exact congrArg (fun x => σ (x.val : K)) h

/-- The raw coefficient keeps its literal -k and every shared-prime zero.
Only the R factor is identified here; no period of the raw factor follows
from the S-place modulus alone. -/
theorem sIntegerSexticRawCoefficient_mul_RCandidate (a b k : N)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S b.val)) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6 a b k *
        sIntegerSexticRCandidate K S ζ hζ σ hS6 a b =
      (χ k.val a * starRingEnd ℂ (χ (-k.val) b)) *
        sIntegerSexticRCorrection K S ζ hζ σ a b := by
  rw [sIntegerSexticRCandidate_eq_RCorrection K S ζ hζ σ hS6 a b hab]
  rfl
end HeckeGeneral.Characters
