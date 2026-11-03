import SIntegerSexticDenominatorMultiplicativity
import SIntegerSexticCoprimeColumns
import SIntegerSexticRIdentification

/-! SOURCE ONLY, UNRUN. Pointwise character-weight extraction on the
genuine full fibre. Frequency k may be zero. Only character values of
the coprime residual columns are cancelled; frequency zero masks remain.
The common ideal may share prime factors with either residual column. -/
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

private theorem symbol_mul_numerator (x y : S.integer K) (n : N) :
    χ (x * y) n = χ x n * χ y n := by
  unfold sIntegerSexticSymbol
  exact sIntegerSexticIdealEvaluation_mul K S ζ hζ σ _ _ _ _ x y

private theorem correlationColumn_exterior (n : N)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S n.val) : p ∉ S := by
  intro hpS
  have hc := sIntegerModulusContraction_coprime K S n.val n.property p hpS
  rw [sup_eq_right.mpr (Ideal.dvd_iff_le.mp hp)] at hc
  exact p.isPrime.ne_top hc

/-- Actual evaluation with denominator C*I_n, including shared-prime
multiplicities; every admissibility proof is constructed. -/
def sIntegerSexticCommonColumnEvaluation
    (C : Ideal (𝓞 K)) (hC : C ≠ 0)
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (n : N) (x : S.integer K) : ℂ :=
  let hS := fun (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ C ∨ p.asIdeal ∣ sIntegerModulusContraction K S n.val) =>
      hp.elim (hCS p) (correlationColumn_exterior K S n p)
  sIntegerSexticIdealEvaluation K S ζ hζ σ
    (C * sIntegerModulusContraction K S n.val)
    (mul_ne_zero hC (sIntegerModulusContraction_ne_bot K S n.val n.property))
    (fun p hp => hS p (p.prime.dvd_mul.mp hp))
    (fun p hp h => hS p (p.prime.dvd_mul.mp hp) (hS6 h)) x

theorem sIntegerSexticCommonColumnEvaluation_eq
    (C : Ideal (𝓞 K)) (hC : C ≠ 0)
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (hC6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → (6 : 𝓞 K) ∉ p.asIdeal)
    (n : N) (x : S.integer K) :
    sIntegerSexticCommonColumnEvaluation K S ζ hζ σ hS6 C hC hCS n x =
      sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 x * χ x n := by
  let hS := fun (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ C ∨ p.asIdeal ∣ sIntegerModulusContraction K S n.val) =>
      hp.elim (hCS p) (correlationColumn_exterior K S n p)
  let h6 := fun p hp h => hS p hp (hS6 h)
  unfold sIntegerSexticCommonColumnEvaluation sIntegerSexticSymbol
  exact sIntegerSexticIdealEvaluation_mul_denominator K S ζ hζ σ C
    (sIntegerModulusContraction K S n.val) hC
    (sIntegerModulusContraction_ne_bot K S n.val n.property) hS h6 x

/-- Extraction uses a residue congruence, and remains valid when k or x
has a prime factor in common with the denominator. -/
theorem sIntegerSexticSymbol_extract_coprime_column
    (n₁ n₂ : N) (k x : S.integer K)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S n₁.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S n₂.val))
    (hx : n₂.val * x - k ∈ Ideal.span ({n₁.val} : Set (S.integer K))) :
    χ x n₁ = χ k n₁ * starRingEnd ℂ (χ n₂.val n₁) := by
  have hn := norm_sIntegerSexticSymbol_eq_one_of_no_common_prime
    K S ζ hζ σ hS6 n₂ n₁ hab
  have hc : χ n₂.val n₁ * starRingEnd ℂ (χ n₂.val n₁) = 1 := by
    rw [Complex.mul_conj', hn]
    norm_num
  have he : χ n₂.val n₁ * χ x n₁ = χ k n₁ := by
    rw [← symbol_mul_numerator]
    exact sIntegerSexticSymbol_periodic K S ζ hζ σ hS6 _ _ n₁ hx
  calc
    χ x n₁ = χ x n₁ * (χ n₂.val n₁ * starRingEnd ℂ (χ n₂.val n₁)) := by
      rw [hc, mul_one]
    _ = (χ n₂.val n₁ * χ x n₁) * starRingEnd ℂ (χ n₂.val n₁) := by ring
    _ = _ := by rw [he]

/-- This pointwise identity is proved before any quotient-fibre transport
or summation. EC is the actual ideal evaluation, not an arbitrary weight. -/
theorem sIntegerSexticCorrelation_weight_extraction
    (C : Ideal (𝓞 K)) (hC : C ≠ 0)
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (hC6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → (6 : 𝓞 K) ∉ p.asIdeal)
    (n₁ n₂ : N) (k x y : S.integer K)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S n₁.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S n₂.val))
    (hx : n₂.val * x - k ∈ Ideal.span ({n₁.val} : Set (S.integer K)))
    (hy : n₁.val * y - (-k) ∈ Ideal.span ({n₂.val} : Set (S.integer K))) :
    (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 x * χ x n₁) *
        starRingEnd ℂ (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 y * χ y n₂) =
      (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ *
        (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 x *
          starRingEnd ℂ (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 y)) := by
  have hxv := sIntegerSexticSymbol_extract_coprime_column
    K S ζ hζ σ hS6 n₁ n₂ k x hab hx
  have hyv := sIntegerSexticSymbol_extract_coprime_column
    K S ζ hζ σ hS6 n₂ n₁ (-k) y (fun p hp => hab p ⟨hp.2, hp.1⟩) hy
  rw [← sIntegerSexticRCandidate_eq_RCorrection K S ζ hζ σ hS6 n₁ n₂ hab]
  unfold sIntegerSexticRCandidate
  change _ = _ * (χ n₁.val n₂ * starRingEnd ℂ (χ n₂.val n₁)) * _
  rw [hxv, hyv]
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The same weight identity for the actual unfactored product-denominator
evaluations. This is the pointwise input to the genuine full-fibre sum. -/
theorem sIntegerSexticCorrelation_product_denominator_weight
    (C : Ideal (𝓞 K)) (hC : C ≠ 0)
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (hC6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → (6 : 𝓞 K) ∉ p.asIdeal)
    (n₁ n₂ : N) (k x y : S.integer K)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S n₁.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S n₂.val))
    (hx : n₂.val * x - k ∈ Ideal.span ({n₁.val} : Set (S.integer K)))
    (hy : n₁.val * y - (-k) ∈ Ideal.span ({n₂.val} : Set (S.integer K))) :
    sIntegerSexticCommonColumnEvaluation K S ζ hζ σ hS6 C hC hCS n₁ x *
        starRingEnd ℂ (sIntegerSexticCommonColumnEvaluation K S ζ hζ σ hS6 C hC hCS n₂ y) =
      (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ *
        (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 x *
          starRingEnd ℂ (sIntegerSexticIdealEvaluation K S ζ hζ σ C hC hCS hC6 y)) := by
  rw [sIntegerSexticCommonColumnEvaluation_eq K S ζ hζ σ hS6 C hC hCS hC6 n₁ x,
    sIntegerSexticCommonColumnEvaluation_eq K S ζ hζ σ hS6 C hC hCS hC6 n₂ y]
  exact sIntegerSexticCorrelation_weight_extraction K S ζ hζ σ hS6
    C hC hCS hC6 n₁ n₂ k x y hab hx hy
end HeckeGeneral.Characters
