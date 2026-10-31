import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonGauss

/-!
# Normalization of the genuine active Gauss factor

The complete active Gauss sum is bounded on its actual squarefree
quotient. Identifying that quotient with the exact active radical then
connects its normalization to the proved common-support harmonic mass.
No aggregate phase or Gauss-mass hypothesis is introduced.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem actual_sInteger_active_divisor_gauss_norm_le_sqrt
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (δ h : A.R) :
    ‖actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ δ) *
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff (firstActiveGenerator C p m n)
        (firstActiveGenerator_generates C p m n).1
        (actualFirstActiveCharacter C p hp m n) h‖ ≤
      Real.sqrt (A.exteriorNorm (firstActiveIdeal p m n)) := by
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    (firstActiveGenerator C p m n) (firstActiveGenerator_generates C p m n).1
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {firstActiveGenerator C p m n})
  exact actual_active_divisor_gauss_norm_le_sqrt C
    (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff) p hp m n δ (Ideal.Quotient.mk _ h)

section Blocks

variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

def FirstCommonCharacterBlock.normalizedActiveGauss
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Z : ℝ) (δ h : A.R) : ℝ :=
  let R := firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity
  ‖actualFirstActiveCharacter C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity (Ideal.Quotient.mk _ δ) *
    actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
      (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity).1
      (actualFirstActiveCharacter C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity) h‖ *
    Z ^ ((firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
        (idealLogLength Z R.val) +
      firstAllowance (idealLogLength Z DE.2) (idealLogLength Z DE.1)
        (idealLogLength Z R.val)) / 2) /
    (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ))

theorem FirstCommonCharacterBlock.normalizedActiveGauss_le_weight
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Z : ℝ) (hZ : 1 < Z) (δ h : A.R) :
    b.normalizedActiveGauss C hDiff Z δ h ≤ firstCommonWeight Z DE.1 DE.2 := by
  rw [b.commonWeight_sqrt_formula Z hZ]
  unfold FirstCommonCharacterBlock.normalizedActiveGauss
  dsimp only
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (actual_sInteger_active_divisor_gauss_norm_le_sqrt C hDiff b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity δ h)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem FirstCommonCharacterBlock.normalizedActiveGauss_le_radical
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (Z : ℝ) (hZ : 1 < Z) (δ h : A.R) :
    b.normalizedActiveGauss C hDiff Z δ h ≤
      1 / (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ) := by
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  exact (b.normalizedActiveGauss_le_weight C hDiff Z hZ δ h).trans
    (firstCommonWeight_le_radical Z hZ DE.1 DE.2 hD hE b.common_support_eq)

end Blocks

theorem actual_first_normalized_gauss_mass
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 < Z →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 → ∀ labels : Finset (Label K),
      (∀ v ∈ labels, Valid s v) →
      (∀ v ∈ labels, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
    ∀ {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior},
    ∀ blocks : ∀ v : labels, FirstCommonCharacterBlock fullI fullJ v.val.1,
    ∀ δ h : labels → A.R,
      (∑ v : labels, (blocks v).normalizedActiveGauss C hDiff Z (δ v) (h v)) ≤
        Cbound * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  obtain ⟨Cbound, hC, hmass⟩ := actual_first_common_mass (K := K) B ε hB hε
  refine ⟨Cbound, hC, ?_⟩
  intro Z hZ s hs hs0 labels hvalid hnorm α β fullI fullJ blocks δ h
  calc
    _ ≤ ∑ v : labels, firstCommonWeight Z v.val.1.1 v.val.1.2 :=
      Finset.sum_le_sum (fun v _ =>
        (blocks v).normalizedActiveGauss_le_weight C hDiff Z hZ (δ v) (h v))
    _ = ∑ v ∈ labels, firstCommonWeight Z v.1.1 v.1.2 := Finset.sum_coe_sort _ _
    _ ≤ _ := hmass Z hZ s hs hs0 labels hvalid hnorm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.normalizedActiveGauss_le_weight
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_normalized_gauss_mass

