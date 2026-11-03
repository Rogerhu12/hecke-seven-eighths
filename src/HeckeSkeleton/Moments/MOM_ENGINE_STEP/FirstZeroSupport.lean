import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedZeroGauss
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource

/-!
# The actual first zero terms are supported on powerful products

The zero-frequency arithmetic statement is applied to the genuine
residual columns with their arbitrary generated moduli. The constant
subtraction at the primal zero is treated too: its residue value is
recovered from the complete zero-dilation Fourier sum. Thus both
additive zero terms vanish off the powerful product diagonal.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]

section Gate

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

theorem ParentPeriodicPair.gated_divisorFourier (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (δ : OS) (h : OS ⧸ Ideal.span {p.modulus}) :
    sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff
        (p.gated P).modulus (p.gated P).modulus_ne_zero (p.gated P).residue δ h =
      if P then sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff
        p.modulus p.modulus_ne_zero p.residue δ h else 0 := by
  by_cases hP : P
  · simp only [ParentPeriodicPair.gated, if_pos hP]
  · simp only [ParentPeriodicPair.gated, if_neg hP, sIntegerPeriodicDivisorFourier,
      PeriodicFourier.divisorTransform, PeriodicFourier.fourier, PeriodicFourier.dilate,
      zero_mul, Finset.sum_const_zero]

theorem ParentPeriodicPair.divisorFourier_zero_dilation (p : ParentPeriodicPair K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0) :
    sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K))) hDiff p.modulus p.modulus_ne_zero
      p.residue 0 0 = (Nat.card (OS ⧸ Ideal.span {p.modulus}) : ℂ) * p.residue 0 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) p.modulus p.modulus_ne_zero
  letI := Fintype.ofFinite (OS ⧸ Ideal.span {p.modulus})
  simp [sIntegerPeriodicDivisorFourier, PeriodicFourier.divisorTransform,
    PeriodicFourier.fourier, PeriodicFourier.dilate, Nat.card_eq_fintype_card]

end Gate

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem FirstCommonCharacterBlock.zeroFourier_nonzero_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (δ : A.R)
    (hzero : sIntegerPeriodicDivisorFourier K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (b.pair hΓ C profiles i j).modulus (b.pair hΓ C profiles i j).modulus_ne_zero
      (b.pair hΓ C profiles i j).residue δ 0 ≠ 0) :
    Powerful ((fullI i).val * (fullJ j).val) := by
  unfold FirstCommonCharacterBlock.pair at hzero
  by_cases hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val
  · simp only [ParentPeriodicPair.gated, if_pos hcop] at hzero
    have hgen := b.generator_coprime C left right i hi j hj hcop
    obtain ⟨hpI, hpJ⟩ := originalTriple_zero_powerful_residuals hΓ C hDiff
      (b.leftResidual i) (b.rightResidual j) (b.leftGenerator i) (b.rightGenerator j)
      (b.left_generates i) (b.right_generates j)
      (actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity)
      (profiles i j) hgen.1 hgen.2 δ hzero
    have hcommon := actual_common_product_powerful b.primes
      b.leftMultiplicity b.rightMultiplicity b.left_positive b.right_positive
    have hproduct := powerful_mul
      (mul_ne_zero (primePowerProduct b.primes b.leftMultiplicity).property.1
        (primePowerProduct b.primes b.rightMultiplicity).property.1)
      (mul_ne_zero (b.leftResidual i).property.1 (b.rightResidual j).property.1)
      hcommon (powerful_mul (b.leftResidual i).property.1 (b.rightResidual j).property.1 hpI hpJ)
    rw [b.left_reconstruct left i hi, b.right_reconstruct right j hj]
    convert hproduct using 1 <;> ring
  · simp only [ParentPeriodicPair.gated, if_neg hcop, sIntegerPeriodicDivisorFourier,
      PeriodicFourier.divisorTransform, PeriodicFourier.fourier, PeriodicFourier.dilate,
      zero_mul, Finset.sum_const_zero, ne_self_iff_false] at hzero

theorem FirstCommonCharacterBlock.zeroFourier_eq_zero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (δ : A.R) (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) :
    sIntegerPeriodicDivisorFourier K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (b.pair hΓ C profiles i j).modulus (b.pair hΓ C profiles i j).modulus_ne_zero
      (b.pair hΓ C profiles i j).residue δ 0 = 0 := by
  by_contra hzero
  exact hbad (b.zeroFourier_nonzero_powerful hΓ C hDiff left right profiles i hi j hj δ hzero)

theorem FirstCommonCharacterBlock.residue_zero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) :
    (b.pair hΓ C profiles i j).residue 0 = 0 := by
  let p := b.pair hΓ C profiles i j
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) p.modulus p.modulus_ne_zero
  have hc : (Nat.card (A.R ⧸ Ideal.span {p.modulus}) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A.R ⧸ Ideal.span {p.modulus})).ne'
  have hz := b.zeroFourier_eq_zero_of_not_powerful hΓ C hDiff left right profiles
    i hi j hj 0 hbad
  rw [p.divisorFourier_zero_dilation hDiff] at hz
  exact (mul_eq_zero.mp hz).resolve_left hc

variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

theorem ParentPeriodicPair.gated_transformedZero
    (p : ParentPeriodicPair K A.Sf Γ) (P : Prop) [Decidable P]
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) :
    (p.gated P).transformedZero μv hDiff finiteTest radius D =
      if P then p.transformedZero μv hDiff finiteTest radius D else 0 := by
  by_cases hP : P
  · rw [p.gated_of_true P hP, if_pos hP]
  · unfold ParentPeriodicPair.transformedZero
    simp only [ParentPeriodicPair.gated, if_neg hP, sIntegerPeriodicDivisorFourier,
      PeriodicFourier.divisorTransform, PeriodicFourier.fourier, PeriodicFourier.dilate,
      zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]

theorem FirstCommonCharacterBlock.transformedZero_eq_zero_of_not_coprime
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hcop : ¬ IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    (b.pair hΓ C profiles i j).transformedZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.pair
  rw [ParentPeriodicPair.gated_transformedZero (A := A), if_neg hcop]

theorem FirstCommonCharacterBlock.transformedZero_eq_zero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) :
    (b.pair hΓ C profiles i j).transformedZero μv hDiff finiteTest radius D = 0 := by
  unfold ParentPeriodicPair.transformedZero
  rw [b.zeroFourier_eq_zero_of_not_powerful hΓ C hDiff left right profiles i hi j hj
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val hbad,
    b.residue_zero_of_not_powerful hΓ C hDiff left right profiles i hi j hj hbad]
  simp only [zero_mul, mul_zero, sub_zero]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.zeroFourier_nonzero_powerful
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.transformedZero_eq_zero_of_not_powerful

