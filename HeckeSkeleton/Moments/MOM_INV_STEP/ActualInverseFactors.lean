import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalInverseCalibration

/-!
# Actual exterior factors of the second expanded source

The two original inverse columns determine their common and residual
ideals by intersection and difference of their actual prime supports.
These ideals are exterior, squarefree and coprime by construction.
Consequently the second coefficient conversion has no factorization or
coprimality input. For a single original unramified live background, the
common scalar cancels exactly in the squared pair.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualInverseFactors

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open IdealMobiusMask FirstSourceDecomposition
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def productExterior (B : Finset (HeightOneSpectrum (𝓞 K)))
    (hB : ∀ p ∈ B, p ∉ S) : ExteriorIdeal K S :=
  ⟨⟨primeProduct B, mem_nonZeroDivisors_of_ne_zero (primeProduct_ne_bot B)⟩, by
    intro p hp
    obtain ⟨q, hq, hpq⟩ :=
      (p.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal)).mp hp
    have he : q = p := HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top (Ideal.dvd_iff_le.mp hpq))
    subst q
    exact hB p hq⟩

def common (x₁ x₂ : ExteriorIdeal K S) : ExteriorIdeal K S :=
  productExterior K S (primeSupport x₁.val ∩ primeSupport x₂.val) (by
    intro p hp
    exact x₁.property p ((mem_primeSupport x₁.val p).mp (Finset.mem_inter.mp hp).1))

def residual (x₁ x₂ : ExteriorIdeal K S) : ExteriorIdeal K S :=
  productExterior K S (primeSupport x₁.val \ primeSupport x₂.val) (by
    intro p hp
    exact x₁.property p ((mem_primeSupport x₁.val p).mp (Finset.mem_sdiff.mp hp).1))

@[simp] theorem common_val (x₁ x₂ : ExteriorIdeal K S) :
    (common K S x₁ x₂).val.val = pairCommon x₁.val x₂.val := rfl

@[simp] theorem residual_val (x₁ x₂ : ExteriorIdeal K S) :
    (residual K S x₁ x₂).val.val = pairResidual x₁.val x₂.val := rfl

theorem common_comm (x₁ x₂ : ExteriorIdeal K S) :
    common K S x₁ x₂ = common K S x₂ x₁ := by
  apply Subtype.ext
  apply Subtype.ext
  change primeProduct (primeSupport x₁.val ∩ primeSupport x₂.val) =
    primeProduct (primeSupport x₂.val ∩ primeSupport x₁.val)
  rw [Finset.inter_comm]

theorem common_squarefree (x₁ x₂ : ExteriorIdeal K S) :
    Squarefree (common K S x₁ x₂).val.val := squarefree_primeProduct _

theorem residual_squarefree (x₁ x₂ : ExteriorIdeal K S) :
    Squarefree (residual K S x₁ x₂).val.val := squarefree_primeProduct _

theorem common_residual_coprime (x₁ x₂ : ExteriorIdeal K S) :
    IsCoprime (common K S x₁ x₂).val.val (residual K S x₁ x₂).val.val := by
  apply primeProduct_coprime
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2

/-- The original source, with its original exterior-ideal subtype,
equals the product of the factors defined above. -/
theorem common_mul_residual (x₁ x₂ : ExteriorIdeal K S)
    (hx₁ : Squarefree x₁.val.val) :
    exteriorMul K S (common K S x₁ x₂) (residual K S x₁ x₂) = x₁ := by
  apply Subtype.ext
  apply Subtype.ext
  change primeProduct (primeSupport x₁.val ∩ primeSupport x₂.val) *
    primeProduct (primeSupport x₁.val \ primeSupport x₂.val) = x₁.val.val
  exact (primeProduct_split (primeSupport x₁.val) (primeSupport x₂.val)).symm.trans
    (primeProduct_support x₁.val hx₁)

theorem common_eq_gcd (x₁ x₂ : ExteriorIdeal K S)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val) :
    (common K S x₁ x₂).val.val = gcd x₁.val.val x₂.val.val :=
  pairCommon_eq_gcd x₁.val x₂.val hx₁ hx₂

variable (D : ThetaArithmeticData K S)

/-- The second coefficient cycle on the actual original source x₁.
Its common and residual ideals are computed, never supplied as data. -/
theorem actual_source_coefficient {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K S D Λ G) (ν : HeckeCharacter K)
    (x₁ x₂ : ExteriorIdeal K S) (hx₁ : Squarefree x₁.val.val) :
    (moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val *
        thetaGamma K S D (residual K S x₁ x₂) 5 =
      ((moebius (common K S x₁ x₂).val.val : ℂ) *
        heckeIdealCoefficient K ν (common K S x₁ x₂).val) *
      (CoefficientCycle.canonicalCoefficient K S D Λ (residual K S x₁ x₂) *
        heckeIdealCoefficient K (ν * G⁻¹) (residual K S x₁ x₂).val) := by
  have h := CanonicalInverseCalibration.second_source_coefficient K S D hcal ν
    (common K S x₁ x₂) (residual K S x₁ x₂)
    (common_residual_coprime K S x₁ x₂) (residual_squarefree K S x₁ x₂)
  rw [common_mul_residual K S x₁ x₂ hx₁] at h
  exact h

/-- In one genuine inverse squared norm the live background is the
same on both columns. Its common-factor coefficient cancels exactly;
the surviving columns have the same background νG⁻¹. -/
theorem actual_pair_coefficient {Λ G : HeckeCharacter K}
    (hcal : ThetaCalibrationInput K S D Λ G) (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p)
    (x₁ x₂ : ExteriorIdeal K S)
    (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val) :
    ((moebius x₁.val.val : ℂ) * heckeIdealCoefficient K ν x₁.val *
        thetaGamma K S D (residual K S x₁ x₂) 5) *
      conj ((moebius x₂.val.val : ℂ) * heckeIdealCoefficient K ν x₂.val *
        thetaGamma K S D (residual K S x₂ x₁) 5) =
      (CoefficientCycle.canonicalCoefficient K S D Λ (residual K S x₁ x₂) *
          heckeIdealCoefficient K (ν * G⁻¹) (residual K S x₁ x₂).val) *
        conj (CoefficientCycle.canonicalCoefficient K S D Λ (residual K S x₂ x₁) *
          heckeIdealCoefficient K (ν * G⁻¹) (residual K S x₂ x₁).val) := by
  rw [actual_source_coefficient K S D hcal ν x₁ x₂ hx₁,
    actual_source_coefficient K S D hcal ν x₂ x₁ hx₂,
    common_comm K S x₂ x₁, map_mul]
  let a := (moebius (common K S x₁ x₂).val.val : ℂ) *
    heckeIdealCoefficient K ν (common K S x₁ x₂).val
  have ha : a * conj a = 1 := by
    rw [Complex.mul_conj', CanonicalInverseCalibration.second_outer_scalar_norm K S ν hν
      (common K S x₁ x₂) (common_squarefree K S x₁ x₂)]
    norm_num
  calc
    _ = (a * conj a) *
      ((CoefficientCycle.canonicalCoefficient K S D Λ (residual K S x₁ x₂) *
          heckeIdealCoefficient K (ν * G⁻¹) (residual K S x₁ x₂).val) *
        conj (CoefficientCycle.canonicalCoefficient K S D Λ (residual K S x₂ x₁) *
          heckeIdealCoefficient K (ν * G⁻¹) (residual K S x₂ x₁).val)) := by
      dsimp only [a]
      ring
    _ = _ := by rw [ha, one_mul]

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualInverseFactors

end
