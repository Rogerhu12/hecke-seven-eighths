import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SIntegerFirstFourier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrbitalCorrelation

/-!
# The actual second finite transform, with the original mask divisors

The complete Gauss columns produced by the first transform are periodic
on each pair's own product modulus.  Their second Fourier coefficient is
the full nonprimitive correlation.  A divisor of the old avoidance mask
is coprime to each retained column modulus; its exact two character
phases are kept.  No inverse of a nonunit divisor is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open NumberField IsDedekindDomain

section Ring

variable {R : Type*} [CommRing R]

theorem completeResidueGauss_unit_dilate (T : NonzeroModulusTrace R) (a : R)
    [Fintype (Residue a)] (χ : MulChar (Residue a) ℂ)
    (u : (Residue a)ˣ) (h : Residue a) :
    completeResidueGauss T a χ ((u : Residue a) * h) =
      χ⁻¹ (u : Residue a) * completeResidueGauss T a χ h := by
  have he := gaussSum_mulShift_eq χ ((T.ψ a).mulShift h) u
  simpa only [gaussSum, completeResidueGauss, AddChar.mulShift_apply,
    mul_assoc, mul_left_comm] using he

theorem completeResidueGauss_scaled (T : NonzeroModulusTrace R)
    (a b m : R) (ha : a ≠ 0) (hb : b ≠ 0) (hm : m = a * b)
    [Fintype (Residue a)] [Fintype (Residue m)]
    (χ : MulChar (Residue a) ℂ) (h : Residue m) :
    fourierSum (T.ψ m) (scaledResidue a b m hm) χ h =
      completeResidueGauss T a χ
        (completeFrequencyReduction a m (hm ▸ dvd_mul_right a b) h) := by
  unfold fourierSum completeResidueGauss
  apply Finset.sum_congr rfl
  intro x _
  rw [T.scale a b m ha hb hm]

/-- The periodic second-transform function uses the pair's own full modulus. -/
def completeGaussPair (T : NonzeroModulusTrace R) (a b : R)
    [Fintype (Residue a)] [Fintype (Residue b)]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (x : Residue (a * b)) : ℂ :=
  completeResidueGauss T a χa
      (completeFrequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (completeResidueGauss T b χb
      (completeFrequencyReduction b (a * b) (dvd_mul_left b a) x))

theorem completeGaussPair_eq_fourierSum (T : NonzeroModulusTrace R)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (x : Residue (a * b)) :
    completeGaussPair T a b χa χb x =
      fourierSum (T.ψ (a * b)) (scaledResidue a b (a * b) rfl) χa x *
        star (fourierSum (T.ψ (a * b))
          (scaledResidue b a (a * b) (mul_comm a b)) χb x) := by
  rw [completeResidueGauss_scaled T a b (a * b) ha hb rfl,
    completeResidueGauss_scaled T b a (a * b) hb ha (mul_comm a b)]
  rfl

theorem completeGaussPair_unit_dilate (T : NonzeroModulusTrace R)
    (a b δ : R) (haδ : IsCoprime a δ) (hbδ : IsCoprime b δ)
    [Fintype (Residue a)] [Fintype (Residue b)]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (x : Residue (a * b)) :
    completeGaussPair T a b χa χb (Ideal.Quotient.mk _ δ * x) =
      (χa⁻¹ (Ideal.Quotient.mk _ δ) * star (χb⁻¹ (Ideal.Quotient.mk _ δ))) *
        completeGaussPair T a b χa χb x := by
  unfold completeGaussPair
  simp only [map_mul, completeFrequencyReduction_mk]
  rw [← residueUnit_coe a δ haδ, ← residueUnit_coe b δ hbδ,
    completeResidueGauss_unit_dilate, completeResidueGauss_unit_dilate, star_mul]
  ring

/-- Every coefficient, including the zero frequency, is the complete
correlation of the original two characters. -/
theorem completeGaussPair_divisor_fourier (T : NonzeroModulusTrace R)
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a * b ≠ 0)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (δ j : R) (haδ : IsCoprime a δ) (hbδ : IsCoprime b δ) :
    PeriodicFourier.divisorTransform (T.ψ (a * b)) (completeGaussPair T a b χa χb)
        (Ideal.Quotient.mk _ δ) (Ideal.Quotient.mk _ j) =
      (χa⁻¹ (Ideal.Quotient.mk _ δ) * star (χb⁻¹ (Ideal.Quotient.mk _ δ))) *
        ((Fintype.card (Residue (a * b)) : ℂ) * fullModulusCorrelation a b χa χb (-j)) := by
  rw [PeriodicFourier.divisorTransform_apply]
  calc
    _ = (χa⁻¹ (Ideal.Quotient.mk _ δ) * star (χb⁻¹ (Ideal.Quotient.mk _ δ))) *
        ∑ x : Residue (a * b), completeGaussPair T a b χa χb x *
          T.ψ (a * b) (Ideal.Quotient.mk _ j * x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [completeGaussPair_unit_dilate T a b δ haδ hbδ χa χb]
      ring
    _ = _ := by
      congr 1
      simp_rw [completeGaussPair_eq_fourierSum T a b ha hb χa χb]
      simpa only [fullModulusCorrelation, map_neg,
        PeriodicFourier.divisorTransform_apply, one_mul] using
        gauss_pair_fourier (T.ψ (a * b)) (T.primitive (a * b) hab)
          (scaledResidue a b (a * b) rfl)
          (scaledResidue b a (a * b) (mul_comm a b)) χa χb (Ideal.Quotient.mk _ j)

end Ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
local notation "OS" => S.integer K

/-- Direct specialization to the very Fourier coefficient in the genuine
masked orbital Poisson formula.  Quotient finiteness is proved arithmetically. -/
theorem actual_gauss_pair_divisor_transform (a b : OS) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar (OS ⧸ Ideal.span ({a} : Set OS)) ℂ)
    (χb : MulChar (OS ⧸ Ideal.span ({b} : Set OS)) ℂ)
    (δ j : OS) (haδ : IsCoprime a δ) (hbδ : IsCoprime b δ) :
    letI := finite_sIntegerPrincipalResidue K S a ha
    letI := finite_sIntegerPrincipalResidue K S b hb
    letI := finite_sIntegerPrincipalResidue K S (a * b) (mul_ne_zero ha hb)
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a} : Set OS))
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({b} : Set OS))
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a * b} : Set OS))
    sIntegerPeriodicDivisorFourier K S hS (a * b) (mul_ne_zero ha hb)
        (completeGaussPair (actualSIntegerTrace K S hS) a b χa χb) δ
        (Ideal.Quotient.mk _ j) =
      (χa⁻¹ (Ideal.Quotient.mk _ δ) * star (χb⁻¹ (Ideal.Quotient.mk _ δ))) *
        ((Fintype.card (OS ⧸ Ideal.span ({a * b} : Set OS)) : ℂ) *
          fullModulusCorrelation a b χa χb (-j)) := by
  letI := finite_sIntegerPrincipalResidue K S a ha
  letI := finite_sIntegerPrincipalResidue K S b hb
  letI := finite_sIntegerPrincipalResidue K S (a * b) (mul_ne_zero ha hb)
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({b} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({a * b} : Set OS))
  unfold sIntegerPeriodicDivisorFourier
  rw [← actualSIntegerTrace_psi K S hS (a * b) (mul_ne_zero ha hb)]
  exact completeGaussPair_divisor_fourier (actualSIntegerTrace K S hS)
    a b ha hb (mul_ne_zero ha hb) χa χb δ j haδ hbδ

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_gauss_pair_divisor_transform

