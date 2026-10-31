import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization

/-!
# Uniform mass of the actually normalized second sources

The normalization scales belong to the original source coefficients.
The row-radius window has no column exponent.  The fixed harmonic
counting constant precedes every source, generator, frequency, profile
normalization scale, divisor, and pool density.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]

/-- No aggregate second-source mass estimate is supplied.  The actual
pointwise correlation and Poisson factors reduce to the inverse common
radical, whose finite ideal sum is bounded internally. -/
theorem actual_second_source_common_mass
    (C : A.GeneralArithmeticContext σ η hS)
    (size ε : ℝ) (hsize : 0 ≤ size) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 < Z →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 → ∀ labels : Finset (Label K),
      (∀ v ∈ labels, Valid s v) →
      (∀ v ∈ labels, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ size ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ size) →
    ∀ {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior},
    ∀ blocks : ∀ v : labels, FirstCommonCharacterBlock fullI fullJ v.val.1,
    ∀ a d h : labels → A.R,
    ∀ ha : ∀ v : labels, A.Generates
      (primePowerProduct (blocks v).primes (blocks v).leftMultiplicity) (a v),
    ∀ hd : ∀ v : labels, A.Generates
      (primePowerProduct (blocks v).primes (blocks v).rightMultiplicity) (d v),
    ∀ a₀ q wo w B krow g ell density densityBound : ℝ,
      0 ≤ densityBound → density ≤ densityBound * Z ^ (-ell) →
    ∀ r : {r : ℝ // 0 < r}, ∀ divisors : labels → Finset (HeightOneSpectrum A.R),
      (∀ v : labels, Z ^ (-krow - g) ≤
        r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (divisors v))).val) →
    ∀ NL NR : labels → ℝ,
      (∀ v : labels, Z ^ a₀ ≤ Real.sqrt (NL v) * Real.sqrt (NR v)) →
      (∑ v : labels,
        (blocks v).secondSourceWeight C Z a₀ q wo w B krow g ell density
          (NL v) (NR v) r (divisors v) (a v) (d v) (ha v) (hd v) (h v)) ≤
        (Cbound * densityBound * orbitalFieldFactor K) *
          Z ^ ((a₀ + q + wo + w + B) + ε) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨Cbound, hC, hmass⟩ := common_radical_harmonic_mass (K := K) size ε hsize hε
  refine ⟨Cbound, hC, ?_⟩
  intro Z hZ s hs hs0 labels hvalid hnorm α β fullI fullJ blocks a d h ha hd
    a₀ q wo w B krow g ell density densityBound hDensityBound hdensity r divisors hrow
    NL NR hcentral
  let F : ℝ := densityBound * orbitalFieldFactor K * Z ^ (a₀ + q + wo + w + B)
  have hF : 0 ≤ F := mul_nonneg
    (mul_nonneg hDensityBound (orbitalFieldFactor_nonneg K))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  calc
    _ ≤ ∑ v : labels, F *
        (1 / (Ideal.absNorm (commonRadical v.val.1.1 v.val.1.2) : ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      apply ((blocks v).secondSourceWeight_le C Z hZ a₀ q wo w B krow g ell
        density densityBound (NL v) (NR v) hDensityBound hdensity
        r (divisors v) (hrow v) (hcentral v)
        (a v) (d v) (ha v) (hd v) (h v)).trans_eq
      dsimp only [F]
      ring
    _ = F * ∑ v : labels,
        1 / (Ideal.absNorm (commonRadical v.val.1.1 v.val.1.2) : ℝ) := by
      rw [Finset.mul_sum]
    _ = F * ∑ v ∈ labels,
        1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ) := by
      rw [Finset.sum_coe_sort]
    _ ≤ F * (Cbound * Z ^ ε / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass Z hZ.le s hs hs0 labels hvalid hnorm) hF
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans hZ)]
      dsimp only [F]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_source_common_mass

