import HeckeGeneral.Analysis.SIntegerMaskedTruncation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentSource

/-!
# The genuine orbital transform of a whole polynomial

The finite periodic input is the squared norm of the *whole* coefficient
polynomial.  In particular, a centered difference is retained inside that
polynomial.  Both transforms in the engine use this same statement.

The analytic identity and quantitative truncation are specialized from the
proved general-number-field orbital Poisson formula.  They use all orbits
of the original finite-index S-unit subgroup, the actual additive zero
terms, the actual Haar covolume and the actual discriminant factor.
Neither a radial Poisson datum nor a convergence hypothesis is assumed.

The same cutoff is selected for every divisor.  The approximation is made
on the genuine periodic sum before any coprime extension or absolute
estimate of its Fourier coefficients.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters MeasureTheory
  HeckeGeneral.Analysis
open scoped Classical BigOperators nonZeroDivisors

/-- The complete squared polynomial, before any expansion or absolute value. -/
def wholeResidueEnergy {ι R : Type*} (columns : Finset ι) (c : ι → ℂ)
    (G : ι → R → ℂ) (x : R) : ℂ :=
  wholePolynomial columns c G x * star (wholePolynomial columns c G x)

theorem wholeResidueEnergy_re {ι R : Type*} (columns : Finset ι) (c : ι → ℂ)
    (G : ι → R → ℂ) (x : R) :
    (wholeResidueEnergy columns c G x).re = ‖wholePolynomial columns c G x‖ ^ 2 := by
  simp [wholeResidueEnergy, Complex.star_def, Complex.mul_conj', pow_two]

theorem wholeResidueEnergy_re_nonneg {ι R : Type*}
    (columns : Finset ι) (c : ι → ℂ) (G : ι → R → ℂ) (x : R) :
    0 ≤ (wholeResidueEnergy columns c G x).re := by
  rw [wholeResidueEnergy_re]
  exact sq_nonneg _

/-- Pointwise equality of every original column preserves the whole norm. -/
theorem wholeResidueEnergy_congr {ι R : Type*}
    (columns : Finset ι) (c : ι → ℂ) (G : ι → R → ℂ) (x y : R)
    (he : ∀ i ∈ columns, G i x = G i y) :
    wholeResidueEnergy columns c G x = wholeResidueEnergy columns c G y := by
  have hp : wholePolynomial columns c G x = wholePolynomial columns c G y := by
    unfold wholePolynomial
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi]
  simp only [wholeResidueEnergy, hp]

/-- Exact sesquilinear expansion; both coefficient arrays are the original one. -/
theorem wholeResidueEnergy_expand {ι R : Type*} (columns : Finset ι) (c : ι → ℂ)
    (G : ι → R → ℂ) (x : R) :
    wholeResidueEnergy columns c G x =
      ∑ i ∈ columns, ∑ j ∈ columns, c i * star (c j) * (G i x * star (G j x)) := by
  unfold wholeResidueEnergy wholePolynomial
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [star_mul]
  ring

/-- Taking the finite Fourier transform keeps the full coefficient array. -/
theorem wholeResidueEnergy_fourier {ι R H : Type*} [Fintype R]
    (columns : Finset ι) (c : ι → ℂ) (G : ι → R → ℂ) (e : H → R → ℂ) (h : H) :
    (∑ x : R, wholeResidueEnergy columns c G x * e h x) =
      ∑ i ∈ columns, ∑ j ∈ columns, c i * star (c j) *
        (∑ x : R, G i x * star (G j x) * e h x) := by
  simp_rw [wholeResidueEnergy_expand]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro x hx
  ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "T" => sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

variable (modulus : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)

/-- The actual whole squared polynomial, with its original unit invariance and
Schwartz profile, as the provider's concrete periodic input. -/
def wholePeriodicPair {ι : Type*} (hmodulus : modulus ≠ 0)
    (columns : Finset ι) (c : ι → ℂ)
    (G : ι → (OS ⧸ Ideal.span ({modulus} : Set OS)) → ℂ)
    (hinv : ∀ i ∈ columns, ∀ u : Γ, ∀ a : OS,
      G i (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
          G i (Ideal.Quotient.mk _ a))
    (φ : SchwartzMap V ℂ) : ParentPeriodicPair K S Γ where
  modulus := modulus
  modulus_ne_zero := hmodulus
  residue := wholeResidueEnergy columns c G
  invariant u a := wholeResidueEnergy_congr columns c G
    (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS))
      (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a))
    (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS)) a)
    (fun i hi => hinv i hi u a)
  profile := φ

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Either engine transform, on the actual whole nonnegative row norm.
`firstTransform` is the proved provider's full Möbius formula, including both
additive zero terms, the Haar covolume, and the discriminant factor. -/
theorem whole_masked_orbital_poisson {ι : Type*}
    (hmodulus : modulus ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (columns : Finset ι) (c : ι → ℂ)
    (G : ι → (OS ⧸ Ideal.span ({modulus} : Set OS)) → ℂ)
    (hinv : ∀ i ∈ columns, ∀ u : Γ, ∀ a : OS,
      G i (Ideal.Quotient.mk _
        (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
          G i (Ideal.Quotient.mk _ a))
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) :
    (wholePeriodicPair K S Γ modulus hmodulus columns c G hinv φ).maskedSeries
        (sIntegerFiniteTestFunction K S h) r M =
      (wholePeriodicPair K S Γ modulus hmodulus columns c G hinv φ).firstTransform
        μv hS h M r :=
  ParentPeriodicPair.maskedSeries_eq_firstTransform ν μv μ
    (wholePeriodicPair K S Γ modulus hmodulus columns c G hinv φ) hS h hlc hcs M r

include ν μ in
/-- A common dual cutoff for the entire squared polynomial, with actual
finite coefficient mass and a fixed Schwartz order chosen first. -/
theorem exists_whole_masked_orbital_truncation
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ M : Finset (HeightOneSpectrum OS),
      ∀ modulus : OS, ∀ hmodulus : modulus ≠ 0,
      ∀ (ι : Type) (columns : Finset ι) (c : ι → ℂ)
        (G : ι → (OS ⧸ Ideal.span ({modulus} : Set OS)) → ℂ),
      ∀ hinv : ∀ i ∈ columns, ∀ u : Γ, ∀ a : OS,
        G i (Ideal.Quotient.mk _
          (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
            G i (Ideal.Quotient.mk _ a),
      ∀ r : {r : ℝ // 0 < r}, ∀ φ : SchwartzMap V ℂ, ∀ X : ℝ, 1 ≤ X →
        let f := wholeResidueEnergy columns c G
        let hf := fun (u : Γ) (a : OS) =>
          wholeResidueEnergy_congr columns c G
            (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS))
              (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a))
            (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS)) a)
            (fun i hi => hinv i hi u a)
        ‖sIntegerWeightedOrbitalSeries K S Γ φ (sIntegerFiniteTestFunction K S h) r
            (fun q => sIntegerOrbitAvoidanceMask K _ Γ M q *
              sIntegerPeriodicOrbitWeight K (S : Set (HeightOneSpectrum (𝓞 K))) Γ modulus f hf q) -
          sIntegerMaskedPeriodicApproximation K S Γ μv modulus hmodulus hS
            φ h M f hf r X‖ ≤
          C * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ * X ^ (1 - decay) *
            sIntegerMaskedTruncationMass K S modulus hmodulus M f r := by
  obtain ⟨seminorms, C, hC, hbound⟩ := exists_sIntegerMaskedPeriodicApproximation_bound
    K S Γ ν μv μ hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro M modulus hmodulus ι columns c G hinv r φ X hX
  exact (hbound M modulus hmodulus (wholeResidueEnergy columns c G)
    (fun u a => wholeResidueEnergy_congr columns c G
        (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS))
          (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a))
        (Ideal.Quotient.mk (Ideal.span ({modulus} : Set OS)) a)
        (fun i hi => hinv i hi u a))
    r φ X hX).2

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.whole_masked_orbital_poisson
#print axioms HeckeSkeleton.Moments.EngineStep.exists_whole_masked_orbital_truncation

