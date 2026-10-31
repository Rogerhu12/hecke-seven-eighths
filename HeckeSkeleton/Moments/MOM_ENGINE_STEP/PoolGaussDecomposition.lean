import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstGaussPool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifierResidualSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondGeneratorSource

/-!
# The outputs of the one pool are genuine residual Gauss sources

Each error is disintegrated over the original chosen prime and the
literal valuation-filtered column set. The residual ideal and its
allowed generator are constructed from that valuation, before the row
and Fourier parameter. The complex reciprocal column phase is kept in
the whole coefficient. The row phase disappears only after taking the
squared norm of the complete polynomial.

The result is an exact identity, with the local factors at 1, 6 and 7
still explicit. There is no second use of the amplifier on these errors.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open MaskedQuotientCRT HeckeGeneral.Arithmetic HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

namespace FirstGaussPoolData

def valuationColumns (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) : Finset ι :=
  d.columns.filter (fun i => primeExponent p (d.ideal i) = n)

def residualPresentation (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (i : d.valuationColumns p n) :
    AmplifierResidualPresentation C p n (d.ideal i.val) :=
  amplifierResidualPresentation C p n (d.ideal i.val) (Finset.mem_filter.mp i.property).2

def errorRows (d : FirstGaussPoolData C P ι) (p : ExteriorPrime A) : Finset A.R :=
  d.rows.filter (fun h => actualPrimeEligible d.frozen (d.rowIdeal h) p)

/-- This is the exact coefficient of the residual *unnormalized* Gauss
sum. The norm quotient is an actual ideal norm, not a size estimate. -/
def residualCoefficient (d : FirstGaussPoolData C P ι) (p : ExteriorPrime A)
    (n : ℕ) (c : ι → ℂ) (i : d.valuationColumns p n) : ℂ :=
  d.adjustedCoefficient c i.val * (d.residualPresentation p n i).columnPhase /
    (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ)

theorem residualCoefficient_eq (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (i : d.valuationColumns p n) :
    d.residualCoefficient p n c i =
      c i.val * (Q p : ℂ) ^ n * (d.residualPresentation p n i).columnPhase := by
  have hn := (d.residualPresentation p n i).norm_reconstructed
  have hn' : (A.exteriorNorm (d.ideal i.val) : ℂ) =
      (Q p : ℂ) ^ n * (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ) := by
    exact_mod_cast hn
  have hne : (A.exteriorNorm (d.residualPresentation p n i).residual : ℂ) ≠ 0 := by
    exact_mod_cast (A.exteriorNorm_pos (d.residualPresentation p n i).residual).ne'
  unfold residualCoefficient adjustedCoefficient
  rw [hn']
  field_simp
  ring

def residualGaussPolynomial (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (h : A.R) : ℂ :=
  ∑ i : d.valuationColumns p n, d.residualCoefficient p n c i *
    actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff
      (d.residualPresentation p n i).generator
      (d.residualPresentation p n i).generates.1
      (generatedIdealCharacter (σ := σ) (d.residualPresentation p n i).residual
        (d.residualPresentation p n i).generator (d.residualPresentation p n i).generates) h

def localErrorWeight (p : ExteriorPrime A) (n : ℕ) : ℝ :=
  if n = 1 then (Q p)⁻¹ else if n = 6 then (1 - (Q p)⁻¹) ^ 2
    else if n = 7 then (Q p)⁻¹ else 0

theorem localErrorWeight_nonneg (p : ExteriorPrime A) (n : ℕ) :
    0 ≤ localErrorWeight p n := by
  unfold localErrorWeight
  split_ifs <;> positivity

theorem whole_error_eq_valuation_sum (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) (h : A.R) :
    wholePolynomial d.columns (d.adjustedCoefficient c) (d.errorColumn n) (h, p) =
      ∑ i : d.valuationColumns p n, d.adjustedCoefficient c i.val *
        (d.finiteColumn i.val h - d.finiteColumn i.val (actualFrequencyAmplify C (h, p))) := by
  rw [Finset.sum_coe_sort]
  unfold wholePolynomial valuationColumns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hn : primeExponent p (d.ideal i) = n <;>
    simp only [errorColumn, hn, if_true, if_false, mul_zero]

/-- The exact error at one genuine eligible pair, with the central
squared saving retained after summing the whole coefficient. -/
theorem whole_error_norm_sq (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (p : ExteriorPrime A) (hp : p ∈ P.primes) (n : ℕ) (c : ι → ℂ)
    (h : A.R) (hh : h ∈ d.errorRows p) :
    ‖wholePolynomial d.columns (d.adjustedCoefficient c) (d.errorColumn n) (h, p)‖ ^ 2 =
      localErrorWeight p n * ‖d.residualGaussPolynomial hDiff p n c h‖ ^ 2 := by
  have hrow := (Finset.mem_filter.mp hh).1
  have he := (Finset.mem_filter.mp hh).2
  have hunit : primeExponent p (d.rowIdeal h) = 0 :=
    primeExponent_zero_of_not_dvd (d.rowIdeal h) p he.1
  rw [d.whole_error_eq_valuation_sum]
  have hx := whole_amplifier_residual_gauss_norm_sq hDiff C D hD
    (Finset.univ : Finset (d.valuationColumns p n))
    (fun i => d.adjustedCoefficient c i.val)
    (fun i => d.ideal i.val) (fun i => d.generator i.val) (fun i => d.generates i.val)
    (fun i _ => d.allowed i.val (Finset.mem_filter.mp i.property).1)
    p n (d.residualPresentation p n) (d.rowIdeal h) h (d.row_generates h hrow)
    hunit d.support (d.pool_support hp)
    (fun i _ => d.column_support i.val (Finset.mem_filter.mp i.property).1)
    (d.row_support h hrow)
  change ‖∑ i : d.valuationColumns p n, d.adjustedCoefficient c i.val *
      (d.finiteColumn i.val h - d.finiteColumn i.val (actualFrequencyAmplify C (h, p)))‖ ^ 2 =
    localErrorWeight p n * ‖∑ i : d.valuationColumns p n,
      (d.adjustedCoefficient c i.val * (d.residualPresentation p n i).columnPhase) *
        actualFiniteColumn C (unitExterior A) (d.residualPresentation p n i).residual 1
          (d.residualPresentation p n i).generator (unitExterior_generates A)
          (d.residualPresentation p n i).generates h‖ ^ 2 at hx
  rw [hx]
  congr 2
  unfold residualGaussPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [actual_unit_column_eq_gauss_div_norm hDiff C]
  unfold residualCoefficient
  ring

def residualEnergy (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) : ℝ :=
  ∑ h ∈ d.errorRows p, ‖d.residualGaussPolynomial hDiff p n c h‖ ^ 2

/-- Exact disintegration of the original eligible pairs by their prime.
The pool is the same finite pool fixed before every internal divisor. -/
theorem errorEnergy_eq_residual (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (c : ι → ℂ) (n : ℕ) :
    d.errorEnergy c n = ∑ p ∈ P.primes,
      localErrorWeight p n * d.residualEnergy hDiff p n c := by
  unfold errorEnergy eligible
  rw [← sum_eligiblePairs]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [residualEnergy, Finset.mul_sum, errorRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases he : actualPrimeEligible d.frozen (d.rowIdeal h) p
  · simp only [he, if_true]
    exact d.whole_error_norm_sq hDiff D hD p hp n c h (Finset.mem_filter.mpr ⟨hh, he⟩)
  · simp only [he, if_false]

/-- The complete one-pool output, with a genuine second-transform source
in every term. No main or error source is supplied as a conclusion input. -/
theorem energy_eq_residual_sources (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (D : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B D)
    (c : ι → ℂ) :
    d.energy c = (4 / d.density) *
      (d.multiplicity * (∑ h ∈ d.mainRows,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2) +
      (∑ p ∈ P.primes, localErrorWeight p 1 * d.residualEnergy hDiff p 1 c) +
      (∑ p ∈ P.primes, localErrorWeight p 6 * d.residualEnergy hDiff p 6 c) +
      (∑ p ∈ P.primes, localErrorWeight p 7 * d.residualEnergy hDiff p 7 c)) := by
  unfold energy mainEnergy
  simp only [← d.whole_gauss_eq hDiff c, d.errorEnergy_eq_residual hDiff D hD c]

end FirstGaussPoolData

variable {Γ : Subgroup A.U}

/-- An actual nonzero element maps to its original subgroup orbit.
The arbitrary value at zero is never used by an eligible source row. -/
def engineElementOrbit (h : A.R) :
    SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ :=
  if hh : h ≠ 0 then Quotient.mk _ ⟨h, hh⟩ else Quotient.mk _ ⟨1, one_ne_zero⟩

theorem generatedColumn_orbit_element
    (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (h : A.R) (hh : h ≠ 0) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).orbit hDiff (engineElementOrbit h) =
      actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff a ha.1
        (generatedIdealCharacter (σ := σ) I a ha) h := by
  rw [engineElementOrbit, dif_pos hh]
  rfl

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.errorEnergy_eq_residual
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.energy_eq_residual_sources
