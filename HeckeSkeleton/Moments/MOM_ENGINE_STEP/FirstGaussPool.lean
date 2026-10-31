import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GaussPoolDictionary

/-!
# The actual first Gauss energies enter one fixed arithmetic pool

The pool is selected before this data and before the whole coefficient.
The record contains only actual ideals, their allowed generators, their
finite prime supports, and norm bounds. It contains no energy inequality.
The resulting estimate keeps the complete coefficient in every amplified
column and every correction at valuation 1, 6, or 7. Its validity for all
coefficients lets the same pool be used for every real Fourier parameter.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- Only primitive arithmetic and size data for a finite whole Gauss
polynomial. The chosen pool is an earlier parameter. -/
structure FirstGaussPoolData
    (C : A.GeneralArithmeticContext σ η hS)
    (P : PowerScaleExteriorPool A bad Z ell eps) (ι : Type*) where
  columns : Finset ι
  ideal : ι → A.Exterior
  generator : ι → A.R
  generates : ∀ i, A.Generates (ideal i) (generator i)
  allowed : ∀ i ∈ columns, A.IsAllowed C.correction.B
    (Units.mk0 (generator i : K) (by exact_mod_cast (generates i).1))
  rows : Finset A.R
  rowIdeal : A.R → A.Exterior
  row_generates : ∀ h ∈ rows, A.Generates (rowIdeal h) h
  support : Finset (ExteriorPrime A)
  column_support : ∀ i ∈ columns, ∀ p : ExteriorPrime A,
    MaskedQuotientCRT.primeExponent p (ideal i) ≠ 0 → p ∈ support
  row_support : ∀ h ∈ rows, ∀ p : ExteriorPrime A,
    MaskedQuotientCRT.primeExponent p (rowIdeal h) ≠ 0 → p ∈ support
  pool_support : P.primes ⊆ support
  frozen : Ideal (𝓞 K)
  frozen_ne_zero : frozen ≠ 0
  rowExponent : ℝ
  frozenExponent : ℝ
  rowExponent_nonneg : 0 ≤ rowExponent
  row_norm : ∀ h ∈ rows, (Ideal.absNorm (rowIdeal h).val : ℝ) ≤ Z ^ rowExponent
  frozen_norm : (Ideal.absNorm frozen : ℝ) ≤ Z ^ frozenExponent
  density_pos : 0 < P.rowDensity rowExponent frozenExponent

namespace FirstGaussPoolData

variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}

def finiteColumn (d : FirstGaussPoolData C P ι) (i : ι) (h : A.R) : ℂ :=
  actualFiniteColumn C (unitExterior A) (d.ideal i) 1 (d.generator i)
    (unitExterior_generates A) (d.generates i) h

def gaussColumn (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (i : ι) (h : A.R) : ℂ :=
  actualSIntegerGauss K (A.Sf : Set _) hDiff (d.generator i) (d.generates i).1
    (generatedIdealCharacter (σ := σ) (d.ideal i) (d.generator i) (d.generates i)) h

/-- The exact central norm is put into the entire original coefficient. -/
def adjustedCoefficient (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (i : ι) : ℂ :=
  c i * (A.exteriorNorm (d.ideal i) : ℂ)

def eligible (d : FirstGaussPoolData C P ι) : Finset (A.R × ExteriorPrime A) :=
  eligiblePairs d.rows P.primes (fun h p => actualPrimeEligible d.frozen (d.rowIdeal h) p)

def mainRows (d : FirstGaussPoolData C P ι) : Finset A.R :=
  d.eligible.image (actualFrequencyAmplify C)

def errorColumn (d : FirstGaussPoolData C P ι)
    (t : ℕ) (i : ι) (hp : A.R × ExteriorPrime A) : ℂ :=
  if MaskedQuotientCRT.primeExponent hp.2 (d.ideal i) = t then
    d.finiteColumn i hp.1 - d.finiteColumn i (actualFrequencyAmplify C hp) else 0

def density (d : FirstGaussPoolData C P ι) : ℝ :=
  P.rowDensity d.rowExponent d.frozenExponent

def multiplicity (d : FirstGaussPoolData C P ι) : ℝ :=
  (d.rowExponent + 6 * ell) / (ell / 2)

theorem multiplicity_nonneg (d : FirstGaussPoolData C P ι) : 0 ≤ d.multiplicity := by
  exact div_nonneg (add_nonneg d.rowExponent_nonneg
    (mul_nonneg (by norm_num) P.exponent_pos.le))
      (div_nonneg P.exponent_pos.le (by norm_num))

def mainEnergy (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ℝ :=
  ∑ y ∈ d.mainRows, ‖wholePolynomial d.columns (d.adjustedCoefficient c) d.finiteColumn y‖ ^ 2

def errorEnergy (d : FirstGaussPoolData C P ι) (c : ι → ℂ) (t : ℕ) : ℝ :=
  ∑ hp ∈ d.eligible, ‖wholePolynomial d.columns (d.adjustedCoefficient c) (d.errorColumn t) hp‖ ^ 2

/-- Explicit main and three correction energies produced by that pool. -/
def energy (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : ℝ :=
  (4 / d.density) * (d.multiplicity * d.mainEnergy c +
    d.errorEnergy c 1 + d.errorEnergy c 6 + d.errorEnergy c 7)

theorem energy_nonneg (d : FirstGaussPoolData C P ι) (c : ι → ℂ) : 0 ≤ d.energy c := by
  have hm : 0 ≤ d.mainEnergy c := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he (t : ℕ) : 0 ≤ d.errorEnergy c t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact mul_nonneg (div_nonneg (by norm_num) d.density_pos.le)
    (add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg d.multiplicity_nonneg hm) (he 1)) (he 6)) (he 7))

theorem whole_error_eq (d : FirstGaussPoolData C P ι) (c : ι → ℂ)
    (t : ℕ) (hp : A.R × ExteriorPrime A) :
    wholePolynomial d.columns (d.adjustedCoefficient c) (d.errorColumn t) hp =
      valuationError d.columns (d.adjustedCoefficient c) d.finiteColumn
        (fun i => MaskedQuotientCRT.primeExponent hp.2 (d.ideal i))
        t hp.1 (actualFrequencyAmplify C hp) := by
  unfold wholePolynomial valuationError errorColumn
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : MaskedQuotientCRT.primeExponent hp.2 (d.ideal i) = t <;> simp [h]

theorem whole_gauss_eq (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (c : ι → ℂ) (h : A.R) :
    wholePolynomial d.columns c (d.gaussColumn hDiff) h =
      wholePolynomial d.columns (d.adjustedCoefficient c) d.finiteColumn h :=
  whole_gauss_eq_actual_unit_columns hDiff C d.columns c d.ideal d.generator d.generates h

theorem coefficient_mul_finite_eq_gauss (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (c : ι → ℂ) (i : ι) (h : A.R) :
    d.adjustedCoefficient c i * d.finiteColumn i h = c i * d.gaussColumn hDiff i h := by
  unfold adjustedCoefficient finiteColumn gaussColumn
  rw [actual_unit_column_eq_gauss_div_norm hDiff C]
  have hn : (A.exteriorNorm (d.ideal i) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (A.exteriorNorm_pos (d.ideal i)))
  field_simp

/-- Each complete valuation error is the literal difference of the
original Gauss columns with the original whole coefficient. -/
theorem whole_error_eq_gauss (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (c : ι → ℂ) (t : ℕ) (hp : A.R × ExteriorPrime A) :
    wholePolynomial d.columns (d.adjustedCoefficient c) (d.errorColumn t) hp =
      valuationError d.columns c (d.gaussColumn hDiff)
        (fun i => MaskedQuotientCRT.primeExponent hp.2 (d.ideal i))
        t hp.1 (actualFrequencyAmplify C hp) := by
  unfold wholePolynomial errorColumn valuationError
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : MaskedQuotientCRT.primeExponent hp.2 (d.ideal i) = t
  · simp only [ht, if_true]
    rw [mul_sub, d.coefficient_mul_finite_eq_gauss hDiff c,
      d.coefficient_mul_finite_eq_gauss hDiff c, mul_sub]
  · simp only [ht, if_false, mul_zero]

/-- Exact source dictionary for the second transform: the amplified
main term and all errors are whole genuine Gauss polynomials. -/
theorem energy_eq_gauss_outputs (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (c : ι → ℂ) :
    d.energy c = (4 / d.density) *
      (d.multiplicity * ∑ h ∈ d.mainRows,
          ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 +
       (∑ hp ∈ d.eligible, ‖valuationError d.columns c (d.gaussColumn hDiff)
          (fun i => MaskedQuotientCRT.primeExponent hp.2 (d.ideal i))
          1 hp.1 (actualFrequencyAmplify C hp)‖ ^ 2) +
       (∑ hp ∈ d.eligible, ‖valuationError d.columns c (d.gaussColumn hDiff)
          (fun i => MaskedQuotientCRT.primeExponent hp.2 (d.ideal i))
          6 hp.1 (actualFrequencyAmplify C hp)‖ ^ 2) +
       (∑ hp ∈ d.eligible, ‖valuationError d.columns c (d.gaussColumn hDiff)
          (fun i => MaskedQuotientCRT.primeExponent hp.2 (d.ideal i))
          7 hp.1 (actualFrequencyAmplify C hp)‖ ^ 2)) := by
  unfold energy mainEnergy errorEnergy
  simp only [← d.whole_gauss_eq hDiff c, d.whole_error_eq_gauss hDiff c]

/-- One fixed actual prime pool bounds every whole Gauss coefficient. -/
theorem energy_bound (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (c : ι → ℂ) :
    (∑ h ∈ d.rows, ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2) ≤
      d.energy c := by
  have hunit (p : ExteriorPrime A) :
      MaskedQuotientCRT.primeExponent p (unitExterior A) = 0 := by
    change (UniqueFactorizationMonoid.normalizedFactors (1 : Ideal (𝓞 K))).count p.val.asIdeal = 0
    simp
  have he := P.finite_energy C d.columns (d.adjustedCoefficient c)
    (fun _ => unitExterior A) d.ideal (fun _ => 1) d.generator
    (fun _ => unitExterior_generates A) d.generates
    (by intro i hi; simp [SArithmeticData.IsAllowed]) d.allowed
    d.support (by intro i hi p hp; exact (hp (hunit p)).elim) d.column_support
    d.rows d.rowIdeal d.row_generates d.row_support d.pool_support
    d.frozen d.frozen_ne_zero (by intro i hi; exact one_dvd _)
    d.rowExponent d.frozenExponent d.row_norm d.frozen_norm d.density_pos
  dsimp only at he
  simp_rw [d.whole_gauss_eq hDiff c]
  simpa only [energy, mainEnergy, errorEnergy, mainRows, eligible, density,
    multiplicity, whole_error_eq, finiteColumn, Finset.sum_add_distrib, add_assoc] using he

/-- An injective genuine row chart may be used directly by the first
orbital source. Its bounded row multiplier is retained explicitly. -/
theorem weighted_energy_bound {H : Type*}
    (d : FirstGaussPoolData C P ι)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (rows : Finset H) (frequency : H → A.R)
    (hinj : Set.InjOn frequency (rows : Set H))
    (hrows : rows.image frequency ⊆ d.rows)
    (q : H → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hq : ∀ h ∈ rows, ‖q h‖ ≤ W) (c : ι → ℂ) :
    weightedEnergy rows (fun h => ‖q h‖)
      (fun h => wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)) ≤
        W * d.energy c := by
  calc
    _ ≤ W * ∑ h ∈ rows,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) (frequency h)‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_right (hq h hh) (sq_nonneg _)
    _ = W * ∑ h ∈ rows.image frequency,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ W * ∑ h ∈ d.rows,
        ‖wholePolynomial d.columns c (d.gaussColumn hDiff) h‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun h _ _ => sq_nonneg _)) hW
    _ ≤ _ := mul_le_mul_of_nonneg_left (d.energy_bound hDiff c) hW

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.energy_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.weighted_energy_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.energy_eq_gauss_outputs
