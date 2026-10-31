import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

/-!
# Source normalization at the actual second-transform radius

The original row radius only pays the row scale.  The whole coefficient
normalizations pay the separate column length.  This file keeps those
two facts separate: it never inserts the column exponent into the row
radius.

The source identities are literal per-column divisions by the square
roots of the original normalization scales.  The raw column factors are
retained; their primitive profile windows, rather than an aggregate
moment bound, control them in an application.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

section OriginalRadius

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Only the actual row-window exponent occurs in this radius condition. -/
theorem secondOrbitalScalar_row_norm_le
    (Z : ℝ) (hZ : 1 < Z) (krow g : ℝ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val) :
    ‖secondOrbitalScalar (K := K) (S := S) r D‖ ≤
      orbitalFieldFactor K * Z ^ (krow + g) := by
  simpa only [zero_sub, sub_zero] using
    secondOrbitalScalar_norm_le_rpow Z hZ 0 krow g r D
      (by simpa only [zero_sub] using hrow)

/-- The exact source coefficient identity before estimating either raw
column.  Both central normalizations occur once. -/
theorem second_source_normalized_pair_norm
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (NL NR : ℝ) (c d : ℂ) :
    ‖secondOrbitalScalar (K := K) (S := S) r D *
      ((c / (Real.sqrt NL : ℂ)) * star (d / (Real.sqrt NR : ℂ)))‖ =
      (‖secondOrbitalScalar (K := K) (S := S) r D‖ /
        (Real.sqrt NL * Real.sqrt NR)) * (‖c‖ * ‖d‖) := by
  simp only [norm_mul, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- A lower window for the original normalization scales is sufficient;
no claim about an arbitrary Gauss coefficient is made. -/
theorem second_source_central_scale_lower
    (Z : ℝ) (hZ : 0 < Z) (a₀ NL NR : ℝ)
    (hNL : Z ^ a₀ ≤ NL) (hNR : Z ^ a₀ ≤ NR) :
    Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR := by
  have hp : 0 ≤ Z ^ a₀ := (Real.rpow_pos_of_pos hZ a₀).le
  calc
    _ = Real.sqrt (Z ^ a₀) * Real.sqrt (Z ^ a₀) := by
      nlinarith [Real.sq_sqrt hp]
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hNL) (Real.sqrt_le_sqrt hNR)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The missing column exponent is paid by the literal source
normalization, while the original radius remains unchanged. -/
theorem second_source_normalized_scalar_bound
    (Z : ℝ) (hZ : 1 < Z) (a₀ krow g NL NR : ℝ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR) :
    ‖secondOrbitalScalar (K := K) (S := S) r D‖ /
        (Real.sqrt NL * Real.sqrt NR) ≤
      orbitalFieldFactor K * Z ^ (krow + g - a₀) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 < Z ^ a₀ := Real.rpow_pos_of_pos hz _
  have hn : 0 ≤ Real.sqrt NL * Real.sqrt NR :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hscalar := secondOrbitalScalar_row_norm_le Z hZ krow g r D hrow
  calc
    _ ≤ (orbitalFieldFactor K * Z ^ (krow + g)) /
        (Real.sqrt NL * Real.sqrt NR) :=
      div_le_div_of_nonneg_right hscalar hn
    _ ≤ (orbitalFieldFactor K * Z ^ (krow + g)) / Z ^ a₀ := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hp hcentral)
          (mul_nonneg (orbitalFieldFactor_nonneg K) (Real.rpow_nonneg hz.le _))
    _ = _ := by rw [Real.rpow_sub hz]; ring

/-- An actual normalized source pair, with both raw column factors
retained instead of assuming a bound on the entire source. -/
theorem second_source_normalized_pair_bound
    (Z : ℝ) (hZ : 1 < Z) (a₀ krow g NL NR : ℝ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (c d : ℂ) :
    ‖secondOrbitalScalar (K := K) (S := S) r D *
      ((c / (Real.sqrt NL : ℂ)) * star (d / (Real.sqrt NR : ℂ)))‖ ≤
      (orbitalFieldFactor K * Z ^ (krow + g - a₀)) * (‖c‖ * ‖d‖) := by
  rw [second_source_normalized_pair_norm]
  exact mul_le_mul_of_nonneg_right
    (second_source_normalized_scalar_bound Z hZ a₀ krow g NL NR r D hrow hcentral)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- This form binds directly to the two actual coefficient fields of a
source chart by pointwise original normalization identities. -/
theorem second_source_actual_coefficients_bound
    (Z : ℝ) (hZ : 1 < Z) (a₀ krow g NL NR : ℝ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (c d rawLeft rawRight : ℂ)
    (hleft : c = rawLeft / (Real.sqrt NL : ℂ))
    (hright : d = rawRight / (Real.sqrt NR : ℂ)) :
    ‖secondOrbitalScalar (K := K) (S := S) r D * (c * star d)‖ ≤
      (orbitalFieldFactor K * Z ^ (krow + g - a₀)) * (‖rawLeft‖ * ‖rawRight‖) := by
  rw [hleft, hright]
  exact second_source_normalized_pair_bound Z hZ a₀ krow g NL NR r D hrow hcentral
    rawLeft rawRight

end OriginalRadius

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- Literal source normalization, complete common correlation, central
common norms, pool density and child allowance.  The full actual radius
and frequency are preserved. -/
def FirstCommonCharacterBlock.secondSourceWeight
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z a₀ q wo w B krow g ell density NL NR : ℝ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) : ℝ :=
  density * (‖secondOrbitalScalar (K := K) (S := A.Sf) r D‖ /
      (Real.sqrt NL * Real.sqrt NR)) *
    ‖b.secondCorrelation (σ := σ) a d ha hd h‖ /
    (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ)) *
    Z ^ (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
        (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
      secondCommonChildAllowance Z w B ell DE.1 DE.2)

theorem FirstCommonCharacterBlock.secondSourceWeight_le
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w B krow g ell density densityBound NL NR : ℝ)
    (hB : 0 ≤ densityBound) (hdensity : density ≤ densityBound * Z ^ (-ell))
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) :
    b.secondSourceWeight C Z a₀ q wo w B krow g ell density NL NR r D a d ha hd h ≤
      densityBound * orbitalFieldFactor K * Z ^ (a₀ + q + wo + w + B) /
        (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  have hρ : 0 ≤ densityBound * Z ^ (-ell) :=
    mul_nonneg hB (Real.rpow_nonneg hz.le _)
  have hscalar := second_source_normalized_scalar_bound Z hZ a₀ krow g NL NR r D
    hrow hcentral
  have hcorr := b.secondCorrelation_norm_le C a d ha hd h
  have hfirst := mul_le_mul hdensity hscalar
    (div_nonneg (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hρ
  have hsecond := mul_le_mul hfirst hcorr (norm_nonneg _)
    (mul_nonneg hρ (mul_nonneg (orbitalFieldFactor_nonneg K) (Real.rpow_nonneg hz.le _)))
  have hthird := div_le_div_of_nonneg_right hsecond
    (mul_nonneg (Real.sqrt_nonneg (Ideal.absNorm DE.1 : ℝ))
      (Real.sqrt_nonneg (Ideal.absNorm DE.2 : ℝ)))
  have hfourth := mul_le_mul_of_nonneg_right hthird
    (Real.rpow_nonneg hz.le
      (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
          (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
        secondCommonChildAllowance Z w B ell DE.1 DE.2))
  unfold FirstCommonCharacterBlock.secondSourceWeight
  apply hfourth.trans_eq
  calc
    _ = densityBound *
      (Z ^ (-ell) * (orbitalFieldFactor K * Z ^ (krow + g - a₀)) *
        ((Ideal.absNorm (gcd DE.1 DE.2) : ℝ) /
          (Ideal.absNorm (b.secondUnitRadical C h).val : ℝ)) /
        (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ)) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
            (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
          secondCommonChildAllowance Z w B ell DE.1 DE.2)) := by ring
    _ = _ := by
      rw [second_actual_scalar_budget_identity Z hZ (orbitalFieldFactor K)
        a₀ q wo w B krow g ell DE.1 DE.2
        (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val
        hD hE (b.secondUnitRadical C h).property.1]
      ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_source_normalized_pair_norm
#print axioms HeckeSkeleton.Moments.EngineStep.second_source_actual_coefficients_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondSourceWeight_le

