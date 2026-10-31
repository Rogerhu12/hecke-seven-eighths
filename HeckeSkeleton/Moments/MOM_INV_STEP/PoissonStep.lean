import HeckeGeneral.Analysis.SIntegerMaskedOrbitalPoisson

/-!
# Two genuine masked orbital Poisson transformations

This module keeps the actual S-integer orbital series, the original unit
subgroup, every mask divisor and its norm-scaled radius, and both additive
zero terms.  The Poisson equalities follow from
`sIntegerMaskedPeriodicOrbitalPoisson`; they are not fields of the input.

`two_poisson_transforms_of_dual_identification` composes two applications of
that theorem.  Its `hidentify` hypothesis is deliberately visible: the
arithmetic and common-kernel identification of an inverse-column norm with
the second physical family must be supplied separately.  In particular,
this theorem by itself does not assert the canonical-energy recursion.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP

open NumberField IsDedekindDomain UniqueFactorizationMonoid
  HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
  HeckeGeneral.Analysis MeasureTheory
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Actual data for one masked orbital sum.  The periodic coefficient is
invariant under the original subgroup, and neither the coefficient nor the
test function is replaced by a majorant before the Fourier transform. -/
structure ActualMaskedPoissonBlock where
  modulus : OS
  modulus_ne_zero : modulus ≠ 0
  profile : SchwartzMap V ℂ
  localTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ
  localTest_locallyConstant : ∀ v ∈ S, IsLocallyConstant (localTest v)
  localTest_compactSupport : ∀ v ∈ S, HasCompactSupport (localTest v)
  mask : Finset (HeightOneSpectrum OS)
  coefficient : (OS ⧸ Ideal.span ({modulus} : Set OS)) → ℂ
  invariant : ∀ u : Γ, ∀ a : OS,
    coefficient (Ideal.Quotient.mk _
      (((S : Set (HeightOneSpectrum (𝓞 K))).unitEquivUnitsInteger K u.val).val * a)) =
        coefficient (Ideal.Quotient.mk _ a)
  radius : {r : ℝ // 0 < r}

namespace ActualMaskedPoissonBlock

variable {K S Γ}

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing OS]

/-- The literal masked physical sum. -/
def physical (b : ActualMaskedPoissonBlock K S Γ) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ b.profile
    (sIntegerFiniteTestFunction K S b.localTest) b.radius
    (fun q => sIntegerOrbitAvoidanceMask K _ Γ b.mask q *
      sIntegerPeriodicOrbitWeight K _ Γ b.modulus b.coefficient b.invariant q)

/-- The actual summand on one original subgroup orbit. -/
def orbitalTerm (b : ActualMaskedPoissonBlock K S Γ)
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) : ℂ :=
  (sIntegerOrbitAvoidanceMask K _ Γ b.mask q *
      sIntegerPeriodicOrbitWeight K _ Γ b.modulus b.coefficient b.invariant q) *
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K))) b.profile
        (sIntegerFiniteTestFunction K S b.localTest))
      ⟨b.radius.val * (sIntegerOrbitNorm K _ Γ q).val,
        mul_pos b.radius.property (sIntegerOrbitNorm K _ Γ q).property⟩

theorem physical_eq_tsum (b : ActualMaskedPoissonBlock K S Γ) :
    b.physical = ∑' q, b.orbitalTerm q := rfl

/-- Absolute convergence follows from the actual finite quotient and the
Schwartz test; it is not an additional hypothesis of the finite expansion. -/
theorem summable_norm_orbitalTerm (b : ActualMaskedPoissonBlock K S Γ) :
    Summable (fun q => ‖b.orbitalTerm q‖) := by
  exact summable_norm_sIntegerMaskedOrbitalProfile K S Γ b.profile
    (sIntegerFiniteTestFunction K S b.localTest)
    (continuous_sIntegerFiniteTestFunction K S b.localTest b.localTest_locallyConstant)
    (hasCompactSupport_sIntegerFiniteTestFunction K S b.localTest b.localTest_compactSupport)
    b.radius b.mask
    (sIntegerPeriodicOrbitWeight K _ Γ b.modulus b.coefficient b.invariant)
    (sIntegerPeriodicResidueL1 K _ b.modulus b.modulus_ne_zero b.coefficient)
    (norm_sIntegerPeriodicOrbitWeight_le_L1 K _ Γ b.modulus b.modulus_ne_zero
      b.coefficient b.invariant)

/-- Finite signed expansions commute with the actual infinite orbit sum.
Each summand's absolute convergence was proved above. -/
theorem finite_weighted_physical_eq_tsum {ι : Type*} (source : Finset ι)
    (weight : ι → ℂ) (blocks : ι → ActualMaskedPoissonBlock K S Γ) :
    (∑ i ∈ source, weight i * (blocks i).physical) =
      ∑' q, ∑ i ∈ source, weight i * (blocks i).orbitalTerm q := by
  symm
  rw [Summable.tsum_finsetSum
    (fun i _hi => ((blocks i).summable_norm_orbitalTerm.of_norm).mul_left (weight i))]
  simp only [tsum_mul_left, physical_eq_tsum]

/-- Inclusion-exclusion coefficient for an actual mask divisor. -/
def divisorCoefficient (b : ActualMaskedPoissonBlock K S Γ)
    (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ)

/-- The exact first prefactor, including the modulus, mask norm and
discriminant. -/
def prefactor (b : ActualMaskedPoissonBlock K S Γ)
    (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  sIntegerMaskPoissonFactor K S b.modulus b.modulus_ne_zero b.radius
    (sIntegerMaskGenerator K _ D)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

/-- The genuine Fourier-side orbital series at the divisor's own radius. -/
def dual (b : ActualMaskedPoissonBlock K S Γ)
    (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  sIntegerWeightedOrbitalSeries K S Γ (traceSchwartzFourier K b.profile)
    (sIntegerFiniteFourierTestFunction K S μv b.localTest)
    (sIntegerMaskDualRadius K S b.modulus b.modulus_ne_zero b.radius
      (sIntegerMaskGenerator K _ D))
    (sIntegerPeriodicFourierOrbitWeight K _ hS Γ b.modulus b.modulus_ne_zero
      b.coefficient b.invariant (sIntegerMaskGenerator K _ D).val)

/-- Both additive zero terms, with their actual Haar covolume. -/
def zeroContribution (b : ActualMaskedPoissonBlock K S Γ)
    (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
    (b.prefactor D *
        (sIntegerPeriodicDivisorFourier K _ hS b.modulus b.modulus_ne_zero
            b.coefficient (sIntegerMaskGenerator K _ D).val 0 *
          sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K b.profile) b.localTest 0) -
      b.coefficient 0 *
        sIntegerTensorTerm K S (traceSchwartzToMixed K b.profile) b.localTest 0)

/-- A finite divisor sum; none of its zero modes has been discarded. -/
def transformed (b : ActualMaskedPoissonBlock K S Γ) : ℂ :=
  ∑ D ∈ b.mask.powerset, b.divisorCoefficient D *
    (b.prefactor D * b.dual μv hS D + b.zeroContribution μv hS D)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- One actual masked orbital Poisson transformation, proved from the
repository's genuine Poisson theorem. -/
theorem physical_eq_transformed (b : ActualMaskedPoissonBlock K S Γ) :
    b.physical = b.transformed μv hS := by
  exact sIntegerMaskedPeriodicOrbitalPoisson K S Γ b.modulus b.modulus_ne_zero
    hS ν μv μ b.profile b.localTest b.localTest_locallyConstant
    b.localTest_compactSupport b.mask b.coefficient b.invariant b.radius

include ν μ in
/-- Poisson can be applied inside a finite signed outer family before
taking absolute values.  The weights may depend on all frozen outer data. -/
theorem finite_physical_eq_transformed {ι : Type*} (source : Finset ι)
    (weight : ι → ℂ) (blocks : ι → ActualMaskedPoissonBlock K S Γ) :
    (∑ i ∈ source, weight i * (blocks i).physical) =
      ∑ i ∈ source, weight i * (blocks i).transformed μv hS := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [physical_eq_transformed μv hS ν μ]

include ν μ in
/-- Two exact Poisson transformations.  The explicit `hidentify` is the
remaining arithmetic/common-kernel interface between the first dual series
and the second physical family.  It is an equality of signed actual sums,
not a hypothesis that an energy estimate or recursive bound already holds.
All first and second divisor masks and both pairs of zero terms survive. -/
theorem two_poisson_transforms_of_dual_identification {ι : Type*}
    (first : ActualMaskedPoissonBlock K S Γ)
    (secondSource : Finset (HeightOneSpectrum OS) → Finset ι)
    (weight : Finset (HeightOneSpectrum OS) → ι → ℂ)
    (second : Finset (HeightOneSpectrum OS) → ι → ActualMaskedPoissonBlock K S Γ)
    (hidentify : ∀ D ∈ first.mask.powerset,
      first.dual μv hS D =
        ∑ i ∈ secondSource D, weight D i * (second D i).physical) :
    first.physical =
      ∑ D ∈ first.mask.powerset, first.divisorCoefficient D *
        (first.prefactor D *
            (∑ i ∈ secondSource D, weight D i *
              ∑ E ∈ (second D i).mask.powerset,
                (second D i).divisorCoefficient E *
                  ((second D i).prefactor E * (second D i).dual μv hS E +
                    (second D i).zeroContribution μv hS E)) +
          first.zeroContribution μv hS D) := by
  rw [physical_eq_transformed μv hS ν μ]
  unfold transformed
  apply Finset.sum_congr rfl
  intro D hD
  rw [hidentify D hD, finite_physical_eq_transformed μv hS ν μ] <;> rfl

/-- A zero-mode elimination requires both literal finite coefficients to
vanish.  It cannot follow merely from the frequency being nonzero. -/
theorem zeroContribution_eq_zero
    (b : ActualMaskedPoissonBlock K S Γ) (D : Finset (HeightOneSpectrum OS))
    (hprimal : b.coefficient 0 = 0)
    (hdual : sIntegerPeriodicDivisorFourier K _ hS b.modulus b.modulus_ne_zero
      b.coefficient (sIntegerMaskGenerator K _ D).val 0 = 0) :
    b.zeroContribution μv hS D = 0 := by
  simp only [zeroContribution, hprimal, hdual, zero_mul, mul_zero, sub_self]

include ν μ in
/-- When both genuine additive zero coefficients vanish for every mask
divisor, the finite formula contains exactly the nonzero orbital terms. -/
theorem physical_eq_dual_of_zero_coefficients
    (b : ActualMaskedPoissonBlock K S Γ)
    (hprimal : b.coefficient 0 = 0)
    (hdual : ∀ D ∈ b.mask.powerset,
      sIntegerPeriodicDivisorFourier K _ hS b.modulus b.modulus_ne_zero
        b.coefficient (sIntegerMaskGenerator K _ D).val 0 = 0) :
    b.physical = ∑ D ∈ b.mask.powerset,
      b.divisorCoefficient D * b.prefactor D * b.dual μv hS D := by
  rw [physical_eq_transformed μv hS ν μ]
  unfold transformed
  apply Finset.sum_congr rfl
  intro D hD
  rw [zeroContribution_eq_zero μv hS b D hprimal (hdual D hD), add_zero,
    mul_assoc]

end ActualMaskedPoissonBlock

end HeckeSkeleton.Moments.MOM_INV_STEP
