import HeckeSkeleton.Moments.MOM_INV_STEP.SecondNormWeights
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained

/-!
# Exact physical normalization of the genuine second source

For the fresh inverse pair the cube conductor is one.  The actual
Poisson factor is therefore the field constant divided by r N(d₂),
times the normalized Fourier coefficient and both residual square-root
norm weights. The actual orbit radius has the corresponding product
scaling, and all original subgroup sectors are retained.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonNormalization

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open CanonicalFirstEnergy PrimitivePoissonSource ConductorMasks FirstInversePoisson
  SecondSourceGauss SecondSourceColumns ActualPoissonScale
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "e" => unitIdeal K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def outerFactor (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) : ℝ :=
  fieldConstant K / (r.val * (sIntegerElementNorm K Sset d).val)

theorem outerFactor_nonneg (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) :
    0 ≤ outerFactor K S r d :=
  div_nonneg (fieldConstant_nonneg K)
    (mul_pos r.property (sIntegerElementNorm K Sset d).property).le

def outerRadius (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (k : Ext) (X Y : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨(k.val.val.absNorm : ℝ) /
      (r.val * (sIntegerElementNorm K Sset d).val * X.val * Y.val),
    div_pos (by exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors k.val)
      (mul_pos (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property)
        X.property) Y.property)⟩

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

theorem cubeNorm_unit (x₁ x₂ : Ext) :
    FirstPoissonNormalization.cubeNorm K S D x₁ x₂ e e = 1 := by
  rw [FirstPoissonNormalization.cubeNorm, CanonicalGroupedGauss.cubeIdeal_val,
    cube_R1_one, map_one, Nat.cast_one]

theorem finite_fourier_normalization (x₁ x₂ : Ext)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (a : OS) :
    sIntegerMaskPoissonFactor K S
        (primitiveModulus K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
        (primitiveModulus_ne_zero K S D (pairSupport K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e)) r d *
      sIntegerPeriodicDivisorFourier K Sset D.different_outside
        (primitiveModulus K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
        (primitiveModulus_ne_zero K S D (pairSupport K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e))
        (primitiveCoefficient K S D (pairSupport K S D x₁ x₂ e e)
          (pairExponent K S x₁ x₂ e e)) d.val (Ideal.Quotient.mk _ a) =
      (outerFactor K S r d : ℂ) * normalizedDivisorFourier K S D x₁ x₂ d.val a *
        normWeight K (ActualInverseFactors.residual K Sset x₁ x₂).val *
        normWeight K (ActualInverseFactors.residual K Sset x₂ x₁).val := by
  have h := FirstPoissonNormalization.prefactor_fourier K S D x₁ x₂ e e r d a
  simpa only [FirstPoissonNormalization.outerFactor, cubeNorm_unit,
    Real.sqrt_one, mul_one, outerFactor, FirstSourceColumns.residualIdeal,
    Bool.false_eq_true, if_false, if_true, leftIdeal_eq_residual, rightIdeal_eq_residual,
    normWeight, map_inv₀, Complex.conj_ofReal,
    FirstSourceColumns.pairFourier, normalizedDivisorFourier] using h

theorem radius_normalization (x₁ x₂ k : Ext)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (X Y : {r : ℝ // 0 < r}) :
    (sIntegerMaskDualRadius K S
      (primitiveModulus K S D (pairSupport K S D x₁ x₂ e e) (pairExponent K S x₁ x₂ e e))
      (primitiveModulus_ne_zero K S D (pairSupport K S D x₁ x₂ e e)
        (pairExponent K S x₁ x₂ e e)) r d).val * (k.val.val.absNorm : ℝ) =
      (outerRadius K S r d k X Y).val /
        ((FirstSourceEnergy.normScale K X (ActualInverseFactors.residual K Sset x₁ x₂).val).val *
          (FirstSourceEnergy.normScale K Y (ActualInverseFactors.residual K Sset x₂ x₁).val).val) := by
  have h := FirstPoissonNormalization.dualRadius_normalized K S D
    x₁ x₂ x₁ x₂ e e k ⟨rfl, rfl, rfl⟩ r d X Y
  simpa only [FirstPoissonNormalization.outerRadius, cubeNorm_unit, mul_one,
    outerRadius, FirstSourceColumns.residualIdeal, Bool.false_eq_true, if_false, if_true,
    leftIdeal_eq_residual, rightIdeal_eq_residual] using h

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [Γ.FiniteIndex] [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def profile (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (k : Ext)
    (X Y : {r : ℝ // 0 < r}) : Profile K S where
  finiteTest := sIntegerFiniteFourierTestFunction K S μv h
  finiteTest_continuous :=
    (sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs).1.continuous
  finiteTest_compact :=
    (sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv h hlc hcs).2
  archTest := φ
  radius := outerRadius K S r d k X Y
  leftScale := X
  rightScale := Y

include hΓ in
theorem actual_pairTerm_eq (x₁ x₂ : Ext)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS)) (k : Ext × Sector)
    (X Y : {r : ℝ // 0 < r}) :
    FirstParentRetained.pairTerm K S D Γ hΓ μv x₁ x₂ e e φ h hlc hcs ∅ r δ k =
      (outerFactor K S r (sIntegerMaskGenerator K Sset δ) : ℂ) *
        normalizedDivisorFourier K S D x₁ x₂ (sIntegerMaskGenerator K Sset δ).val
          (CanonicalSectors.rowElement K Sset Γ D k).val *
        normWeight K (ActualInverseFactors.residual K Sset x₁ x₂).val *
        normWeight K (ActualInverseFactors.residual K Sset x₂ x₁).val *
        (profile K S μv ν φ h hlc hcs r (sIntegerMaskGenerator K Sset δ) k.1 X Y).value K S
          (ActualInverseFactors.residual K Sset x₁ x₂).val
          (ActualInverseFactors.residual K Sset x₂ x₁).val := by
  rcases k with ⟨I, ξ⟩
  unfold FirstParentRetained.pairTerm
  rw [FirstParentRetained.dualTerm_sector K S D Γ hΓ μv ν
    x₁ x₂ x₁ x₂ e e I ⟨rfl, rfl, rfl⟩ ξ φ h hlc hcs ∅ r δ X Y]
  dsimp only [CanonicalBlock.primitivePairBlock, PrimitivePoissonSource.block,
    ActualMaskedPoissonBlock.prefactor]
  change sIntegerMaskPoissonFactor K S _ _ r (sIntegerMaskGenerator K Sset δ) *
    (sIntegerPeriodicDivisorFourier K Sset D.different_outside _ _ _
      (sIntegerMaskGenerator K Sset δ).val
      (Ideal.Quotient.mk _ (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val) * _) = _
  rw [← mul_assoc, finite_fourier_normalization]
  congr 1
  simp only [FirstParentRetained.profile, Profile.value,
    FirstPoissonNormalization.outerRadius, cubeNorm_unit, mul_one, profile, outerRadius,
    FirstSourceColumns.residualIdeal, Bool.false_eq_true, if_false, if_true,
    leftIdeal_eq_residual, rightIdeal_eq_residual]

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondPoissonNormalization

end
