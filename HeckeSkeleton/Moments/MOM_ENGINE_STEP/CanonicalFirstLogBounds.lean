import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogChart

/-!
# Bounds for the constructed first log chart

The bounds below are proved from the literal fields of `canonicalLog`.
The row estimate uses the arithmetic fact that every original orbital
norm is at least one.  The exact common factor retains the active
modulus with exponent `δ - 1/2` after the genuine Gauss square root.

The column estimates retain the inverse norm supplied by Poisson.  The
small Mellin powers are paid only from individual original norm windows;
no transformed row-weight or transformed coefficient bound is an input.
-/

noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters

namespace CanonicalFirstLog

theorem tiltScalar_norm {N : ℝ} (hN : 0 < N) (δ : ℝ) :
    ‖((N ^ δ : ℝ) : ℂ)‖ = N ^ δ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hN.le _)]

theorem scaledTiltScalar_norm {N : ℝ} (hN : 0 < N) (δ : ℝ) (c : ℂ) :
    ‖c * ((N ^ δ : ℝ) : ℂ)‖ = ‖c‖ * N ^ δ := by
  rw [norm_mul, tiltScalar_norm hN δ]

theorem normalizedTiltScalar_norm {N : ℝ} (hN : 0 < N) (δ : ℝ) :
    ‖((N ^ δ : ℝ) : ℂ) / (N : ℂ)‖ = N ^ (δ - 1) := by
  rw [norm_div, tiltScalar_norm hN δ, Complex.norm_real,
    Real.norm_of_nonneg hN.le, Real.rpow_sub_one hN.ne' δ]

theorem scaledNormalizedTiltScalar_norm {N : ℝ} (hN : 0 < N) (δ : ℝ) (c : ℂ) :
    ‖c * (((N ^ δ : ℝ) : ℂ) / (N : ℂ))‖ = ‖c‖ * N ^ (δ - 1) := by
  rw [norm_mul, normalizedTiltScalar_norm hN δ]

/-- A tiny norm power is paid from an individual original polynomial
norm window, with no column-cardinality loss. -/
theorem tilt_le_of_norm_window {N Z B δ : ℝ} (hN : 0 < N) (hZ : 0 < Z)
    (hδ : 0 ≤ δ) (hwindow : N ≤ Z ^ B) : N ^ δ ≤ Z ^ (B * δ) := by
  exact (Real.rpow_le_rpow hN.le hwindow hδ).trans_eq
    (Real.rpow_mul hZ.le B δ).symm

theorem scaledNormalizedTiltScalar_norm_le_of_window
    {N Z B δ C : ℝ} (hN : 0 < N) (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow : N ≤ Z ^ B) (c : ℂ) (hc : ‖c‖ ≤ C) :
    ‖c * (((N ^ δ : ℝ) : ℂ) / (N : ℂ))‖ ≤ C * Z ^ (B * δ) / N := by
  rw [norm_mul, norm_div, tiltScalar_norm hN δ, Complex.norm_real,
    Real.norm_of_nonneg hN.le, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hN.le
  exact mul_le_mul hc (tilt_le_of_norm_window hN hZ hδ hwindow)
    (Real.rpow_nonneg hN.le _) ((norm_nonneg c).trans hc)

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The actual common Poisson scalar times the explicit Mellin row
factor.  This is exactly the weight of the constructed first chart. -/
def poissonTiltWeight (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (δ : ℝ)
    (q : Q) : ℂ :=
  sIntegerMaskPoissonFactor K S r.modulus r.nonzero radius
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
    (((rowRadius r radius D q).val ^ (-δ) : ℝ) : ℂ)

/-- A constant computed before the row is chosen. -/
def rowWeightBound (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (δ : ℝ) : ℝ :=
  ‖sIntegerMaskPoissonFactor K S r.modulus r.nonzero radius
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
    (sIntegerMaskDualRadius K S r.modulus r.nonzero radius
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ^ (-δ)

theorem rowWeightBound_nonneg (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (δ : ℝ) :
    0 ≤ rowWeightBound r radius D δ :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
    (sIntegerMaskDualRadius K S r.modulus r.nonzero radius
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property.le _)

/-- The original norm-one lower bound proves the weight estimate on
all orbital rows, before any physical cutoff. -/
theorem norm_poissonTiltWeight_le (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    (δ : ℝ) (hδ : 0 ≤ δ) (q : Q) :
    ‖poissonTiltWeight r radius D δ q‖ ≤ rowWeightBound r radius D δ := by
  unfold poissonTiltWeight rowWeightBound
  rw [norm_mul, tiltScalar_norm (rowRadius r radius D q).property]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let ρ := sIntegerMaskDualRadius K S r.modulus r.nonzero radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  let N := sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q
  change (ρ.val * N.val) ^ (-δ) ≤ ρ.val ^ (-δ)
  rw [Real.mul_rpow ρ.property.le N.property.le]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_sIntegerOrbitNorm q)
      (neg_nonpos.mpr hδ)) (Real.rpow_nonneg ρ.property.le _)).trans_eq (mul_one _)

theorem norm_maskPoissonFactor (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) :
    ‖sIntegerMaskPoissonFactor K S r.modulus r.nonzero radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ =
      orbitalFieldFactor K *
        (sIntegerMaskDilationRadius K S radius
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val⁻¹ *
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val⁻¹ := by
  let u := sIntegerMaskDilationRadius K S radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  let N := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨r.modulus, r.nonzero⟩
  change ‖(u.val : ℂ)⁻¹ * (orbitalFieldFactor K : ℂ) * (N.val : ℂ)⁻¹‖ =
    orbitalFieldFactor K * u.val⁻¹ * N.val⁻¹
  rw [norm_mul, norm_mul, norm_inv, norm_inv]
  simp only [Complex.norm_real, Real.norm_of_nonneg u.property.le,
    Real.norm_of_nonneg N.property.le, Real.norm_of_nonneg (orbitalFieldFactor_nonneg K)]
  ring

/-- The exact common factor still contains the inverse active norm.
Only the chosen tiny Mellin exponent modifies it. -/
theorem rowWeightBound_eq (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (δ : ℝ) :
    rowWeightBound r radius D δ =
      orbitalFieldFactor K *
        (sIntegerMaskDilationRadius K S radius
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ^ (δ - 1) *
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val ^ (δ - 1) := by
  unfold rowWeightBound
  rw [norm_maskPoissonFactor r radius D]
  let u := sIntegerMaskDilationRadius K S radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  let N := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨r.modulus, r.nonzero⟩
  change (orbitalFieldFactor K * u.val⁻¹ * N.val⁻¹) *
    ((u.val * N.val)⁻¹) ^ (-δ) =
      orbitalFieldFactor K * u.val ^ (δ - 1) * N.val ^ (δ - 1)
  rw [Real.inv_rpow (mul_pos u.property N.property).le,
    Real.rpow_neg (mul_pos u.property N.property).le, inv_inv,
    Real.mul_rpow u.property.le N.property.le,
    Real.rpow_sub_one u.property.ne' δ, Real.rpow_sub_one N.property.ne' δ]
  ring

/-- Multiplying by the actual active Gauss bound retains the active
norm with exponent `δ - 1/2`. -/
theorem rowWeightBound_mul_sqrt_eq (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (δ : ℝ) :
    rowWeightBound r radius D δ *
        Real.sqrt (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val =
      orbitalFieldFactor K *
        (sIntegerMaskDilationRadius K S radius
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ^ (δ - 1) *
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val ^ (δ - 1 / 2) := by
  rw [rowWeightBound_eq r radius D δ, Real.sqrt_eq_rpow, mul_assoc,
    ← Real.rpow_add
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨r.modulus, r.nonzero⟩).property]
  rw [show δ - 1 + (1 / 2 : ℝ) = δ - 1 / 2 by ring]

/-- The additional row Mellin factor is paid by the original mask
dilation and common modulus window.  The original Poisson factor stays
explicit. -/
theorem rowWeightBound_le_of_norm_window (r : OrbitalGaussColumn K S Γ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS))
    {δ Z B : ℝ} (hδ : 0 ≤ δ) (hZ : 0 < Z)
    (hwindow :
      (sIntegerMaskDilationRadius K S radius
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val *
        (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          ⟨r.modulus, r.nonzero⟩).val ≤ Z ^ B) :
    rowWeightBound r radius D δ ≤
      ‖sIntegerMaskPoissonFactor K S r.modulus r.nonzero radius
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ * Z ^ (B * δ) := by
  unfold rowWeightBound
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  let u := sIntegerMaskDilationRadius K S radius
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  let N := sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    ⟨r.modulus, r.nonzero⟩
  change ((u.val * N.val)⁻¹) ^ (-δ) ≤ Z ^ (B * δ)
  rw [Real.inv_rpow (mul_pos u.property N.property).le,
    Real.rpow_neg (mul_pos u.property N.property).le, inv_inv]
  exact tilt_le_of_norm_window (mul_pos u.property N.property) hZ hδ hwindow

end CanonicalFirstLog

section ActualChart

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
variable (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ))
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)

namespace FirstBlockProfileChart

theorem canonicalLog_weight_eq
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    (canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).weight q =
      CanonicalFirstLog.poissonTiltWeight
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) radius D δ q := rfl

theorem canonicalLog_weight_le
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).weight q‖ ≤
      CanonicalFirstLog.rowWeightBound
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) radius D δ := by
  rw [canonicalLog_weight_eq]
  exact CanonicalFirstLog.norm_poissonTiltWeight_le _ _ _ δ hδ.le q

/-- The exact common active saving for the actual first chart. -/
theorem canonicalLog_weight_mul_sqrt_le
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).weight q‖ *
        Real.sqrt (A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ≤
      orbitalFieldFactor K *
        (sIntegerMaskDilationRadius K A.Sf radius
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val ^ (δ - 1) *
        (A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) ^
          (δ - 1 / 2) := by
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  have hN := generates_sIntegerElementNorm
    (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator C b.primes b.leftMultiplicity b.rightMultiplicity)
    (firstActiveGenerator_generates C b.primes b.leftMultiplicity b.rightMultiplicity)
  change (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
    ⟨r.modulus, r.nonzero⟩).val =
      A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) at hN
  calc
    _ ≤ CanonicalFirstLog.rowWeightBound r radius D δ *
        Real.sqrt (A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity)) :=
      mul_le_mul_of_nonneg_right
        (canonicalLog_weight_le hΓ μv ν b C left right φ finiteTest hlc hcs
          radius D δ hδ hδ1 q) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← hN]
      exact CanonicalFirstLog.rowWeightBound_mul_sqrt_eq r radius D δ

theorem canonicalLog_leftCoefficient_norm (i : ι) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).leftCoefficient i‖ = (A.exteriorNorm (b.leftResidual i)) ^ (δ - 1) := by
  exact CanonicalFirstLog.normalizedTiltScalar_norm (A.exteriorNorm_pos _) δ

theorem canonicalLog_rightCoefficient_norm (j : κ) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).rightCoefficient j‖ = (A.exteriorNorm (b.rightResidual j)) ^ (δ - 1) := by
  exact CanonicalFirstLog.normalizedTiltScalar_norm (A.exteriorNorm_pos _) δ

theorem canonicalLog_left_raw_norm (i : ι) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).leftCoefficient i * (A.exteriorNorm (b.leftResidual i) : ℂ)‖ =
      (A.exteriorNorm (b.leftResidual i)) ^ δ := by
  rw [norm_mul, canonicalLog_leftCoefficient_norm, Complex.norm_real,
    Real.norm_of_nonneg (A.exteriorNorm_pos _).le,
    Real.rpow_sub_one (A.exteriorNorm_pos _).ne' δ,
    div_mul_cancel₀ _ (A.exteriorNorm_pos _).ne']

theorem canonicalLog_right_raw_norm (j : κ) :
    ‖(canonicalLog hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1).rightCoefficient j * (A.exteriorNorm (b.rightResidual j) : ℂ)‖ =
      (A.exteriorNorm (b.rightResidual j)) ^ δ := by
  rw [norm_mul, canonicalLog_rightCoefficient_norm, Complex.norm_real,
    Real.norm_of_nonneg (A.exteriorNorm_pos _).le,
    Real.rpow_sub_one (A.exteriorNorm_pos _).ne' δ,
    div_mul_cancel₀ _ (A.exteriorNorm_pos _).ne']

/-- The literal coefficient is in the exact inverse-norm form consumed
by the original prime-pool residual transport. -/
theorem canonicalLogWithCoefficients_leftCoefficient_eq
    (c : ι → ℂ) (e : κ → ℂ) (i : ι) :
    (canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).leftCoefficient i =
      (c i * (((A.exteriorNorm (b.leftResidual i)) ^ δ : ℝ) : ℂ)) /
        (A.exteriorNorm (b.leftResidual i) : ℂ) := by
  change c i *
      ((((A.exteriorNorm (b.leftResidual i)) ^ δ : ℝ) : ℂ) /
        (A.exteriorNorm (b.leftResidual i) : ℂ)) = _
  exact (mul_div_assoc _ _ _).symm

theorem canonicalLogWithCoefficients_rightCoefficient_eq
    (c : ι → ℂ) (e : κ → ℂ) (j : κ) :
    (canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).rightCoefficient j =
      (e j * (((A.exteriorNorm (b.rightResidual j)) ^ δ : ℝ) : ℂ)) /
        (A.exteriorNorm (b.rightResidual j) : ℂ) := by
  change e j *
      ((((A.exteriorNorm (b.rightResidual j)) ^ δ : ℝ) : ℂ) /
        (A.exteriorNorm (b.rightResidual j) : ℂ)) = _
  exact (mul_div_assoc _ _ _).symm

theorem canonicalLogWithCoefficients_leftCoefficient_norm (c : ι → ℂ) (e : κ → ℂ) (i : ι) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).leftCoefficient i‖ =
      ‖c i‖ * (A.exteriorNorm (b.leftResidual i)) ^ (δ - 1) := by
  exact CanonicalFirstLog.scaledNormalizedTiltScalar_norm (A.exteriorNorm_pos _) δ (c i)

theorem canonicalLogWithCoefficients_rightCoefficient_norm (c : ι → ℂ) (e : κ → ℂ) (j : κ) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).rightCoefficient j‖ =
      ‖e j‖ * (A.exteriorNorm (b.rightResidual j)) ^ (δ - 1) := by
  exact CanonicalFirstLog.scaledNormalizedTiltScalar_norm (A.exteriorNorm_pos _) δ (e j)

/-- Recovering the raw coefficient cancels exactly the single inverse
column norm supplied by Poisson. -/
theorem canonicalLogWithCoefficients_left_raw_norm (c : ι → ℂ) (e : κ → ℂ) (i : ι) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).leftCoefficient i * (A.exteriorNorm (b.leftResidual i) : ℂ)‖ =
      ‖c i‖ * (A.exteriorNorm (b.leftResidual i)) ^ δ := by
  let N := A.exteriorNorm (b.leftResidual i)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (A.exteriorNorm_pos (b.leftResidual i)).ne'
  change ‖(c i * (((N ^ δ : ℝ) : ℂ) / (N : ℂ))) * (N : ℂ)‖ = ‖c i‖ * N ^ δ
  rw [mul_assoc, div_mul_cancel₀ _ hN]
  exact CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos _) δ (c i)

theorem canonicalLogWithCoefficients_right_raw_norm (c : ι → ℂ) (e : κ → ℂ) (j : κ) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).rightCoefficient j * (A.exteriorNorm (b.rightResidual j) : ℂ)‖ =
      ‖e j‖ * (A.exteriorNorm (b.rightResidual j)) ^ δ := by
  let N := A.exteriorNorm (b.rightResidual j)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (A.exteriorNorm_pos (b.rightResidual j)).ne'
  change ‖(e j * (((N ^ δ : ℝ) : ℂ) / (N : ℂ))) * (N : ℂ)‖ = ‖e j‖ * N ^ δ
  rw [mul_assoc, div_mul_cancel₀ _ hN]
  exact CanonicalFirstLog.scaledTiltScalar_norm (A.exteriorNorm_pos _) δ (e j)

theorem canonicalLogWithCoefficients_weight_le (c : ι → ℂ) (e : κ → ℂ)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).weight q‖ ≤
      CanonicalFirstLog.rowWeightBound
        (actualActiveColumn hΓ C b.primes b.primes_injective
          b.leftMultiplicity b.rightMultiplicity) radius D δ :=
  canonicalLog_weight_le hΓ μv ν b C left right φ finiteTest hlc hcs radius D δ hδ hδ1 q

/-- Original individual coefficient and norm windows pay the tiny
Mellin power, retaining the true inverse column norm. -/
theorem canonicalLogWithCoefficients_left_norm_le_of_window
    (c : ι → ℂ) (e : κ → ℂ) (i : ι) {Z B C₀ : ℝ} (hZ : 0 < Z)
    (hwindow : A.exteriorNorm (b.leftResidual i) ≤ Z ^ B) (hc : ‖c i‖ ≤ C₀) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).leftCoefficient i‖ ≤
      C₀ * Z ^ (B * δ) / A.exteriorNorm (b.leftResidual i) :=
  CanonicalFirstLog.scaledNormalizedTiltScalar_norm_le_of_window
    (A.exteriorNorm_pos _) hZ hδ.le hwindow (c i) hc

theorem canonicalLogWithCoefficients_right_norm_le_of_window
    (c : ι → ℂ) (e : κ → ℂ) (j : κ) {Z B C₀ : ℝ} (hZ : 0 < Z)
    (hwindow : A.exteriorNorm (b.rightResidual j) ≤ Z ^ B) (hc : ‖e j‖ ≤ C₀) :
    ‖(canonicalLogWithCoefficients hΓ μv ν b C left right φ c e finiteTest hlc hcs
        radius D δ hδ hδ1).rightCoefficient j‖ ≤
      C₀ * Z ^ (B * δ) / A.exteriorNorm (b.rightResidual j) :=
  CanonicalFirstLog.scaledNormalizedTiltScalar_norm_le_of_window
    (A.exteriorNorm_pos _) hZ hδ.le hwindow (e j) hc

end FirstBlockProfileChart
end ActualChart

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.norm_poissonTiltWeight_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.rowWeightBound_mul_sqrt_eq
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLog_weight_mul_sqrt_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLogWithCoefficients_left_raw_norm
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockProfileChart.canonicalLogWithCoefficients_left_norm_le_of_window
