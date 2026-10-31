import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentTruncation

/-!
# One physical frequency set for the whole finite source

A common normalized tail parameter does not give a common set of frequencies:
the dual radius depends on the column pair and on the mask divisor.  This file
uses the maximum of the actual inverse radii.  All pairs and divisors then have
the same finite set of subgroup orbits, without a column-dependent sharp
indicator in their archimedean kernel.  Taking a maximum, rather than a sum,
also avoids introducing an artificial column-count factor in the row length.

The source record contains only the original finite columns, their individual
periodic pair data, a mask, a radius, and a tail parameter.  Every transformed
summand, radius, frequency, and additive zero term is computed from these data.
The comparison theorem applies to an arbitrary rectangular pair matrix.  In
particular it can be used both for the original parent and for a whole Gauss
polynomial produced by the one prime-pool operation.
-/

noncomputable section
open scoped Classical BigOperators nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- Original data for a rectangular finite source.  In an application this
record is formed on each actual common-support rectangle. -/
structure FirstFiniteSource (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
    (ι κ : Type*) where
  leftColumns : Finset ι
  rightColumns : Finset κ
  pairs : ι → κ → ParentPeriodicPair K S Γ
  mask : Finset (HeightOneSpectrum
    (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))
  radius : {r : ℝ // 0 < r}
  cutoff : ℝ
  cutoff_ge_one : 1 ≤ cutoff

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

def ParentPeriodicPair.dualRadius (p : ParentPeriodicPair K S Γ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) :
    {ρ : ℝ // 0 < ρ} :=
  sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero r
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)

def FirstFiniteSource.branches {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ) :
    Finset ((ι × κ) × Finset (HeightOneSpectrum OS)) :=
  (s.leftColumns ×ˢ s.rightColumns) ×ˢ s.mask.powerset

def FirstFiniteSource.inverseRadii {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ) :
    Finset ℝ :=
  insert 1 (s.branches.image fun e =>
    ((s.pairs e.1.1 e.1.2).dualRadius s.radius e.2).val⁻¹)

def FirstFiniteSource.inverseRadiusBound {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) : ℝ :=
  s.inverseRadii.sup' (by exact Finset.insert_nonempty _ _) id

def FirstFiniteSource.physicalCutoff {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) : ℝ :=
  s.cutoff * s.inverseRadiusBound

theorem FirstFiniteSource.one_le_inverseRadiusBound {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) : 1 ≤ s.inverseRadiusBound := by
  exact Finset.le_sup' id (Finset.mem_insert_self 1 _)

theorem FirstFiniteSource.inverseRadius_le {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    {i : ι} (hi : i ∈ s.leftColumns) {j : κ} (hj : j ∈ s.rightColumns)
    {D : Finset (HeightOneSpectrum OS)} (hD : D ∈ s.mask.powerset) :
    ((s.pairs i j).dualRadius s.radius D).val⁻¹ ≤ s.inverseRadiusBound := by
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨((i, j), D),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hD⟩, rfl⟩

theorem FirstFiniteSource.scaledCutoff_ge {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    {i : ι} (hi : i ∈ s.leftColumns) {j : κ} (hj : j ∈ s.rightColumns)
    {D : Finset (HeightOneSpectrum OS)} (hD : D ∈ s.mask.powerset) :
    s.cutoff ≤ ((s.pairs i j).dualRadius s.radius D).val * s.physicalCutoff := by
  let ρ := (s.pairs i j).dualRadius s.radius D
  have hi' : ρ.val⁻¹ ≤ s.inverseRadiusBound := s.inverseRadius_le hi hj hD
  have hmul := mul_le_mul_of_nonneg_left hi' ρ.property.le
  rw [mul_inv_cancel₀ (ne_of_gt ρ.property)] at hmul
  calc
    s.cutoff = s.cutoff * 1 := (mul_one _).symm
    _ ≤ s.cutoff * (ρ.val * s.inverseRadiusBound) :=
      mul_le_mul_of_nonneg_left hmul (zero_le_one.trans s.cutoff_ge_one)
    _ = ρ.val * s.physicalCutoff := by
      unfold FirstFiniteSource.physicalCutoff
      ring

/-- A uniform dyadic upper bound for the actual inverse radii bounds the
common physical length without multiplying by the number of columns. -/
theorem FirstFiniteSource.physicalCutoff_le {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (R : ℝ) (hR : 1 ≤ R)
    (hradii : ∀ i ∈ s.leftColumns, ∀ j ∈ s.rightColumns,
      ∀ D ∈ s.mask.powerset, ((s.pairs i j).dualRadius s.radius D).val⁻¹ ≤ R) :
    s.physicalCutoff ≤ s.cutoff * R := by
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans s.cutoff_ge_one)
  apply Finset.sup'_le
  intro t ht
  rcases Finset.mem_insert.mp ht with h | h
  · simpa only [id_eq, h] using hR
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hij, hD⟩ := Finset.mem_product.mp he
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    exact hradii e.1.1 hi e.1.2 hj e.2 hD

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]

/-- The same actual finite orbit set for every pair and every mask divisor.
All subgroup sectors remain present. -/
def FirstFiniteSource.rows {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ) : Finset Q :=
  sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ s.physicalCutoff

@[simp] theorem FirstFiniteSource.mem_rows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (q : Q) :
    q ∈ s.rows ↔
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤
        s.physicalCutoff := by
  simp only [FirstFiniteSource.rows, sIntegerOrbitCutoff,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq, one_mul]

theorem orbitCutoff_mul_radius (ρ : {r : ℝ // 0 < r}) (H : ℝ) :
    sIntegerOrbitCutoff K S Γ ρ (ρ.val * H) =
      sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ H := by
  ext q
  simp only [sIntegerOrbitCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, one_mul]
  exact mul_le_mul_iff_right₀ ρ.property

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

/-- A genuinely finite expression with a common physical orbit cutoff.
The mask divisor, full finite Fourier coefficient, and two zero terms are
the literal terms of the orbital Poisson provider. -/
def ParentPeriodicPair.physicalTransform (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
      (∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ H,
        sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
          p.modulus p.modulus_ne_zero p.residue p.invariant
          (sIntegerMaskGenerator K _ D).val (p.dualRadius r D) q) +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
            (sIntegerPeriodicDivisorFourier K _ hS p.modulus p.modulus_ne_zero p.residue
                (sIntegerMaskGenerator K _ D).val 0 *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K p.profile) h 0) -
          p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0))

/-- The literal nonzero row of a mask-divisor branch, including its actual
Möbius and Poisson factors. -/
def ParentPeriodicPair.transformedRow (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) (q : Q) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
    sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
      p.modulus p.modulus_ne_zero p.residue p.invariant
      (sIntegerMaskGenerator K _ D).val (p.dualRadius r D) q

/-- Both actual additive zero terms, before any estimate or deletion. -/
def ParentPeriodicPair.transformedZero (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
    (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
      (sIntegerPeriodicDivisorFourier K _ hS p.modulus p.modulus_ne_zero p.residue
          (sIntegerMaskGenerator K _ D).val 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K p.profile) h 0) -
      p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0)

theorem ParentPeriodicPair.physicalTransform_eq (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    p.physicalTransform μv hS h M r H =
      (∑ D ∈ M.powerset, p.transformedZero μv hS h r D) +
      ∑ D ∈ M.powerset, ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ H,
        p.transformedRow μv hS h r D q := by
  unfold ParentPeriodicPair.physicalTransform ParentPeriodicPair.transformedZero
    ParentPeriodicPair.transformedRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _
  simp only [← Finset.mul_sum]
  ring

include ν μ in
theorem ParentPeriodicPair.physicalTransform_error (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : ℝ) :
    p.maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        p.physicalTransform μv hS h M r H =
      ∑ D ∈ M.powerset,
        let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
          p.modulus p.modulus_ne_zero p.residue p.invariant
          (sIntegerMaskGenerator K _ D).val (p.dualRadius r D)
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
          sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
            (sIntegerMaskGenerator K _ D) *
          ((∑' q : Q, F q) -
            ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ H, F q) := by
  rw [p.maskedSeries_eq_firstTransform ν μv μ hS h hlc hcs M r]
  unfold ParentPeriodicPair.firstTransform ParentPeriodicPair.physicalTransform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D _
  dsimp only
  unfold sIntegerWeightedOrbitalSeries sIntegerPeriodicFourierProfileTerm
    ParentPeriodicPair.dualRadius
  ring

include ν μ in
/-- Uniform pairwise comparison at any common physical cutoff satisfying
the actual radius inequalities.  The constants precede both cutoff scales
and every original profile, residue coefficient, modulus, and mask. -/
theorem physical_transform_uniform_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∀ H : ℝ, ∀ p : ParentPeriodicPair K S Γ,
      ∀ M : Finset (HeightOneSpectrum OS), ∀ r : {r : ℝ // 0 < r},
      (∀ D ∈ M.powerset, X ≤ (p.dualRadius r D).val * H) →
      ‖p.maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        p.physicalTransform μv hS h M r H‖ ≤
        C * X ^ (1 - decay) *
          (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
            p.truncationMass M r) := by
  obtain ⟨seminorms, C, hC, htail⟩ := exists_sIntegerPeriodicFourier_truncation_bound
    K S Γ ν μv hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro X hX H p M r hscaled
  let e : Finset (HeightOneSpectrum OS) → ℂ := fun D =>
    let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
      p.modulus p.modulus_ne_zero p.residue p.invariant
      (sIntegerMaskGenerator K _ D).val (p.dualRadius r D)
    (∑' q : Q, F q) -
      ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ H, F q
  have he (D : Finset (HeightOneSpectrum OS)) (hD : D ∈ M.powerset) : ‖e D‖ ≤
      sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
        p.modulus p.modulus_ne_zero
        (fun a => p.residue (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
      C * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
        (1 + (p.dualRadius r D).val⁻¹) * X ^ (1 - decay) := by
    have hb := (htail p.modulus p.modulus_ne_zero p.residue p.invariant
      (sIntegerMaskGenerator K _ D).val p.profile (p.dualRadius r D)
      ((p.dualRadius r D).val * H) (hX.trans (hscaled D hD))).2.2
    rw [orbitCutoff_mul_radius] at hb
    have hpow : ((p.dualRadius r D).val * H) ^ (1 - decay) ≤ X ^ (1 - decay) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hX) (hscaled D hD)
        (by linarith)
    have hmass : 0 ≤
        sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
          p.modulus p.modulus_ne_zero
          (fun a => p.residue (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
        C * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
          (1 + (p.dualRadius r D).val⁻¹) :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (sIntegerPeriodicResidueL1_nonneg K _ p.modulus p.modulus_ne_zero _) hC)
          (apply_nonneg _ _))
        (add_nonneg zero_le_one (inv_nonneg.mpr (p.dualRadius r D).property.le))
    exact hb.trans (mul_le_mul_of_nonneg_left hpow hmass)
  rw [p.physicalTransform_error ν μv μ hS h hlc hcs M r H]
  change ‖∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
      (sIntegerMaskGenerator K _ D) * e D‖ ≤ _
  calc
    _ ≤ ∑ D ∈ M.powerset,
        ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
        ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
          (sIntegerMaskGenerator K _ D)‖ * ‖e D‖ := by
      simpa only [norm_mul] using norm_sum_le M.powerset
        (fun D => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
          sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
            (sIntegerMaskGenerator K _ D) * e D)
    _ ≤ ∑ D ∈ M.powerset,
        ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
        ‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
          (sIntegerMaskGenerator K _ D)‖ *
        (sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
          p.modulus p.modulus_ne_zero
          (fun a => p.residue (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
        C * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
          (1 + (p.dualRadius r D).val⁻¹) * X ^ (1 - decay)) := by
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left (he D hD) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      unfold ParentPeriodicPair.truncationMass sIntegerMaskedTruncationMass
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      unfold ParentPeriodicPair.dualRadius
      ring

/-- Actual finite first-transform expression of a rectangular source. -/
def FirstFiniteSource.transform {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℂ :=
  ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
    (s.pairs i j).physicalTransform μv hS h s.mask s.radius s.physicalCutoff

def FirstFiniteSource.zeroTerm {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℂ :=
  ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns, ∑ D ∈ s.mask.powerset,
    (s.pairs i j).transformedZero μv hS h s.radius D

/-- Exact finite reindexing places the single common row set before the
whole column pair sum.  No row-dependent column indicator is introduced. -/
theorem FirstFiniteSource.transform_eq_common_rows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    s.transform μv hS h = s.zeroTerm μv hS h +
      ∑ D ∈ s.mask.powerset, ∑ q ∈ s.rows,
        ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
          (s.pairs i j).transformedRow μv hS h s.radius D q := by
  unfold FirstFiniteSource.transform
  simp only [ParentPeriodicPair.physicalTransform_eq, Finset.sum_add_distrib]
  change s.zeroTerm μv hS h +
    (∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
      ∑ D ∈ s.mask.powerset, ∑ q ∈ s.rows,
        (s.pairs i j).transformedRow μv hS h s.radius D q) = _
  congr 1
  calc
    _ = ∑ i ∈ s.leftColumns, ∑ D ∈ s.mask.powerset,
          ∑ j ∈ s.rightColumns, ∑ q ∈ s.rows,
            (s.pairs i j).transformedRow μv hS h s.radius D q := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ D ∈ s.mask.powerset, ∑ i ∈ s.leftColumns,
          ∑ j ∈ s.rightColumns, ∑ q ∈ s.rows,
            (s.pairs i j).transformedRow μv hS h s.radius D q := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      calc
        _ = ∑ i ∈ s.leftColumns, ∑ q ∈ s.rows, ∑ j ∈ s.rightColumns,
              (s.pairs i j).transformedRow μv hS h s.radius D q := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

include ν μ in
/-- The actual finite rectangular source has a common row set and a
uniformly certified tail.  There is no whole-source comparison hypothesis. -/
theorem finite_source_uniform_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ),
      ‖(∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
          (s.pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) s.radius s.mask) -
        s.transform μv hS h‖ ≤
        C * s.cutoff ^ (1 - decay) *
          ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (s.pairs i j).profile *
              (s.pairs i j).truncationMass s.mask s.radius := by
  obtain ⟨seminorms, C, hC, hbound⟩ := physical_transform_uniform_bound
    ν μv μ hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro ι κ s
  unfold FirstFiniteSource.transform
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
        ‖(s.pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) s.radius s.mask -
          (s.pairs i j).physicalTransform μv hS h s.mask s.radius s.physicalCutoff‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_sum_le _ _)
    _ ≤ ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
        C * s.cutoff ^ (1 - decay) *
          (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (s.pairs i j).profile *
            (s.pairs i j).truncationMass s.mask s.radius) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hbound s.cutoff s.cutoff_ge_one s.physicalCutoff (s.pairs i j) s.mask s.radius
        (fun D hD => s.scaledCutoff_ge hi hj hD)
    _ = _ := by simp only [Finset.mul_sum]

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.physical_transform_uniform_bound
#print axioms HeckeSkeleton.Moments.EngineStep.finite_source_uniform_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.transform_eq_common_rows
