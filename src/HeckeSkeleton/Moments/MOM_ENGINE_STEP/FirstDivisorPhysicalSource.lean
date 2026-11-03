import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstFiniteSource

/-!
# A physical first-frequency set for each original mask divisor

Each original divisor keeps its own physical cutoff. Within that divisor,
the cutoff is the maximum over the actual nonzero pair profiles, so the
whole pair polynomial still has one common row set. No column, arithmetic
coefficient, Fourier factor or additive origin is changed.

The uniform truncation proof uses the original orbital Poisson identity
with the cutoff function evaluated at the same divisor. In particular,
a bound for one divisor is never replaced by the maximum over the mask.
-/

noncomputable section
open scoped Classical BigOperators nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
local notation "Q" => SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ

variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The radii belong to the actual current divisor and nonzero pair
profiles. The inserted zero makes the maximum total even on empty blocks. -/
def FirstFiniteSource.divisorInverseRadii {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) : Finset ℝ :=
  insert 0 (((s.leftColumns ×ˢ s.rightColumns).filter
    (fun ij => (s.pairs ij.1 ij.2).profile ≠ 0)).image fun ij =>
      ((s.pairs ij.1 ij.2).dualRadius s.radius D).val⁻¹)

def FirstFiniteSource.divisorInverseRadiusBound {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) : ℝ :=
  (s.divisorInverseRadii D).sup' (Finset.insert_nonempty _ _) id

def FirstFiniteSource.divisorPhysicalCutoff {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) : ℝ :=
  s.cutoff * s.divisorInverseRadiusBound D

theorem FirstFiniteSource.divisorInverseRadiusBound_nonneg {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) :
    0 ≤ s.divisorInverseRadiusBound D :=
  Finset.le_sup' id (Finset.mem_insert_self 0 _)

theorem FirstFiniteSource.divisorInverseRadius_le {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    {i : ι} (hi : i ∈ s.leftColumns) {j : κ} (hj : j ∈ s.rightColumns)
    (D : Finset (HeightOneSpectrum OS)) (hprofile : (s.pairs i j).profile ≠ 0) :
    ((s.pairs i j).dualRadius s.radius D).val⁻¹ ≤ s.divisorInverseRadiusBound D := by
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(i, j),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hprofile⟩, rfl⟩

theorem FirstFiniteSource.divisorScaledCutoff_ge {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    {i : ι} (hi : i ∈ s.leftColumns) {j : κ} (hj : j ∈ s.rightColumns)
    (D : Finset (HeightOneSpectrum OS)) (hprofile : (s.pairs i j).profile ≠ 0) :
    s.cutoff ≤ ((s.pairs i j).dualRadius s.radius D).val * s.divisorPhysicalCutoff D := by
  let ρ := (s.pairs i j).dualRadius s.radius D
  have hi' : ρ.val⁻¹ ≤ s.divisorInverseRadiusBound D :=
    s.divisorInverseRadius_le hi hj D hprofile
  have hmul := mul_le_mul_of_nonneg_left hi' ρ.property.le
  rw [mul_inv_cancel₀ (ne_of_gt ρ.property)] at hmul
  calc
    s.cutoff = s.cutoff * 1 := (mul_one _).symm
    _ ≤ s.cutoff * (ρ.val * s.divisorInverseRadiusBound D) :=
      mul_le_mul_of_nonneg_left hmul (zero_le_one.trans s.cutoff_ge_one)
    _ = ρ.val * s.divisorPhysicalCutoff D := by
      unfold FirstFiniteSource.divisorPhysicalCutoff
      ring

/-- An actual fixed-divisor window controls its own physical cutoff. -/
theorem FirstFiniteSource.divisorPhysicalCutoff_le_supported {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS))
    (R : ℝ) (hR : 0 ≤ R)
    (hradii : ∀ i ∈ s.leftColumns, ∀ j ∈ s.rightColumns,
      (s.pairs i j).profile ≠ 0 → ((s.pairs i j).dualRadius s.radius D).val⁻¹ ≤ R) :
    s.divisorPhysicalCutoff D ≤ s.cutoff * R := by
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans s.cutoff_ge_one)
  apply Finset.sup'_le
  intro t ht
  rcases Finset.mem_insert.mp ht with h | h
  · simpa only [id_eq, h] using hR
  · obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hmem, hprofile⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    exact hradii ij.1 hi ij.2 hj hprofile

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]

/-- All subgroup sectors remain in the original fixed-divisor cutoff. -/
def FirstFiniteSource.divisorRows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) : Finset Q :=
  sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ (s.divisorPhysicalCutoff D)

@[simp] theorem FirstFiniteSource.mem_divisorRows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS)) (q : Q) :
    q ∈ s.divisorRows D ↔
      (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val ≤
        s.divisorPhysicalCutoff D := by
  simp only [FirstFiniteSource.divisorRows, sIntegerOrbitCutoff,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq, one_mul]

theorem FirstFiniteSource.divisorRows_empty_of_subunit {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ) (D : Finset (HeightOneSpectrum OS))
    (hH : s.divisorPhysicalCutoff D < 1) : s.divisorRows D = ∅ := by
  ext q
  constructor
  · intro hq
    exact False.elim ((not_lt_of_ge
      ((one_le_sIntegerOrbitNorm q).trans ((s.mem_divisorRows D q).mp hq))) hH)
  · intro hq
    simp at hq

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

def ParentPeriodicPair.divisorPhysicalTransform (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : Finset (HeightOneSpectrum OS) → ℝ) : ℂ :=
  ∑ D ∈ M.powerset, (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
      (∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ (H D),
        sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
          p.modulus p.modulus_ne_zero p.residue p.invariant
          (sIntegerMaskGenerator K _ D).val (p.dualRadius r D) q) +
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r (sIntegerMaskGenerator K _ D) *
            (sIntegerPeriodicDivisorFourier K _ hS p.modulus p.modulus_ne_zero p.residue
                (sIntegerMaskGenerator K _ D).val 0 *
              sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K p.profile) h 0) -
          p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0))

theorem ParentPeriodicPair.divisorPhysicalTransform_eq (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : Finset (HeightOneSpectrum OS) → ℝ) :
    p.divisorPhysicalTransform μv hS h M r H =
      (∑ D ∈ M.powerset, p.transformedZero μv hS h r D) +
      ∑ D ∈ M.powerset, ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ (H D),
        p.transformedRow μv hS h r D q := by
  unfold ParentPeriodicPair.divisorPhysicalTransform ParentPeriodicPair.transformedZero
    ParentPeriodicPair.transformedRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _
  simp only [← Finset.mul_sum]
  ring

include ν μ in
theorem ParentPeriodicPair.divisorPhysicalTransform_error (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : Finset (HeightOneSpectrum OS) → ℝ) :
    p.maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        p.divisorPhysicalTransform μv hS h M r H =
      ∑ D ∈ M.powerset,
        let F := sIntegerPeriodicFourierProfileTerm K S Γ μv hS h p.profile
          p.modulus p.modulus_ne_zero p.residue p.invariant
          (sIntegerMaskGenerator K _ D).val (p.dualRadius r D)
        (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
          sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
            (sIntegerMaskGenerator K _ D) *
          ((∑' q : Q, F q) -
            ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ (H D), F q) := by
  rw [p.maskedSeries_eq_firstTransform ν μv μ hS h hlc hcs M r]
  unfold ParentPeriodicPair.firstTransform ParentPeriodicPair.divisorPhysicalTransform
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D _
  dsimp only
  unfold sIntegerWeightedOrbitalSeries sIntegerPeriodicFourierProfileTerm
    ParentPeriodicPair.dualRadius
  ring

include ν μ in
/-- A zero original profile contributes no physical truncation error,
at every common cutoff, including a cutoff below one. -/
theorem ParentPeriodicPair.divisorPhysicalTransform_error_zero (p : ParentPeriodicPair K S Γ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : Finset (HeightOneSpectrum OS) → ℝ)
    (hprofile : p.profile = 0) :
    p.maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        p.divisorPhysicalTransform μv hS h M r H = 0 := by
  rw [p.divisorPhysicalTransform_error ν μv μ hS h hlc hcs M r H]
  have hfourier : traceSchwartzFourier K (0 : SchwartzMap V ℂ) = 0 := by
    simpa only [traceSchwartzFourierCLM_apply] using (traceSchwartzFourierCLM K).map_zero
  have horbital (ρ : {r : ℝ // 0 < r}) :
      sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
          (0 : SchwartzMap V ℂ) (sIntegerFiniteFourierTestFunction K S μv h)) ρ = 0 := by
    simpa only [zero_smul] using
      sUnitOrbitalProfile_tensor_smul K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerFiniteFourierTestFunction K S μv h) (0 : ℂ) (0 : SchwartzMap V ℂ) ρ
  simp only [sIntegerPeriodicFourierProfileTerm, hprofile, hfourier, horbital,
    mul_zero, tsum_zero, Finset.sum_const_zero, sub_self]

include ν μ in
/-- Uniform pairwise comparison at a physical cutoff function satisfying
the actual same-divisor radius inequalities.  The constants precede both cutoff scales
and every original profile, residue coefficient, modulus, and mask. -/
theorem divisor_physical_transform_uniform_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∀ H : Finset (HeightOneSpectrum OS) → ℝ, ∀ p : ParentPeriodicPair K S Γ,
      ∀ M : Finset (HeightOneSpectrum OS), ∀ r : {r : ℝ // 0 < r},
      (∀ D ∈ M.powerset, X ≤ (p.dualRadius r D).val * H D) →
      ‖p.maskedSeries (sIntegerFiniteTestFunction K S h) r M -
        p.divisorPhysicalTransform μv hS h M r H‖ ≤
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
      ∑ q ∈ sIntegerOrbitCutoff K S Γ ⟨1, zero_lt_one⟩ (H D), F q
  have he (D : Finset (HeightOneSpectrum OS)) (hD : D ∈ M.powerset) : ‖e D‖ ≤
      sIntegerPeriodicResidueL1 K (S : Set (HeightOneSpectrum (𝓞 K)))
        p.modulus p.modulus_ne_zero
        (fun a => p.residue (Ideal.Quotient.mk _ (sIntegerMaskGenerator K _ D).val * a)) *
      C * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
        (1 + (p.dualRadius r D).val⁻¹) * X ^ (1 - decay) := by
    have hb := (htail p.modulus p.modulus_ne_zero p.residue p.invariant
      (sIntegerMaskGenerator K _ D).val p.profile (p.dualRadius r D)
      ((p.dualRadius r D).val * H D) (hX.trans (hscaled D hD))).2.2
    rw [orbitCutoff_mul_radius] at hb
    have hpow : ((p.dualRadius r D).val * H D) ^ (1 - decay) ≤ X ^ (1 - decay) :=
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
  rw [p.divisorPhysicalTransform_error ν μv μ hS h hlc hcs M r H]
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

def FirstFiniteSource.divisorTransform {ι κ : Type*} (s : FirstFiniteSource K S Γ ι κ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℂ :=
  ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
    (s.pairs i j).divisorPhysicalTransform μv hS h s.mask s.radius s.divisorPhysicalCutoff

/-- Exact finite reindexing places the same-divisor row set before the
whole column pair sum.  No row-dependent column indicator is introduced. -/
theorem FirstFiniteSource.divisorTransform_eq_common_rows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    s.divisorTransform μv hS h = s.zeroTerm μv hS h +
      ∑ D ∈ s.mask.powerset, ∑ q ∈ s.divisorRows D,
        ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
          (s.pairs i j).transformedRow μv hS h s.radius D q := by
  unfold FirstFiniteSource.divisorTransform
  simp only [ParentPeriodicPair.divisorPhysicalTransform_eq, Finset.sum_add_distrib]
  change s.zeroTerm μv hS h +
    (∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
      ∑ D ∈ s.mask.powerset, ∑ q ∈ s.divisorRows D,
        (s.pairs i j).transformedRow μv hS h s.radius D q) = _
  congr 1
  calc
    _ = ∑ i ∈ s.leftColumns, ∑ D ∈ s.mask.powerset,
          ∑ j ∈ s.rightColumns, ∑ q ∈ s.divisorRows D,
            (s.pairs i j).transformedRow μv hS h s.radius D q := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ D ∈ s.mask.powerset, ∑ i ∈ s.leftColumns,
          ∑ j ∈ s.rightColumns, ∑ q ∈ s.divisorRows D,
            (s.pairs i j).transformedRow μv hS h s.radius D q := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      calc
        _ = ∑ i ∈ s.leftColumns, ∑ q ∈ s.divisorRows D, ∑ j ∈ s.rightColumns,
              (s.pairs i j).transformedRow μv hS h s.radius D q := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

include ν μ in
/-- The actual finite rectangular source has a common row set within each divisor and a
uniformly certified tail.  There is no whole-source comparison hypothesis. -/
theorem finite_source_divisor_uniform_bound
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
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
        s.divisorTransform μv hS h‖ ≤
        C * s.cutoff ^ (1 - decay) *
          ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (s.pairs i j).profile *
              (s.pairs i j).truncationMass s.mask s.radius := by
  obtain ⟨seminorms, C, hC, hbound⟩ := divisor_physical_transform_uniform_bound (K := K) (S := S) (Γ := Γ)
    ν μv μ hS h hlc hcs decay hdecay order horder hdegree
  refine ⟨seminorms, C, hC, ?_⟩
  intro ι κ s
  unfold FirstFiniteSource.divisorTransform
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
        ‖(s.pairs i j).maskedSeries (sIntegerFiniteTestFunction K S h) s.radius s.mask -
          (s.pairs i j).divisorPhysicalTransform μv hS h s.mask s.radius s.divisorPhysicalCutoff‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_sum_le _ _)
    _ ≤ ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
        C * s.cutoff ^ (1 - decay) *
          (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (s.pairs i j).profile *
            (s.pairs i j).truncationMass s.mask s.radius) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hp : (s.pairs i j).profile = 0
      · rw [(s.pairs i j).divisorPhysicalTransform_error_zero ν μv μ hS h hlc hcs
          s.mask s.radius s.divisorPhysicalCutoff hp, hp]
        simp only [norm_zero, map_zero, zero_mul, mul_zero, le_refl]
      · exact hbound s.cutoff s.cutoff_ge_one s.divisorPhysicalCutoff (s.pairs i j) s.mask s.radius
          (fun D hD => s.divisorScaledCutoff_ge hi hj D hp)
    _ = _ := by simp only [Finset.mul_sum]

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.divisorPhysicalCutoff_le_supported
#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.mem_divisorRows
#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.divisorPhysicalTransform_error
#print axioms HeckeSkeleton.Moments.EngineStep.divisor_physical_transform_uniform_bound
#print axioms HeckeSkeleton.Moments.EngineStep.finite_source_divisor_uniform_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.divisorTransform_eq_common_rows
