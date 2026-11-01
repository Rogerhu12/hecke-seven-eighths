import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstBlocks
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import Mathlib.Algebra.Group.PUnit

/-!
# The actual parent through the complete first orbital transform

This is a finite-source bridge. Its inputs are pointwise original-source
calibrations and individual transformed-profile charts. The common support
partition, principal mask, complete first finite Fourier factorization,
reciprocity, common physical cutoff, Fourier Cauchy estimate, and uniform
tail comparison are proved by the imported providers. The zero terms
remain additive and each block's tail is counted once.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open UniqueFactorizationMonoid

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
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- A chart for each individual profile, valid on all orbital frequencies.
It assumes no finite transform or summed energy inequality. -/
structure FirstBlockProfileChart {ι κ : Type*}
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (left : Finset ι) (right : Finset κ)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) where
  kernel : 𝓢(E, ℂ)
  weight : Q → ℂ
  leftCoefficient : ι → ℂ
  rightCoefficient : κ → ℂ
  leftPoint : ι → E
  rightPoint : κ → E
  rowPoint : Q → E
  profile : ∀ t : Q, ∀ i ∈ b.leftColumns left, ∀ j ∈ b.rightColumns right,
    IsCoprime (b.leftResidual i).val (b.rightResidual j).val →
    ((generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
        (b.left_generates i)).originalTriple
      (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
        (b.right_generates j))
      (actualActiveColumn hΓ C b.primes b.primes_injective
        b.leftMultiplicity b.rightMultiplicity) (profiles i j)).transformedProfile
          μv finiteTest radius D t =
      weight t * (leftCoefficient i * star (rightCoefficient j)) *
        kernel (rowPoint t + leftPoint i + rightPoint j)

variable {hΓ μv}

def FirstBlockProfileChart.kernelCost {ι κ : Type*}
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    {b : FirstCommonCharacterBlock fullI fullJ DE}
    {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
    {profiles : ι → κ → SchwartzMap V ℂ}
    {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
    {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) : ℝ :=
  let source := b.finiteSource hΓ C left right profiles M radius X hX
  let a := fun i => generatedOriginalColumn (σ := σ) hΓ
    (b.leftResidual i) (b.leftGenerator i) (b.left_generates i)
  let a' := fun j => generatedOriginalColumn (σ := σ) hΓ
    (b.rightResidual j) (b.rightGenerator j) (b.right_generates j)
  let r := actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  firstResidualKernelCost hDiff (PUnit : Type) chart.kernel (source.divisorRows D) (fun t => t.out.val)
    source.leftColumns source.rightColumns
    (fun i => (b.leftResidual i).val) (fun j => (b.rightResidual j).val)
    a a' (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun t : Q => (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
      (r.character (Ideal.Quotient.mk _ δ) *
        actualSIntegerGauss K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff r.modulus r.nonzero r.character t.out.val))
    chart.weight
    (fun i => chart.leftCoefficient i * firstLeftDivisorFactor (a i) r δ)
    (fun j => chart.rightCoefficient j * firstRightDivisorFactor (a' j) r δ)
    chart.leftPoint chart.rightPoint

theorem FirstBlockProfileChart.kernel_bound_of_phase_one {ι κ : Type*}
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    {b : FirstCommonCharacterBlock fullI fullJ DE}
    {C : A.GeneralArithmeticContext σ η hS} {left : Finset ι} {right : Finset κ}
    {profiles : ι → κ → SchwartzMap V ℂ}
    {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
    {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
    (chart : FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (hphase : ∀ i j, IsCoprime (b.leftResidual i).val (b.rightResidual j).val →
      firstReciprocalPhase
        (generatedOriginalColumn (σ := σ) hΓ (b.leftResidual i) (b.leftGenerator i)
          (b.left_generates i))
        (generatedOriginalColumn (σ := σ) hΓ (b.rightResidual j) (b.rightGenerator j)
          (b.right_generates j)) = 1) :
    let source := b.finiteSource hΓ C left right profiles M radius X hX
    ‖∑ t ∈ (source.divisorRows D), ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
      chart.kernelCost hDiff M X hX := by
  exact b.kernel_bound hΓ μv PUnit C hDiff finiteTest left right profiles M radius X hX D
    chart.kernel (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    chart.weight chart.leftCoefficient chart.rightCoefficient
    chart.leftPoint chart.rightPoint chart.rowPoint
    (fun i j hc => by simpa using hphase i j hc)
    (fun t _ i hi j hj hc => chart.profile t i hi j hj hc)

variable (hΓ μv)

theorem canonical_first_block_transform_bound
    (C : A.GeneralArithmeticContext σ η hS)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (profiles : ι → κ → SchwartzMap V ℂ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
    let source := b.finiteSource hΓ C left right profiles M radius X hX
    ∀ charts : ∀ D : (b.mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv b C left right profiles finiteTest radius D.val,
    ‖source.divisorTransform μv hDiff finiteTest‖ ≤
      ‖source.zeroTerm μv hDiff finiteTest‖ +
        ∑ D : (b.mask M).powerset, (charts D).kernelCost hDiff M X hX := by
  dsimp only
  intro charts
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
  let source := b.finiteSource hΓ C left right profiles M radius X hX
  change ‖source.divisorTransform μv hDiff finiteTest‖ ≤ _
  rw [source.divisorTransform_eq_common_rows μv hDiff finiteTest]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ D ∈ source.mask.powerset,
        ‖∑ t ∈ (source.divisorRows D), ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D t‖ :=
      norm_sum_le _ _
    _ = ∑ D : (b.mask M).powerset,
        ‖∑ t ∈ (source.divisorRows D.val), ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D.val t‖ :=
       (Finset.sum_coe_sort (b.mask M).powerset (fun D =>
         ‖∑ t ∈ (source.divisorRows D), ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
           (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D t‖)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D _
      exact (charts D).kernel_bound_of_phase_one hDiff M X hX (fun i j hc =>
        canonicalFirstCommonBlock_phase_one hΓ C left right fullI fullJ DE.val DE.property i j hc)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem parent_first_stage_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (columns : Finset ι) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X),
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ {ω ψ₀ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ₀)
      (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Z t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).zeroTerm μv hDiff finiteTest‖ +
          (∑ D : ((blocks DE).mask M).powerset, (charts DE D).kernelCost hDiff M X hX) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass (sources DE).mask radius) := by
  obtain ⟨seminorms, Ctail, hC, htail⟩ := finite_source_divisor_uniform_bound
    (K := K) (S := A.Sf) (Γ := Γ) ν μv μ hDiff finiteTest hlc hcs
    decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro ι columns fullI afull hafull profiles radius M X hX
  dsimp only
  intro charts ω ψ₀ centered d a Z t Y₁ Y₂ B cal
  let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
      (fun j => (fullI j).val) =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
  let series := fun DE => ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
    ((sources DE).pairs i j).maskedSeries (sIntegerFiniteTestFunction K A.Sf finiteTest)
      radius (sources DE).mask
  have hp := parent_orbital_source_bound (K := K) (S := A.Sf) (Γ := Γ)
    centered d a Z t Y₁ Y₂ columns _
    (sIntegerFiniteTestFunction K A.Sf finiteTest)
    (continuous_sIntegerFiniteTestFunction K A.Sf finiteTest hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf finiteTest hcs) radius M B cal
  rw [common_support_original_sources hΓ C columns columns fullI fullI afull afull
    hafull hafull (fun DE hDE => canonicalFirstCommonBlock C columns columns fullI fullI DE hDE)] at hp
  change pairedStageEnergy centered d a Z t Y₁ Y₂ ≤ (B : ℝ) * (∑ DE, series DE).re at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro DE _
  have ht := htail (sources DE)
  have hk := canonical_first_block_transform_bound hΓ μv C columns columns fullI fullI
    DE profiles hDiff finiteTest M radius X hX (charts DE)
  have hre := Complex.re_le_norm (series DE - (sources DE).divisorTransform μv hDiff finiteTest)
  rw [Complex.sub_re] at hre
  have hfinite := Complex.re_le_norm ((sources DE).divisorTransform μv hDiff finiteTest)
  change (series DE).re ≤ _
  change ‖series DE - (sources DE).divisorTransform μv hDiff finiteTest‖ ≤ _ at ht
  exact ((sub_le_iff_le_add.mp (hre.trans ht)).trans
     (add_le_add le_rfl (hfinite.trans hk))).trans_eq (add_comm _ _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonical_first_block_transform_bound
#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_bound

