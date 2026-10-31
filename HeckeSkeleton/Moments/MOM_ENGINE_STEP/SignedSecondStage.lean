import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonGaussOrigin

/-!
# The second transform with the original-origin sign

The fixed row-ball profile has a positive original tensor at zero.
The Poisson origin is therefore retained with its negative sign while
the complete common-support source is assembled. Its whole Gram square
is nonnegative. Only then are the pure dual zero, nonzero rows, and
original truncation error estimated in norm.

All columns, coefficients, profiles, cutoffs, and Fourier charts are
those of the original source. The empty additional Gauss row mask does
not remove any mask already present in the original coefficients.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The actual common-block transform on real parts. No positivity is
asserted for an individual block's original-origin contribution. -/
theorem canonical_second_block_transform_re_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (profiles : ι → κ → SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ∀ charts : ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right profiles finiteTest radius D.val,
    (source.transform μv hDiff finiteTest).re ≤
      ‖source.dualZeroTerm μv hDiff finiteTest‖ - (source.originZeroTerm finiteTest).re +
        ∑ D : M.powerset, (charts D).kernelCost M X hX := by
  dsimp only
  intro charts
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
  let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
  have hrows :
      ‖∑ D ∈ M.powerset, ∑ t ∈ source.rows,
        ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D t‖ ≤
        ∑ D : M.powerset, (charts D).kernelCost M X hX := by
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
            (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D t‖ :=
        norm_sum_le _ _
      _ = ∑ D : M.powerset,
          ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
            (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D.val t‖ :=
        (Finset.sum_coe_sort _ _).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro D _
        exact (charts D).kernel_bound
          (commonSupportPool_support_eq left right (fun i => (fullI i).val)
            (fun j => (fullJ j).val) DE.val DE.property)
          (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).1
          (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).2 M X hX
  change (source.transform μv hDiff finiteTest).re ≤ _
  rw [source.transform_eq_common_rows μv hDiff finiteTest,
    source.zeroTerm_eq_dual_sub_origin μv hDiff finiteTest]
  simp only [Complex.add_re, Complex.sub_re]
  exact add_le_add (sub_le_sub_right (Complex.re_le_norm _) _)
    ((Complex.re_le_norm _).trans hrows)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- One uniform cutoff estimate for the complete original Gauss energy.
The original-origin sign is used after all common blocks are summed.
The only positivity premise concerns the individual original tensor;
the canonical row-ball test supplies it internally. -/
theorem gauss_second_stage_dual_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ L < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {H ι : Type*} (rows : Finset H) (rowMap : H → Q) (weight : H → ℝ)
      (columns : Finset ι) (c : ι → ℂ) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (hfull : ∀ i ∈ columns, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
      (φ : SchwartzMap V ℂ)
      (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0).re)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (hmask : M = ∅) (X : ℝ) (hX : 1 ≤ X),
    let profiles := fun i j => (c i * star (c j)) • φ
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C
      columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ B : ℕ, GaussEnergyChart rows rowMap weight φ
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).dualZeroTerm μv hDiff finiteTest‖ +
          (∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass M radius) := by
  obtain ⟨seminorms, Ctail, hC, htail⟩ := finite_source_uniform_bound
    (K := K) (S := A.Sf) (Γ := Γ) ν μv μ hDiff finiteTest hlc hcs
    decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro H ι rows rowMap weight columns c fullI afull hafull hfull φ hpositive radius M hmask X hX
  dsimp only
  intro charts B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
      (fun j => (fullI j).val) =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C
    columns columns profiles M radius X hX
  let series := fun DE => ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
    ((sources DE).pairs i j).maskedSeries (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M
  let cost := fun DE =>
    ‖(sources DE).dualZeroTerm μv hDiff finiteTest‖ +
      (∑ D : M.powerset, (charts DE D).kernelCost M X hX) +
      Ctail * X ^ (1 - decay) *
        ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
          seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
            ((sources DE).pairs i j).truncationMass M radius
  have hp := gauss_energy_orbital_source_bound hDiff rows rowMap weight columns c
    (fun i => generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)) φ
    (sIntegerFiniteTestFunction K A.Sf finiteTest)
    (continuous_sIntegerFiniteTestFunction K A.Sf finiteTest hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf finiteTest hcs) radius M B cal
  rw [common_support_gauss_sources hΓ hDiff C Drecipe hD columns columns fullI fullI
    afull afull hafull hafull hfull hfull] at hp
  change weightedEnergy rows weight _ ≤ (B : ℝ) * (∑ DE, series DE).re at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  change (∑ DE, series DE).re ≤ ∑ DE, cost DE
  have hblock (DE) :
      (series DE).re ≤ cost DE - ((sources DE).originZeroTerm finiteTest).re := by
    have ht := htail (sources DE)
    have hk := canonical_second_block_transform_re_bound hΓ μv hDiff C
      columns columns fullI fullI DE profiles finiteTest M radius X hX (charts DE)
    have hre := Complex.re_le_norm (series DE - (sources DE).transform μv hDiff finiteTest)
    rw [Complex.sub_re] at hre
    change ‖series DE - (sources DE).transform μv hDiff finiteTest‖ ≤ _ at ht
    exact ((sub_le_iff_le_add.mp (hre.trans ht)).trans
      (add_le_add le_rfl hk)).trans_eq (by dsimp only [cost]; ring)
  have ho : 0 ≤ (∑ DE, (sources DE).originZeroTerm finiteTest).re := by
    simpa only [sources, hmask] using
      common_support_gauss_origin_nonneg hΓ hDiff C columns c fullI afull hafull
        φ finiteTest hpositive radius X hX
  rw [Complex.re_sum] at ho ⊢
  calc
    _ ≤ ∑ DE, (cost DE - ((sources DE).originZeroTerm finiteTest).re) :=
      Finset.sum_le_sum (fun DE _ => hblock DE)
    _ = (∑ DE, cost DE) - ∑ DE, ((sources DE).originZeroTerm finiteTest).re :=
      Finset.sum_sub_distrib
    _ ≤ _ := sub_le_self _ ho

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.canonical_second_block_transform_re_bound
#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_dual_bound
