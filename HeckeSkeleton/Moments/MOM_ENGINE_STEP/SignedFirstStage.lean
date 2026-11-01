import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonFirstOrigin
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstPooledStage

/-!
# The first transform with the original-origin sign

The first common-support sources retain their actual principal masks.
Their original-origin terms are summed before applying positivity of the
original complete Gram source.  The fixed canonical row-ball tensor is
positive at zero, so no annularity condition is imposed on the test.

The first output retains each actual mask divisor and its full finite
nonzero row sum.  The subsequent pool estimate is derived from that same
source and does not alter either the columns or the row set.  The only
profile identities below concern individual original Gram profiles;
the canonical original source supplies them by construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

section RawRows

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The complete finite rows for each actual original mask divisor.
There is no replacement by a post-Cauchy kernel cost in this definition. -/
def FirstFiniteSource.rawRowCost {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℝ :=
  ∑ D : s.mask.powerset,
    ‖∑ t ∈ s.divisorRows D.val, ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
      (s.pairs i j).transformedRow μv hDiff finiteTest s.radius D.val t‖

/-- The genuine finite transform retains its original-origin sign
before any nonzero row is assigned to an ordinary or exceptional class. -/
theorem FirstFiniteSource.divisorTransform_re_le_dual_rows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (s.divisorTransform μv hDiff h).re ≤
      ‖s.dualZeroTerm μv hDiff h‖ - (s.originZeroTerm h).re +
        ∑ D : s.mask.powerset,
          ‖∑ t ∈ s.divisorRows D.val, ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
            (s.pairs i j).transformedRow μv hDiff h s.radius D.val t‖ := by
  rw [s.divisorTransform_eq_common_rows μv hDiff h,
    s.zeroTerm_eq_dual_sub_origin μv hDiff h]
  simp only [Complex.add_re, Complex.sub_re]
  apply add_le_add (sub_le_sub_right (Complex.re_le_norm _) _)
  apply (Complex.re_le_norm _).trans
  calc
    _ ≤ ∑ D ∈ s.mask.powerset,
        ‖∑ t ∈ s.divisorRows D, ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
          (s.pairs i j).transformedRow μv hDiff h s.radius D t‖ := norm_sum_le _ _
    _ = _ := (Finset.sum_coe_sort _ _).symm

end RawRows

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

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The true first orbital transform, with its complete raw finite row
carrier and only the pure dual zero in the positive terminal budget.
The original zero is a proved whole-source square, not an input bound. -/
theorem parent_first_stage_dual_raw_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
      (fullI : ι → A.Exterior) (afull : ι → A.R)
      (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ)
      (hprofiles : ∀ i j, profiles i j =
        (coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K A.Sf rowBallSize)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (X : ℝ) (hX : 1 ≤ X),
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Z t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf rowBallSize)) radius M B →
    pairedStageEnergy centered d a Z t Y₁ Y₂ ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).dualZeroTerm μv hDiff (rowBallFiniteFamily K A.Sf rowBallSize)‖ +
          (sources DE).rawRowCost μv hDiff (rowBallFiniteFamily K A.Sf rowBallSize) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass (sources DE).mask radius) := by
  let finiteTest := rowBallFiniteFamily K A.Sf rowBallSize
  have hlc := rowBallFiniteFamily_locallyConstant K A.Sf rowBallSize
  have hcs := rowBallFiniteFamily_compactSupport K A.Sf rowBallSize
  obtain ⟨seminorms, Ctail, hC, htail⟩ := finite_source_divisor_uniform_bound
    (K := K) (S := A.Sf) (Γ := Γ) ν μv μ hDiff finiteTest hlc hcs
    decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro ι columns coefficient fullI afull hafull profiles hprofiles radius M X hX
  dsimp only
  intro ω ψ centered d a Z t Y₁ Y₂ B cal
  let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
      (fun j => (fullI j).val) =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
  let series := fun DE => ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
    ((sources DE).pairs i j).maskedSeries (sIntegerFiniteTestFunction K A.Sf finiteTest)
      radius (sources DE).mask
  let cost := fun DE =>
    ‖(sources DE).dualZeroTerm μv hDiff finiteTest‖ +
      (sources DE).rawRowCost μv hDiff finiteTest +
      Ctail * X ^ (1 - decay) *
        ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
          seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
            ((sources DE).pairs i j).truncationMass (sources DE).mask radius
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
  change (∑ DE, series DE).re ≤ ∑ DE, cost DE
  have hblock (DE) :
      (series DE).re ≤ cost DE - ((sources DE).originZeroTerm finiteTest).re := by
    have ht := htail (sources DE)
    have hk := (sources DE).divisorTransform_re_le_dual_rows μv hDiff finiteTest
    have hre := Complex.re_le_norm (series DE - (sources DE).divisorTransform μv hDiff finiteTest)
    rw [Complex.sub_re] at hre
    change ‖series DE - (sources DE).divisorTransform μv hDiff finiteTest‖ ≤ _ at ht
    exact ((sub_le_iff_le_add.mp (hre.trans ht)).trans
      (add_le_add le_rfl hk)).trans_eq (by
        dsimp only [cost, FirstFiniteSource.rawRowCost]
        ring)
  have hprofiles' : profiles = fun i j =>
      (coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K A.Sf rowBallSize :=
    funext fun i => funext fun j => hprofiles i j
  have ho : 0 ≤ (∑ DE, (sources DE).originZeroTerm finiteTest).re := by
    dsimp only [sources]
    rw [hprofiles']
    exact common_support_canonical_original_origin_nonneg hΓ C columns fullI afull hafull
      (fun DE hDE => canonicalFirstCommonBlock C columns columns fullI fullI DE hDE)
      coefficient rowBallSize radius M X hX
  rw [Complex.re_sum] at ho ⊢
  calc
    _ ≤ ∑ DE, (cost DE - ((sources DE).originZeroTerm finiteTest).re) :=
      Finset.sum_le_sum (fun DE _ => hblock DE)
    _ = (∑ DE, cost DE) - ∑ DE, ((sources DE).originZeroTerm finiteTest).re :=
      Finset.sum_sub_distrib
    _ ≤ _ := sub_le_self _ ho

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

include ν μ in
/-- The same signed first source followed by its single actual prime
pool.  The original finite row cost is bounded by the existing genuine
Fourier chart and pool providers only at this final step. -/
theorem parent_first_stage_pool_dual_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (rowBallSize : ℝ) (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ Lattice < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ (Zpool ell eps : ℝ) (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (P : PowerScaleExteriorPool A bad Zpool ell eps),
    ∀ {ι : Type*} (columns : Finset ι) (coefficient : ι → ℂ)
      (fullI : ι → A.Exterior) (afull : ι → A.R)
      (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (profiles : ι → ι → SchwartzMap V ℂ)
      (hprofiles : ∀ i j, profiles i j =
        (coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K A.Sf rowBallSize)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (X : ℝ) (hX : 1 ≤ X),
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).finiteSource hΓ C columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockProfileChart (E := E) hΓ μv (blocks DE) C columns columns profiles
        (rowBallFiniteFamily K A.Sf rowBallSize) radius D.val,
    ∀ pools : ∀ DE, ∀ D : ((blocks DE).mask M).powerset,
      FirstBlockPoolData (charts DE D) P M X hX,
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ)
      (a : RealParameters) (t Y₁ Y₂ : ℝ) (B : ℕ),
    ParentSourceCalibration centered d a Zpool t Y₁ Y₂ columns
      (fun i j => (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).originalPair
        (generatedOriginalColumn (σ := σ) hΓ (fullI j) (afull j) (hafull j)) (profiles i j))
      (sIntegerFiniteTestFunction K A.Sf (rowBallFiniteFamily K A.Sf rowBallSize)) radius M B →
    pairedStageEnergy centered d a Zpool t Y₁ Y₂ ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).dualZeroTerm μv hDiff (rowBallFiniteFamily K A.Sf rowBallSize)‖ +
          (∑ D : ((blocks DE).mask M).powerset, (pools DE D).pooledCost) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ V ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass (sources DE).mask radius) := by
  obtain ⟨seminorms, Ctail, hC, hparent⟩ :=
    parent_first_stage_dual_raw_bound (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ)
      C hDiff rowBallSize decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro Zpool ell eps bad P ι columns coefficient fullI afull hafull profiles hprofiles radius M X hX
  dsimp only
  intro charts pools ω ψ centered d a t Y₁ Y₂ B cal
  have hp := hparent columns coefficient fullI afull hafull profiles hprofiles radius M X hX
    centered d a Zpool t Y₁ Y₂ B cal
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro DE _
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  let b := canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let source := b.finiteSource hΓ C columns columns profiles M radius X hX
  change (∑ D : (b.mask M).powerset,
      ‖∑ t ∈ source.divisorRows D.val, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
        (source.pairs i j).transformedRow μv hDiff
          (rowBallFiniteFamily K A.Sf rowBallSize) radius D.val t‖) ≤ _
  apply Finset.sum_le_sum
  intro D _
  exact ((charts DE D).kernel_bound_of_phase_one hDiff M X hX (fun i j hc =>
    canonicalFirstCommonBlock_phase_one hΓ C columns columns fullI fullI DE.val DE.property i j hc)).trans
      ((pools DE D).kernelCost_le_pool hDiff)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.divisorTransform_re_le_dual_rows
#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_dual_raw_bound
#print axioms HeckeSkeleton.Moments.EngineStep.parent_first_stage_pool_dual_bound
