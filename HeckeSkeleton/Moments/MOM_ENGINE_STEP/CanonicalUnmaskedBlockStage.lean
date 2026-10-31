import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBlockGaussStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask

/-!
# The unmasked second majorant with the actual common-block classifier

This uses each common block's full original prime set and its genuine
nonunit divided-frequency flags.  The empty row mask is chosen when the
positive Gauss majorant is constructed.  All column coefficients,
original column masks, common ideals and the full-log Fourier kernel
remain those of the same original source.

The uniform Poisson theorem supplies the energy bound internally.  In
particular there is no comparison obtained by removing masks from an
already expanded complex correlation, and no global union of the common
blocks' prime supports is charged to a single column norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
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

namespace ActualGaussStage

variable {hΓ μv hDiff ν}

/-- Construct the second stage from the very original Gauss source.
No avoidance or column coprimality premise is needed for its new row
ball.  Masks already present in G.coefficient are retained literally. -/
def canonicalUnmaskedRowBallByBlock
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {ι : Type*} (G : ActualGaussSource C ι)
    (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
    (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
    {Θ : Type*} [Fintype Θ]
    (dimension width : ℕ)
    (character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1)) :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G (rowBallFiniteFamily K A.Sf 1) :=
  canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ ∅ cutoff hcutoff hnorm
    G.emptyMask_row_avoidance G.emptyMask_columns_coprime
    dimension width (fun DE _ => character DE) (fun DE _ => dyad DE)

section Projections

variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ]
variable (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

@[simp] theorem canonicalUnmaskedRowBallByBlock_mask :
    (canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).mask = ∅ := rfl

@[simp] theorem canonicalUnmaskedRowBallByBlock_radius :
    (canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).radius.val =
        (retainedScale * Z ^ g)⁻¹ := rfl

@[simp] theorem canonicalUnmaskedRowBallByBlock_profile :
    (canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).profile =
        CanonicalRowBall.archTest K A.Sf 1 := rfl

theorem canonicalUnmaskedRowBallByBlock_source_profile
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (i j : ι) :
    (((canonicalUnmaskedRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad).sources DE).pairs i j).profile =
        (G.coefficient i * star (G.coefficient j)) •
          CanonicalRowBall.archTest K A.Sf 1 := rfl

end Projections

end ActualGaussStage

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The original uniform Poisson theorem bounds this constructed
majorant of the same G.energy, with the actual per-block classifier
and no input energy comparison. -/
theorem canonical_unmasked_block_gauss_stage_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B Drecipe)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ
      (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (G : ActualGaussSource C ι),
    ∀ retainedScale Z g : ℝ, ∀ (hscale : 0 < retainedScale) (hZ : 0 < Z),
    ∀ cutoff : ℝ, ∀ hcutoff : 1 ≤ cutoff,
    ∀ hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g,
    ∀ {Θ : Type*} [Fintype Θ],
    ∀ (dimension width : ℕ),
    ∀ (character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ),
    ∀ (dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1)),
      G.energy hDiff ≤
        (ActualGaussStage.canonicalUnmaskedRowBallByBlock
          (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
          δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
          dimension width character dyad).cost seminorms Ctail decay := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    actual_gauss_stage_bound (E := ℝ) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro ι G retainedScale Z g hscale hZ cutoff hcutoff hnorm Θ _ dimension width character dyad
  exact hbound G _

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedRowBallByBlock
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedRowBallByBlock_source_profile
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_unmasked_block_gauss_stage_bound
