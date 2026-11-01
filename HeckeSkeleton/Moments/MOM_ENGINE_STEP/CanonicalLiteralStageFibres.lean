import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralOriginalPoolStages

/-!
# Actual orbital fibres of the fixed second-stage classifier

The direct and residual sources retain the original signed orbit
representatives. The main source pays its actual amplification
multiplicity. A nonzero physical fibre provides a genuine original
row, including when every column coefficient vanishes.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {C : A.GeneralArithmeticContext σ η hS}

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- A positive maximum of the actual finite fibre sizes requires an
actual original row. This does not inspect coefficient activity. -/
theorem engineOrbitMultiplicity_rows_nonempty (rows : Finset A.R)
    (h : engineOrbitMultiplicity (Γ := Γ) rows ≠ 0) : rows.Nonempty := by
  by_contra hempty
  have he : rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  apply h
  simp only [he, engineOrbitMultiplicity, Finset.sup_empty]

namespace ActualGaussStage

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)

local notation "stage" => literalSectorStage (hΓ := hΓ) (μv := μv) (hDiff := hDiff)
  (ν := ν) P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm

@[simp] theorem literalSectorStage_fiber :
    stage.fiber = engineOrbitMultiplicity (Γ := Γ) G.rows := rfl

theorem literalSectorStage_rows_nonempty (h : stage.fiber ≠ 0) : G.rows.Nonempty :=
  engineOrbitMultiplicity_rows_nonempty G.rows h

/-- Every subset of the original signed representative image keeps
unit physical fibres in the actual constructed stage. -/
theorem literalSectorStage_fiber_le_one
    (original : Finset Orbit) (sign : A.R) (hsign : sign ≠ 0)
    (hrows : G.rows ⊆ original.image (fun q => q.out.val * sign)) : stage.fiber ≤ 1 :=
  engineOrbit_image_multiplicity_le_one original sign hsign G.rows hrows

end ActualGaussStage

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z step eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z (step / 3) eps}
variable {ι : Type*} (d : FirstGaussPoolData C pool ι) (c : ι → ℂ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (a : RealParameters) (I : OriginalNominalIdeals K)
variable (supportError : ℝ) (herr : 0 ≤ supportError) (hstep : 0 < step)
variable (hrows : ∀ h ∈ d.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ I.canonicalRetainedScale a Z supportError)
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)

local notation "stages" => d.literalCanonicalStages (hΓ := hΓ) (μv := μv)
  (hDiff := hDiff) (ν := ν) c P a I supportError herr hstep hrows δ hδ hδhalf cutoff hcutoff

/-- One original bound controls the genuine main and all 1/6/7
physical fibres. It is selected before the prime pool and its sources. -/
theorem literalCanonicalStages_fiber_le
    (M : ℝ) (hM : d.rowExponent ≤ M)
    (original : Finset Orbit) (sign : A.R) (hsign : sign ≠ 0)
    (horiginal : d.rows ⊆ original.image (fun q => q.out.val * sign))
    (tag : PoolSourceTag pool) :
    (stages.tag tag).fiber ≤ max 1 ⌈(M + 6 * (step / 3)) / ((step / 3) / 2)⌉₊ := by
  rcases tag with u | p | p | p
  · exact (d.main_orbit_multiplicity_le_uniform M hM original sign hsign horiginal).trans
      (le_max_right _ _)
  all_goals
    exact (d.error_orbit_multiplicity_le_one original sign hsign horiginal p.val).trans
      (le_max_left _ _)

/-- This is the same physical source used to create the selected
stage; no supported-column replacement enters the terminal estimate. -/
theorem literalCanonicalStages_rows_nonempty
    (tag : PoolSourceTag pool) (h : (stages.tag tag).fiber ≠ 0) :
    (d.tagSource c tag).rows.Nonempty := by
  rcases tag with u | p | p | p
  all_goals
    exact engineOrbitMultiplicity_rows_nonempty _ h

end FirstGaussPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.engineOrbitMultiplicity_rows_nonempty
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.literalSectorStage_fiber_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalCanonicalStages_fiber_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalCanonicalStages_rows_nonempty
