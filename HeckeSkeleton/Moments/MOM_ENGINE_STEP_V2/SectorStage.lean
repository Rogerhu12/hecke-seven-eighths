import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SectorRows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed finite classifier for every original second source

The classifier records the genuine divided-frequency and sixth-unit
sector. Its auxiliary character is trivial and there are no dyadic
coordinates. The original block classifier consequently supplies its
own physical-fibre dictionary from the original column norm window.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep

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

local instance literalSectorStageSixthFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := Fintype.ofFinite _

namespace ActualGaussStage

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)

def literalSectorStage :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G (rowBallFiniteFamily K A.Sf 1) :=
  canonicalUnmaskedSectorRowBallByBlock
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm 0 0
    (fun _ _ => (PUnit.unit : PUnit.{1})) (fun _ _ i => Fin.elim0 i)

local notation "stage" => literalSectorStage (hΓ := hΓ) (μv := μv) (hDiff := hDiff)
  (ν := ν) P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm

@[simp] theorem literalSectorStage_mask : (stage).mask = ∅ := rfl

@[simp] theorem literalSectorStage_radius :
    (stage).radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ := rfl

@[simp] theorem literalSectorStage_profile :
    (stage).profile = CanonicalRowBall.archTest K A.Sf 1 := rfl

@[simp] theorem literalSectorStage_kernel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (stage).mask.powerset) :
    ((stage).charts DE D).kernel = canonicalRowBallKernel (Γ := Γ) μv ν δ hδ hδhalf := rfl

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStepV2

