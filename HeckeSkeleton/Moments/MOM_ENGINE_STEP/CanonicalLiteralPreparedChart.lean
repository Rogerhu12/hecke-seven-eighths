import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedBlockStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralChartLocations

set_option linter.unusedSectionVars false

/-!
# The actual prepared chart fields used by the literal child binding

The active common-label gate and both coefficient-zero gates are read
from the original stage. On a live common label they retain the exact
original column coefficient, its Mellin norm power and the genuine
chosen empty-mask unit. Both stored coordinates are also computed
here, including the original first source's power and sign.

The position identities hold at the same two Fourier variables. Their
only extra term is a common row translation inside a column norm; the
ordinary binding already removes that unit phase exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

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
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "s" => canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad

/-- The canonical prepared stage retains its original coefficient
on every active common block. The two coefficient-zero gates are
identically harmless even on an individual zero column. -/
theorem canonicalUnmasked_prepared_leftCoefficient
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset)
    (hactive : DE.val ∈ G.activeCommon) (i : ι)
    (hi : i ∈ (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).leftColumns G.columns) :
    ((s).supported.gated.charts DE D).sourceLeftCoefficient i =
      G.coefficient i * ((A.exteriorNorm (G.ideal i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (G.ideal i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

/-- The canonical prepared stage retains its original coefficient
on every active common block. The two coefficient-zero gates are
identically harmless even on an individual zero column. -/
theorem canonicalUnmasked_prepared_rightCoefficient
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset)
    (hactive : DE.val ∈ G.activeCommon) (i : ι)
    (hi : i ∈ (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).rightColumns G.columns) :
    ((s).supported.gated.charts DE D).sourceRightCoefficient i =
      G.coefficient i * ((A.exteriorNorm (G.ideal i) ^ δ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) (G.ideal i).val
          (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)) := by
  sorry

variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (v : (canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (canonicalUnmaskedRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (F : SchwartzMap ℝ ℂ) (power : A.Exterior) (firstSign : ℝ)
variable (j : v.AllocationKey)

local notation "firstPoint" => fun i =>
  -firstSign * Real.log (A.exteriorNorm (ExteriorIdealEuler.mul power (G.ideal i)))

/-- The exact common row translation for the stored left column.
It is proved from the original complete ideal and the actual residual
occurrence product. No source point identity is an input. -/
theorem canonicalUnmasked_prepared_leaf_leftPoint
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ∃ z : WithLp 2 (ℝ × ℝ),
      ∀ i ∈ (v.leaf exceptional F firstPoint j).left,
        WithLp.toLp 2 ((v.leaf exceptional F firstPoint j).leftFirst q i,
          (v.leaf exceptional F firstPoint j).leftSecond q i) =
          z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
            (CanonicalLiteralLocations.plain firstSign)
            (CanonicalLiteralLocations.prime firstSign) i := by
  sorry

/-- The stored right first coordinate enters with its existing minus
sign. Its second coordinate has no row-radius term, and the same
residual ideals give the whole common translation. -/
theorem canonicalUnmasked_prepared_leaf_rightPoint
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ∃ z : WithLp 2 (ℝ × ℝ),
      ∀ i ∈ (v.leaf exceptional F firstPoint j).right,
        WithLp.toLp 2 (-(v.leaf exceptional F firstPoint j).rightFirst q i,
          (v.leaf exceptional F firstPoint j).rightSecond q i) =
          z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
            (CanonicalLiteralLocations.plain (-firstSign))
            (CanonicalLiteralLocations.prime (-firstSign)) i := by
  sorry

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leftCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leaf_leftPoint
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leaf_rightPoint
