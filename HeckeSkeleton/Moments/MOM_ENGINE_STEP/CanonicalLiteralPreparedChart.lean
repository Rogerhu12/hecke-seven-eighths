import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalUnmaskedBlockStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportedGaussStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralChartLocations

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
  let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  have hD : D.val = ∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp D.property)
  change (if G.coefficient i = 0 then 0 else
      if DE.val ∈ G.activeCommon then
        (if G.coefficient i = 0 then 0 else
          G.coefficient i * ((A.exteriorNorm (b.secondLeftIdeal i) ^ δ : ℝ) : ℂ))
      else 0) *
    (generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
      (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (b.secondLeft_generates C i)).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val = _
  rw [hD, CanonicalLiteralFixedPhases.generated_empty_divisorPhase]
  by_cases hz : G.coefficient i = 0
  · simp only [hz, if_pos, zero_mul]
  · simp only [if_neg hz, if_pos hactive]
    rw [b.secondLeftIdeal_eq G.columns i hi]

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
  let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
  have hD : D.val = ∅ := Finset.subset_empty.mp (Finset.mem_powerset.mp D.property)
  change (if G.coefficient i = 0 then 0 else
      if DE.val ∈ G.activeCommon then
        (if G.coefficient i = 0 then 0 else
          G.coefficient i * ((A.exteriorNorm (b.secondRightIdeal i) ^ δ : ℝ) : ℂ))
      else 0) *
    (generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal i)
      (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator i)
      (b.secondRight_generates C i)).divisorPhase
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val = _
  rw [hD, CanonicalLiteralFixedPhases.generated_empty_divisorPhase]
  by_cases hz : G.coefficient i = 0
  · simp only [hz, if_pos, zero_mul]
  · simp only [if_neg hz, if_pos hactive]
    rw [b.secondRightIdeal_eq G.columns i hi]

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
  let radius := CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ
  let rowLog := Real.log (CanonicalSecondLogChart.rowRadius radius v.2.1.val q).val
  refine ⟨WithLp.toLp 2
    (-firstSign * Real.log (A.exteriorNorm
      (ExteriorIdealEuler.mul power v.block.commonLeftIdeal)),
      rowLog - Real.log (A.exteriorNorm v.block.commonLeftIdeal)), ?_⟩
  intro i hi
  have hi' : i ∈ v.leftReindex.cartesian := by
    change i ∈ pairedAllocatedColumns j.1.val j.2.2.1.val
      v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
      id id HeightOneSpectrum.asIdeal at hi
    rw [paired_allocated_columns_eq_filter] at hi
    exact (Finset.mem_filter.mp hi).1
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hi').1
  have h₁ := v.literalLeftResidualAtlas.plain₁_nonzero i.1.1 hp.1
  have h₂ := v.literalLeftResidualAtlas.plain₂_nonzero i.1.2 hp.2
  have hc := v.literalLeft_index_common i hi'
  change WithLp.toLp 2
    (-firstSign * Real.log (Ideal.absNorm (power.val * (G.ideal (v.leftReindex.index i)).val) : ℝ),
      rowLog - Real.log (Ideal.absNorm (v.block.secondLeftIdeal (v.leftReindex.index i)).val : ℝ)) = _
  apply CanonicalLiteralLocations.actual_product_locations firstSign rowLog i h₁ h₂
    _ _ (power.val * v.block.commonLeftIdeal.val) v.block.commonLeftIdeal.val
    (mul_ne_zero power.property.1 v.block.commonLeftIdeal.property.1)
    v.block.commonLeftIdeal.property.1
  · rw [v.block.left_reconstruct G.columns _ hc, v.leftReindex.ideal_product i hi', mul_assoc]
  · change v.block.commonLeftIdeal.val * (v.block.leftResidual (v.leftReindex.index i)).val = _
    rw [v.leftReindex.ideal_product i hi']

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
  refine ⟨WithLp.toLp 2
    (firstSign * Real.log (A.exteriorNorm
      (ExteriorIdealEuler.mul power v.block.commonRightIdeal)),
      -Real.log (A.exteriorNorm v.block.commonRightIdeal)), ?_⟩
  intro i hi
  have hi' : i ∈ v.rightReindex.cartesian := by
    change i ∈ pairedAllocatedColumns j.1.val j.2.2.2.val
      v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
      id id HeightOneSpectrum.asIdeal at hi
    rw [paired_allocated_columns_eq_filter] at hi
    exact (Finset.mem_filter.mp hi).1
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hi').1
  have h₁ := v.literalRightResidualAtlas.plain₁_nonzero i.1.1 hp.1
  have h₂ := v.literalRightResidualAtlas.plain₂_nonzero i.1.2 hp.2
  have hc := v.literalRight_index_common i hi'
  have he := CanonicalLiteralLocations.actual_product_locations (-firstSign) 0 i h₁ h₂
    (power.val * (G.ideal (v.rightReindex.index i)).val)
    (v.block.secondRightIdeal (v.rightReindex.index i)).val
    (power.val * v.block.commonRightIdeal.val) v.block.commonRightIdeal.val
    (mul_ne_zero power.property.1 v.block.commonRightIdeal.property.1)
    v.block.commonRightIdeal.property.1
    (by rw [v.block.right_reconstruct G.columns _ hc, v.rightReindex.ideal_product i hi', mul_assoc])
    (by change v.block.commonRightIdeal.val *
          (v.block.rightResidual (v.rightReindex.index i)).val = _
        rw [v.rightReindex.ideal_product i hi'])
  change WithLp.toLp 2
    (-(-firstSign * Real.log (Ideal.absNorm (power.val * (G.ideal (v.rightReindex.index i)).val) : ℝ)),
      -Real.log (Ideal.absNorm (v.block.secondRightIdeal (v.rightReindex.index i)).val : ℝ)) = _
  simpa only [neg_neg, neg_mul, zero_sub] using he

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leftCoefficient
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leaf_leftPoint
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmasked_prepared_leaf_rightPoint
