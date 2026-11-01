import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPreparedChart

/-!
# Inserting the proved literal atom calculations into the stored leaf

This is the shared structural adapter for the canonical source
specializations. It combines the already proved individual original
coefficient calculation with the canonical chart-field identities and
the actual fixed-power location formula. Actual source constructors
supply those proofs internally from their original occurrence maps.
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

variable (x : ι → ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) (RC.branch v.2.2.2.1).slotCount)
variable (hcoeffL : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ v.block.leftColumns G.columns →
  leftAtoms.whole i =
    G.coefficient ((LC.branch v.2.2.1).reindex.index i) *
      ((A.exteriorNorm (G.ideal ((LC.branch v.2.2.1).reindex.index i)) ^ δ : ℝ) : ℂ) *
      actualIdealResidue (A := A) (σ := σ)
        (G.ideal ((LC.branch v.2.2.1).reindex.index i)).val
        (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)))
variable (hcoeffR : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns G.columns →
  rightAtoms.whole i =
    G.coefficient ((RC.branch v.2.2.2.1).reindex.index i) *
      ((A.exteriorNorm (G.ideal ((RC.branch v.2.2.2.1).reindex.index i)) ^ δ : ℝ) : ℂ) *
      actualIdealResidue (A := A) (σ := σ)
        (G.ideal ((RC.branch v.2.2.2.1).reindex.index i)).val
        (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := A)))

include hcoeffL in
private theorem preparedLiteral_leftCoefficient
    (hactive : v.1.val ∈ G.activeCommon)
    (i : AllocationColumn K (LC.branch v.2.2.1).slotCount)
    (hi : i ∈ (LC.branch v.2.2.1).reindex.cartesian)
    (hc : (LC.branch v.2.2.1).reindex.index i ∈ v.block.leftColumns G.columns) :
    v.chart.sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i :=
  (canonicalUnmasked_prepared_leftCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad v.1 v.2.1 hactive _ hc).trans
      (hcoeffL i hi hc).symm

include hcoeffR in
private theorem preparedLiteral_rightCoefficient
    (hactive : v.1.val ∈ G.activeCommon)
    (i : AllocationColumn K (RC.branch v.2.2.2.1).slotCount)
    (hi : i ∈ (RC.branch v.2.2.2.1).reindex.cartesian)
    (hc : (RC.branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns G.columns) :
    v.chart.sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i :=
  (canonicalUnmasked_prepared_rightCoefficient
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
    dimension width character dyad v.1 v.2.1 hactive _ hc).trans
      (hcoeffR i hi hc).symm

/-- The column calculations are inserted into the actual prepared
leaf. Liveness is used only to identify its original active common
label and its actual allocation. -/
def preparedLiteralExtraction (hlive : (v.leaf exceptional F x j).Live) :
    (v.leaf exceptional F x j).ConstantAtomExtraction := by
  have ha : v.1.val ∈ G.activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (s).supported_gated_leaf_active LC RC exceptional F x ⟨v, j⟩ q i hci
  exact v.literalExtraction leftAtoms rightAtoms exceptional F x j
    (preparedLiteral_leftCoefficient (v := v) (leftAtoms := leftAtoms) (hcoeffL := hcoeffL) ha)
    (preparedLiteral_rightCoefficient (v := v) (rightAtoms := rightAtoms) (hcoeffR := hcoeffR) ha)

/-- One adapter is shared by the actual direct, main and valuation
calculations. In the actual-source constructors both `hcoeff` proofs
come from the original atom tables and `hx` comes from the original
prime-power reconstruction; none is a primitive producer field. -/
def preparedLiteralOrdinaryBinding
    (hx : ∀ i, x i = -firstSign * Real.log
      (A.exteriorNorm (ExteriorIdealEuler.mul power (G.ideal i))))
    (hlive : (v.leaf exceptional F x j).Live) :
    (preparedLiteralExtraction (v := v) (exceptional := exceptional) (F := F) (j := j)
      (x := x) (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
      (hcoeffL := hcoeffL) (hcoeffR := hcoeffR) hlive).leaf.OrdinaryBinding
      (v.literalRectangles leftAtoms rightAtoms exceptional F x j firstSign hlive) := by
  have ha : v.1.val ∈ G.activeCommon := by
    obtain ⟨q, hq, i, hi, hci⟩ := hlive.2.1
    exact (s).supported_gated_leaf_active LC RC exceptional F x ⟨v, j⟩ q i hci
  apply v.literalOrdinaryBinding leftAtoms rightAtoms exceptional F x j
    (preparedLiteral_leftCoefficient (v := v) (leftAtoms := leftAtoms) (hcoeffL := hcoeffL) ha)
    (preparedLiteral_rightCoefficient (v := v) (rightAtoms := rightAtoms) (hcoeffR := hcoeffR) ha)
    firstSign hlive
  · intro q _
    rw [funext hx]
    exact canonicalUnmasked_prepared_leaf_leftPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad LC RC v exceptional F power firstSign j q
  · intro q _
    rw [funext hx]
    exact canonicalUnmasked_prepared_leaf_rightPoint
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad LC RC v exceptional F power firstSign j q

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.preparedLiteralExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.preparedLiteralOrdinaryBinding
