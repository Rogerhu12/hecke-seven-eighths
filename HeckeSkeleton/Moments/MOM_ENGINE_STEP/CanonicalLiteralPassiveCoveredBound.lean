import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveCoveredProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveOriginalBound

/-!
# The original covered integrand and the passive finite family

The original ordinary row class, its complete two coefficients, and
its two logarithmic locations are retained. The actual atom recipes
supply the passive expansion for every original live row. The old
second-allocation scalar is paid once outside the resulting passive
integrand, with its full original divisor norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralActualProfiles PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]



variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
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

local instance canonicalLiteralPassiveCoveredBoundCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
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
variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredClassKey LC RC)
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (firstKernel : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)
variable (hlive : (v.leaf exceptional firstKernel x j).Live) (firstSign : ℝ)
variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftScalar rightScalar : ℂ)
variable (leftBalance rightBalance : Bool → ℝ)
variable (hleftBalance : ∀ r, 0 < leftBalance r)
variable (hrightBalance : ∀ r, 0 < rightBalance r)
variable (firstSupport : Finset (Ideal (𝓞 K)))
variable (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (leftProfiles : ProfileSupport (v.literalLeftAtoms leftAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (rightProfiles : ProfileSupport (v.literalRightAtoms rightAtoms)
  ((primeSupport A.cS ∪ firstSupport) ∪ primeSupport v.1.val.1))
variable (hbaseLeft : (v.literalLeftAtoms leftAtoms).base = Z)
variable (hbaseRight : (v.literalRightAtoms rightAtoms).base = Z)
variable {ω ψ : HeckeCharacter K}
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (choice : CanonicalLiteralPassiveSource.PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (leftRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalLeftAtoms leftAtoms))
variable (rightRecipe : CanonicalLiteralActualCharacters.Recipe P Rchar F parent oldMoving
  correction remaining extra (v.literalRightAtoms rightAtoms))
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)

local notation "rectangles" =>
  v.literalStrippedRectangles leftAtoms rightAtoms exceptional firstKernel x j
    leftScalar rightScalar firstSign hlive leftBalance rightBalance hleftBalance hrightBalance
local notation "leftTable" => ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTable" => ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain rightBalance
local notation "leftTests" => (leftProfiles.profiles.scale leftScalar⁻¹).balancePlain leftBalance
local notation "rightTests" => (rightProfiles.profiles.scale rightScalar⁻¹).balancePlain rightBalance
local notation "normalizationRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar
local notation "ordinaryRows" => (normalizationRows).restrictRows
  (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
local notation "allocation" => v.literalAllocation exceptional firstKernel x j hlive
local notation "pattern" => v.chart.originalNonunitPattern ∅ cutoff hcutoff v.rowLabel
local notation "sector" => v.chart.originalSector P ∅ cutoff hcutoff v.rowLabel
local notation "leftAllocation" => ((rectangles).leftFrame C false).allocation
local notation "rightAllocation" => ((rectangles).rightFrame C false).allocation
local notation "leftPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => leftRecipe.slots.index (SlotRestriction.index (leftAllocation).keep i))
local notation "rightPaid" => CanonicalLiteralPaidCharacters.paidSourceCharacters P Rchar
  choice.phases parent oldMoving correction remaining
  (fun i => rightRecipe.slots.index (SlotRestriction.index (rightAllocation).keep i))
local notation "frozenPair" =>
  Real.sqrt ((leftTable).originalFrozenCost leftAllocation) *
    Real.sqrt ((rightTable).originalFrozenCost rightAllocation)

/-- This is the old second-allocation cost, not a new passive cost.
Its two stored allocations still have the same original divisor. -/
def literalPassiveOriginalFrozenPair : ℝ := frozenPair

theorem literalPassiveOriginalFrozenPair_nonneg : 0 ≤ frozenPair :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

include hcorr hfirst hextra hone hroot hemb in
/-- The complete ordinary integrand is bounded by the passive
integrand on the same row measure. No completed source bound is input. -/
theorem literalPassiveOriginalIntegrand_le (ξ : WithLp 2 (ℝ × ℝ)) :
    (rectangles).originalIntegrand ξ ≤ frozenPair *
      CanonicalLiteralPassiveNormalizedFamily.integrand C ordinaryRows leftTests rightTests
        leftAllocation rightAllocation leftPaid rightPaid (choice.mask extra) (choice.mask extra)
        firstSign (-firstSign) ξ := by
  have hp : v.chart.NonunitLabelStable :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_nonunitLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  have hs : v.chart.SectorLabelStable P :=
    ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock_sectorLabelStable
      (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      P δ₂ hδ₂ hδ₂half G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      dimension width character dyad v.1 v.2.1
  let patternRows : (ordinaryRows).live → CanonicalOriginalPhaseCalibration.PatternSector
      P ordinaryRows C pattern sector :=
    v.chart.originalReweightedPatternSector P hp hs ∅ cutoff hcutoff v.rowLabel
      ((v.literalRows leftAtoms rightAtoms).withColumnConstants leftScalar rightScalar).weight
      (fun h => (v.chart.actualRows ∅ cutoff hcutoff v.rowLabel).correlation h ≠ 0)
      (fun h => ¬(v.leaf exceptional firstKernel x j).exceptional h)
  have hrows (h : (ordinaryRows).live) : (patternRows h).val.val = h := rfl
  have supportL : (v.literalLeftAtoms leftAtoms).SupportData
      ((primeSupport A.cS ∪ firstSupport) ∪
        primeSupport (primePowerProduct v.block.primes v.block.leftMultiplicity).val) := by
    rw [v.block.common_left]
    exact leftProfiles.support
  have supportR : (v.literalRightAtoms rightAtoms).SupportData
      ((primeSupport A.cS ∪ firstSupport) ∪
        primeSupport (primePowerProduct v.block.primes v.block.leftMultiplicity).val) := by
    rw [v.block.common_left]
    exact rightProfiles.support
  have hL := (Finset.mem_filter.mp (allocation).property).2.1
  have hleft := CanonicalLiteralPassiveOriginalBound.sqrt_frequency_le_passive
    (W := leftTests) (B := leftAllocation) (P := P) (Rchar := Rchar) (F := F)
    (parent := parent) (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (C := C) (S := ordinaryRows) (pattern := pattern) (sector := sector)
    (remaining := remaining) (extra := extra) (index := leftRecipe.slots.index)
    (choice := choice) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hcharacters := leftRecipe.characters) (firstSupport := firstSupport) (hfirst := hfirst)
    (hextra := hextra) (hl := v.block.left_positive) (hr := v.block.right_positive)
    (support := (supportL.scale leftScalar⁻¹).balancePlain leftBalance)
    (hplain₁ := rfl) (hplain₂ := rfl) (hslots := rfl)
    (patternRows := patternRows) (patternRows_val := hrows)
    hL j.2.2.1.property firstSign false ξ
  have hright := CanonicalLiteralPassiveOriginalBound.sqrt_frequency_le_passive
    (W := rightTests) (B := rightAllocation) (P := P) (Rchar := Rchar) (F := F)
    (parent := parent) (oldMoving := oldMoving) (correction := correction) (hcorr := hcorr)
    (C := C) (S := ordinaryRows) (pattern := pattern) (sector := sector)
    (remaining := remaining) (extra := extra) (index := rightRecipe.slots.index)
    (choice := choice) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hcharacters := rightRecipe.characters) (firstSupport := firstSupport) (hfirst := hfirst)
    (hextra := hextra) (hl := v.block.left_positive) (hr := v.block.right_positive)
    (support := (supportR.scale rightScalar⁻¹).balancePlain rightBalance)
    (hplain₁ := rfl) (hplain₂ := rfl) (hslots := rfl)
    (patternRows := patternRows) (patternRows_val := hrows)
    hL j.2.2.2.property (-firstSign) true ξ
  have hEL := CanonicalLiteralOriginalEnergy.left_energy leftTable ordinaryRows C leftAllocation
    j.2.1 (fun i => v.block.leftResidual (v.leftReindex.index i))
    (by
      intro i hi
      apply v.leftReindex.ideal_product i
      rw [ActualColumnAllocation.columns, WholeAllocation.paired_allocated_columns_eq_filter] at hi
      exact (Finset.mem_filter.mp hi).1) firstSign ξ
  have hER := CanonicalLiteralOriginalEnergy.right_energy rightTable ordinaryRows C rightAllocation
    j.2.1 (fun i => v.block.rightResidual (v.rightReindex.index i))
    (by
      intro i hi
      apply v.rightReindex.ideal_product i
      rw [ActualColumnAllocation.columns, WholeAllocation.paired_allocated_columns_eq_filter] at hi
      exact (Finset.mem_filter.mp hi).1) (-firstSign) ξ
  have hwholeL : (leftTable).whole =
      ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).whole :=
    funext (((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).balancePlain_whole
      leftBalance hleftBalance)
  have hwholeR : (rightTable).whole =
      ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).whole :=
    funext (((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).balancePlain_whole
      rightBalance hrightBalance)
  change Real.sqrt (jointColumnEnergy (ordinaryRows).rows (leftAllocation).columns
      (fun h => (ordinaryRows).weight h * (ordinaryRows).correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) PUnit.{1}
        (fun i => v.block.leftResidual (v.leftReindex.index i)) (ordinaryRows).frequency
        (fun _ => PUnit.unit) j.2.1 ((v.literalLeftAtoms leftAtoms).scale leftScalar⁻¹).whole)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign) (CanonicalLiteralLocations.prime firstSign)) ξ) *
    Real.sqrt (jointColumnEnergy (ordinaryRows).rows (rightAllocation).columns
      (fun h => (ordinaryRows).weight h * (ordinaryRows).correlation h)
      (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
        (fun i => v.block.rightResidual (v.rightReindex.index i)) (ordinaryRows).frequency
        (fun _ => PUnit.unit) j.2.1 ((v.literalRightAtoms rightAtoms).scale rightScalar⁻¹).whole)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
        (CanonicalLiteralLocations.plain (-firstSign))
        (CanonicalLiteralLocations.prime (-firstSign))) ξ) ≤ _
  rw [← hwholeL, ← hwholeR, hEL, hER]
  have he := mul_le_mul hleft hright (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  convert he using 1 <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      CanonicalLiteralPassiveNormalizedFamily.integrand] <;> ring

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveOriginalFrozenPair
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalPassiveOriginalIntegrand_le
