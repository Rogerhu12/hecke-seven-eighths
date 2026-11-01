import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolPassiveNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolFactorFreeWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolCombinedProfile
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNominalWeightWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveIndexedWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary

/-!
# Original source weights for the same passive normalized children

The source, all literal atoms, the two kernels, and the chosen passive
family are exactly the original passive construction. The original
prime and scale windows are built from the original profile data. The
first Poisson factor is charged jointly with the actual extracted
scalar pair, retaining its Mellin tilt. The old shared allocation
cost is paid once outside the family, and the complete three slot
powers remain explicit in the original arithmetic-index estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open MeasureTheory HeckePort.IdealMobiusDivisorSum

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

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z ell eps}
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) pool M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (q : pool.primes) (n : ℕ)
variable (valuation : AmplifierValuation) (valuation_eq : n = valuation.multiplicity)


variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
variable (orders : Finset (ℕ × ℕ)) (originalBound : ℝ) (horiginalBound : 0 ≤ originalBound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hreference : reference ∈ rowDomain) (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (step error mesh : ℝ) (hstep : 0 < step) (herror : 0 ≤ error) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)

section LiteralLeftPoolPassiveIndex

variable (hnorm : ∀ h ∈ (p.divisorPools.leftData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.leftSourceCovers (raw).originalAtlas S χ).residual q n))
local notation "firstPoint" => (fun i : (p.divisorPools.leftData S).valuationColumns q.val n =>
  -Real.log (A.exteriorNorm (b.leftResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.1
local notation "oldRightAtoms" => literalLeftPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.2.1
local notation "oldLeftScalar" => literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.1
local notation "oldRightScalar" => literalLeftPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.2.1
local notation "leftAtoms" => (oldLeftAtoms).redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => (oldRightAtoms).redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
local notation "extra" => literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime)
local notation "source" => (p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val)
variable (hlive : ((ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.fiberCoveredLeaf
  ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.leftSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) exceptional F (fun i : (p.divisorPools.leftData S).valuationColumns q.val n =>
      -Real.log (A.exteriorNorm (b.leftResidual i.val))) ⟨v, j⟩).Live)
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (direct : geometry.tag = .direct → (data ξ).geometry.slotCount = 0)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (hcutoffPower : cutoff₂ ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).columns,
  ((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm (((p.divisorPools.leftData S).residualSource q.val n (p.leftDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (oldSupport : A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ a.q)
variable (firstIdeal : geometry.ideals.first.val = DE.1)
variable (oppositeIdeal : geometry.ideals.opposite.val = DE.2)
variable (physicalDivisor : geometry.ideals.complementary.val =
  (firstPhysicalDivisorIdeal (A := A) D).val)
variable (branchTag : geometry.tag = .error valuation q.val.val)
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hfirstFrozen : geometry.literalFirstExtraction.val = DE.1 * q.val.val.asIdeal ^ n)
variable (herrorPos : 0 < error)
variable (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hsupportError : geometry.supportError ≤ error)
variable (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
variable (firstNormalization : ℝ)
variable (hfirstNormalization : firstNormalization =
  firstLeftAllowance Z (geometry.skeleton.A +
    (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
    geometry.ideals.first.val geometry.ideals.opposite.val)

variable {branch : TwoDivisorCommonBranch (K := K)}
variable (index : branch.Index)
variable (hfirstIndex : index.1.val.1 = DE)
variable (hleftIndex : v.1.val.1 = index.2.2.1.val.1.1)
variable (hrightIndex : v.1.val.2 = index.2.2.1.val.1.2)
variable (hdivisorIndex : j.1.val = index.2.2.2.1.val)
variable (firstM firstQ maskLength activeLength : ℝ)
variable (hcanonicalWeight : p.weightBound = CanonicalFirstLog.rowWeightBound
  (actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity) radius D δ₁)
variable (hfirstRadius : radius.val = Z ^ (-firstM))
variable (hmaskLength : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ maskLength)
variable (hactiveLength : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).modulus,
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val = Z ^ activeLength)

/-- The actual passive family has the original arithmetic-index
bound, with its original frozen cost paid once and three slot powers.
All original occurrence windows and the combined first profile cost
are constructed here from the original source. -/
def literalLeftPoolPassiveNormalizationIndex :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  have bareLive : (v.leaf exceptional F firstPoint j).Live :=
    (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive
  let baseExtraction := literalLeftPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalLeftPoolOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 bareLive baseExtraction baseBinding
    (literalLeftPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
    oldLeftScalar (literalLeftPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 bareLive baseExtraction baseBinding
    (literalLeftPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
    oldRightScalar (literalLeftPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
  have hproductL : (oldLeftAtoms).centered = true →
      (oldLeftAtoms).scale₁ true * (oldLeftAtoms).scale₂ true =
        (oldLeftAtoms).scale₁ false * (oldLeftAtoms).scale₂ false := by
    dsimp only [literalLeftPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : (oldRightAtoms).centered = true →
      (oldRightAtoms).scale₁ true * (oldRightAtoms).scale₂ true =
        (oldRightAtoms).scale₁ false * (oldRightAtoms).scale₂ false := by
    dsimp only [literalLeftPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 bareLive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 bareLive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldLeftAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldRightAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hbL : ∀ r, 0 < leftBalance r :=
    fun _ => zero_lt_one
  have hbR : ∀ r, 0 < rightBalance r :=
    fun _ => zero_lt_one
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    1 bareLive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := (literalLeftPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ q n v.2.2.1).redistributeNormFactors δ₁ δ₂
  let ER := (literalLeftPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ q n v.2.2.2.1).redistributeNormFactors δ₁ δ₂
  let TL := literalLeftPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ q n v.2.2.1
  let TR := literalLeftPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ q n v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    ((literalLeftPoolRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1).redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe rightAtoms
    ((literalLeftPoolRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1).redistributeNormFactors δ₁ δ₂)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    change (v.literalLeftAtoms oldLeftAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalLeftPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    change (v.literalRightAtoms oldRightAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalLeftPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hactive : geometry.skeleton.R = idealLogLength Z (firstActiveRadical DE.1 DE.2) := by
    change idealLogLength Z (firstActiveRadical geometry.ideals.first.val
      geometry.ideals.opposite.val) = _
    rw [firstIdeal, oppositeIdeal]
  have hphysical : geometry.skeleton.E =
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val := by
    change idealLogLength Z geometry.ideals.complementary.val = _
    rw [physicalDivisor]
  let choice : CanonicalLiteralPassiveSource.PhaseChoice fixedPhases C :=
    .amplified q.val valuation (by
      change _ ^ (2 * n) = _ ^ (2 * valuation.multiplicity)
      rw [valuation_eq])
  have hmoving : geometry.skeleton.wo =
      (valuation.movingMultiplicity : ℝ) * idealLogLength Z q.val.val.asIdeal := by
    change geometry.tag.movingLength Z = _
    rw [branchTag]
    rfl
  have hpaidSupport : A.exteriorNorm
      ((choice.phases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
        Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo) := by
    change A.exteriorNorm
      (((CanonicalLiteralPaidCharacters.reducedPhases fixedPhases C q.val valuation)
        .moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
      Z ^ (a.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo)
    rw [hactive, hphysical, hmoving]
    simpa only [← valuation_eq] using
      CanonicalLiteralPaidSupport.reduced_amplified_left P R C b D
        Q.moving Q.remaining firstFixed hfirst q.val valuation Z a.q hZ oldSupport
  have hzero : (0, 0) ∈ CanonicalLogProfiles.sourceOrders
      (CanonicalLogProfiles.sourceOrders orders) :=
    CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _
        (hprimeOrders CanonicalFullKappaPrime.zero_mem_orders))
  let windowsL := literalLeftPoolFactorFreeOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum q n v.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  let windowsR := literalLeftPoolFactorFreeOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum q n v.2.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  have htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength = a.n₁ + a.n₂ + a.z := by
    rw [domain.total_length]
  have hcenteredL : (leftAtoms).centered = centered := by
    change (oldLeftAtoms).centered = centered
    simp only [literalLeftPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcenteredR : (rightAtoms).centered = centered := by
    change (oldRightAtoms).centered = centered
    simp only [literalLeftPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcombined := literalLeftPoolCombinedProfile_le
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ₂.le hδsum q n v.2.2.1 v.2.2.2.1
    originalWindow hzero htime hprime hi (zero_le_one.trans hhi)
    (fun _ hx => hx.2) cap hcap hcanonicalWeight
    firstM firstQ maskLength activeLength hfirstRadius hmaskLength hactiveLength
  have hfirstCost : 0 ≤ orbitalFieldFactor K *
      (CanonicalLiteralFirstScalarCost.atomBudget hi originalBound) ^ cap :=
    mul_nonneg (orbitalFieldFactor_nonneg K)
      (pow_nonneg (zero_le_one.trans
        (CanonicalLiteralFirstScalarCost.atomBudget_one hi originalBound)) _)
  have hD : index.1.val.1.1 ≠ 0 := by
    rw [hfirstIndex, ← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : index.1.val.1.2 ≠ 0 := by
    rw [hfirstIndex, ← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  have hsupport : primeSupport index.1.val.1.1 = primeSupport index.1.val.1.2 := by
    rw [hfirstIndex]
    exact b.common_support_eq
  fun analyticLeft analyticRight heightLeft heightRight =>
  v.literalPassiveNormalizedFamily_index_from_combined_atoms
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := bareLive) (firstSign := 1)
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1 ∪ {q.val.val.asIdeal})
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (choice := choice) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) (extra := extra)
    (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (cap := cap) (hcountL := windowsL.slots) (hcountR := windowsR.slots)
    (atomBound := CanonicalLiteralMassProfilePower.slotBudget originalBound)
    (hAtomBound := windowsL.atomBound_one)
    (hcostL := windowsL.prime_atoms) (hcostR := windowsR.prime_atoms)
    (hprimeL := windowsL.prime_norm) (hprimeR := windowsR.prime_norm)
    (hslotsL := fun _ => rfl) (hslotsR := fun _ => rfl)
    (hfirstL := windowsL.nominal_scale geometry hfirstFrozen htotal hcenteredL)
    (hfirstR := windowsR.nominal_scale geometry hfirstFrozen htotal hcenteredR)
    (hgaussL := windowsL.nominal_gauss geometry hfirstFrozen htotal)
    (hgaussR := windowsR.nominal_gauss geometry hfirstFrozen htotal)
    (herrorPos := herrorPos) (hannulusThreshold := hannulusThreshold)
    (hscaleThreshold := hscaleThreshold) (hsupportError := hsupportError)
    (hphysicalError := hphysicalError) (firstNormalization := firstNormalization)
    (hfirstNormalization := hfirstNormalization)
    (index := index) (hleftIndex := hleftIndex) (hrightIndex := hrightIndex)
    (hdivisorIndex := hdivisorIndex)
    (parentWidth := firstM + firstQ)
    (total := a.n₁ + a.n₂ + (data ξ).geometry.totalLength + firstQ + maskLength + activeLength)
    (rawProfile := p.weightBound)
    (firstCost := orbitalFieldFactor K *
      (CanonicalLiteralFirstScalarCost.atomBudget hi originalBound) ^ cap)
    (tilt := CanonicalFirstResidualProfileCost.tiltError firstM
      (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) maskLength activeLength δ₁ δ₂)
    (hrawProfile := p.weight_nonneg) (hfirstCost := hfirstCost) (hcombinedProfile := hcombined)
    (hD := hD) (hE := hE) (hsupportFirst := hsupport)
    (Ray₁ := PUnit) (Ray₂ := PUnit)
    (phase₁ := fun _ => (1 : Circle)) (χ₁ := χ)
    (phase₂ := fun _ => (1 : Circle)) (χ₂ := j.2.1)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight)
    (heightLeft := heightLeft) (heightRight := heightRight)

end LiteralLeftPoolPassiveIndex

section LiteralRightPoolPassiveIndex

variable (hnorm : ∀ h ∈ (p.divisorPools.rightData S).errorRows q.val,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns
  (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val) (fun i => (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (((p.rightSourceCovers (raw).originalAtlas S χ).residual q n))
local notation "firstPoint" => (fun i : (p.divisorPools.rightData S).valuationColumns q.val n =>
  Real.log (A.exteriorNorm (b.rightResidual i.val)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)) (((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n)))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.1
local notation "oldRightAtoms" => literalRightPoolAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ q n v.2.2.2.1
local notation "oldLeftScalar" => literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.1
local notation "oldRightScalar" => literalRightPoolScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ q n v.2.2.2.1
local notation "leftAtoms" => (oldLeftAtoms).redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => (oldRightAtoms).redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.amplifiedPhases C
  firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n
local notation "extra" => literalDeletionIdeal (primeSupport DE.1 ∪ {q.val.val.asIdeal}) (fun _ hp => by
        rcases Finset.mem_union.mp hp with hp | hp
        · exact support_prime hp
        · rcases Finset.mem_singleton.mp hp with rfl
          exact q.val.val.prime)
local notation "source" => (p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val)
variable (hlive : ((ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.fiberCoveredLeaf
  ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) ((p.rightSourceCovers (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ).residual q n) exceptional F (fun i : (p.divisorPools.rightData S).valuationColumns q.val n =>
      Real.log (A.exteriorNorm (b.rightResidual i.val))) ⟨v, j⟩).Live)
variable (profileBound : ℝ) (hprofileBound : 0 ≤ profileBound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ profileBound)
variable (geometry : OriginalNominalGeometry (K := K) a Z step)
variable (hretained : geometry.retainedScale = retainedScale)
variable (henlargement : geometry.enlargement = g)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct v.block.primes v.block.leftMultiplicity).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct v.block.primes v.block.rightMultiplicity).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (hnonunit : geometry.ideals.nonunitPart.val =
  (secondPatternNonunitIdeal v.block.primes
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)).val)
variable (direct : geometry.tag = .direct → (data ξ).geometry.slotCount = 0)
variable (columnLoss cutoffExponent : ℝ)
variable (hcolumnLoss : 0 ≤ columnLoss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (hsmall : 2 * (2 * columnLoss + cutoffExponent) ≤ step)
variable (hcutoffPower : cutoff₂ ≤ Z ^ cutoffExponent)
variable (hactiveColumns : ∀ i ∈ ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).columns,
  ((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).coefficient i ≠ 0 →
  A.exteriorNorm (((p.divisorPools.rightData S).residualSource q.val n (p.rightDivisorCoefficient S χ)).ideal i) ≤
    Z ^ (geometry.skeleton.A - geometry.skeleton.c - geometry.skeleton.w + columnLoss))
variable (oldSupport : A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ Z ^ a.q)
variable (firstIdeal : geometry.ideals.first.val = DE.2)
variable (oppositeIdeal : geometry.ideals.opposite.val = DE.1)
variable (physicalDivisor : geometry.ideals.complementary.val =
  (firstPhysicalDivisorIdeal (A := A) D).val)
variable (branchTag : geometry.tag = .error valuation q.val.val)
variable (hexceptional : (v.leaf exceptional F firstPoint j).exceptional = fun h =>
  (v.chart.actualRows ∅ cutoff₂ hcutoff₂ v.rowLabel).literalCharacter C P R
    (CanonicalLiteralActualCharacters.amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst q.val n)
    Q.moving Q.correction
    (v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel)
    (v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel) h ∈ (data ξ).theta)

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hfirstFrozen : geometry.literalFirstExtraction.val = DE.2 * q.val.val.asIdeal ^ n)
variable (herrorPos : 0 < error)
variable (hannulusThreshold : OriginalPairAllowanceProduction.annulusThreshold hi error ≤ Z)
variable (hscaleThreshold : hi ^ (2 * cap) ≤ Z ^ error)
variable (hsupportError : geometry.supportError ≤ error)
variable (hphysicalError : 2 * columnLoss + cutoffExponent ≤ error)
variable (firstNormalization : ℝ)
variable (hfirstNormalization : firstNormalization =
  firstLeftAllowance Z (geometry.skeleton.A +
    (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E))
    geometry.ideals.first.val geometry.ideals.opposite.val)

variable {branch : TwoDivisorCommonBranch (K := K)}
variable (index : branch.Index)
variable (hfirstIndex : index.1.val.1 = DE)
variable (hleftIndex : v.1.val.1 = index.2.2.1.val.1.1)
variable (hrightIndex : v.1.val.2 = index.2.2.1.val.1.2)
variable (hdivisorIndex : j.1.val = index.2.2.2.1.val)
variable (firstM firstQ maskLength activeLength : ℝ)
variable (hcanonicalWeight : p.weightBound = CanonicalFirstLog.rowWeightBound
  (actualActiveColumn hΓ C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity) radius D δ₁)
variable (hfirstRadius : radius.val = Z ^ (-firstM))
variable (hmaskLength : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ maskLength)
variable (hactiveLength : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  ⟨(actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).modulus,
    (actualActiveColumn hΓ C b.primes b.primes_injective
      b.leftMultiplicity b.rightMultiplicity).nonzero⟩).val = Z ^ activeLength)

/-- The actual passive family has the original arithmetic-index
bound, with its original frozen cost paid once and three slot powers.
All original occurrence windows and the combined first profile cost
are constructed here from the original source. -/
def literalRightPoolPassiveNormalizationIndex :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  have bareLive : (v.leaf exceptional F firstPoint j).Live :=
    (v.leaf exceptional F firstPoint j).live_of_scale_live _ _ hlive
  let baseExtraction := literalRightPoolExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalRightPoolOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width q n hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) bareLive baseExtraction baseBinding
    (literalRightPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
    oldLeftScalar (literalRightPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) bareLive baseExtraction baseBinding
    (literalRightPoolCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
    oldRightScalar (literalRightPoolAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1)
  have hproductL : (oldLeftAtoms).centered = true →
      (oldLeftAtoms).scale₁ true * (oldLeftAtoms).scale₂ true =
        (oldLeftAtoms).scale₁ false * (oldLeftAtoms).scale₂ false := by
    dsimp only [literalRightPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : (oldRightAtoms).centered = true →
      (oldRightAtoms).scale₁ true * (oldRightAtoms).scale₂ true =
        (oldRightAtoms).scale₁ false * (oldRightAtoms).scale₂ false := by
    dsimp only [literalRightPoolAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) bareLive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) bareLive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldLeftAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldRightAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hbL : ∀ r, 0 < leftBalance r :=
    fun _ => zero_lt_one
  have hbR : ∀ r, 0 < rightBalance r :=
    fun _ => zero_lt_one
  let extraction := originalExtraction.trans
    (originalExtraction.leaf.stripColumnConstants leftScalar rightScalar hcL hcR)
  let binding := v.stripExistingOrdinaryBinding leftAtoms rightAtoms exceptional F firstPoint j
    (-1) bareLive originalExtraction originalBinding leftScalar rightScalar hcL hcR
    leftBalance rightBalance hbL hbR
  have hwindow : Set.Icc lo hi ⊆ Set.Ioi 0 := fun _ hy => lt_of_lt_of_le hlo hy.1
  let EL := (literalRightPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ q n v.2.2.1).redistributeNormFactors δ₁ δ₂
  let ER := (literalRightPoolProfileSupport hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href originalWindow hreference htime hwindow firstFixed hfirst δ₂ q n v.2.2.2.1).redistributeNormFactors δ₁ δ₂
  let TL := literalRightPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ q n v.2.2.1
  let TR := literalRightPoolFactorFreeComputedProfiles hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    reference href orders originalBound horiginalBound originalWindow hreference htime
    isCompact_Icc hwindow hprime firstFixed hfirst δ₂ q n v.2.2.2.1
  let profilesL := v.literalLeftProfileSupport leftAtoms EL rfl rfl (fun _ => rfl)
  let profilesR := v.literalRightProfileSupport rightAtoms ER rfl rfl (fun _ => rfl)
  let computedL := v.literalLeftComputedProfiles leftAtoms EL rfl rfl (fun _ => rfl)
    leftScalar leftBalance TL
  let computedR := v.literalRightComputedProfiles rightAtoms ER rfl rfl (fun _ => rfl)
    rightScalar rightBalance TR
  let recipeL := v.literalLeftRecipe leftAtoms
    ((literalRightPoolRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.1).redistributeNormFactors δ₁ δ₂)
  let recipeR := v.literalRightRecipe rightAtoms
    ((literalRightPoolRecipe hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ q n v.2.2.2.1).redistributeNormFactors δ₁ δ₂)
  have hbaseL : (v.literalLeftAtoms leftAtoms).base = Z := by
    change (v.literalLeftAtoms oldLeftAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalLeftAtoms,
      ActualGaussStage.CoveredClassKey.literalLeftOriginal,
      literalRightPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hbaseR : (v.literalRightAtoms rightAtoms).base = Z := by
    change (v.literalRightAtoms oldRightAtoms).base = Z
    simp only [ActualGaussStage.CoveredClassKey.literalRightAtoms,
      ActualGaussStage.CoveredClassKey.literalRightOriginal,
      literalRightPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_base_eq] <;> rfl
  have hcorr : Q.correction ∈ (data ξ).theta := by
    rcases Q.correction_mem ξ with hc | hc
    · simpa only [hc] using hone
    · exact hc
  have hactive : geometry.skeleton.R = idealLogLength Z (firstActiveRadical DE.1 DE.2) := by
    change idealLogLength Z (firstActiveRadical geometry.ideals.first.val
      geometry.ideals.opposite.val) = _
    rw [firstIdeal, oppositeIdeal,
      firstActiveRadical_swap_of_support DE.1 DE.2 b.common_support_eq]
  have hphysical : geometry.skeleton.E =
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val := by
    change idealLogLength Z geometry.ideals.complementary.val = _
    rw [physicalDivisor]
  let choice : CanonicalLiteralPassiveSource.PhaseChoice fixedPhases C :=
    .amplified q.val valuation (by
      change _ ^ (2 * n) = _ ^ (2 * valuation.multiplicity)
      rw [valuation_eq])
  have hmoving : geometry.skeleton.wo =
      (valuation.movingMultiplicity : ℝ) * idealLogLength Z q.val.val.asIdeal := by
    change geometry.tag.movingLength Z = _
    rw [branchTag]
    rfl
  have hpaidSupport : A.exteriorNorm
      ((choice.phases.moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
        Z ^ (geometry.skeleton.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo) := by
    change A.exteriorNorm
      (((CanonicalLiteralPaidCharacters.reducedPhases fixedPhases C q.val valuation)
        .moving P R Q.moving).effectiveFullSupport Q.remaining) ≤
      Z ^ (a.q + geometry.skeleton.R + geometry.skeleton.E + geometry.skeleton.wo)
    rw [hactive, hphysical, hmoving]
    simpa only [← valuation_eq] using
      CanonicalLiteralPaidSupport.reduced_amplified_right P R C b D
        Q.moving Q.remaining firstFixed hfirst q.val valuation Z a.q hZ oldSupport
  have hzero : (0, 0) ∈ CanonicalLogProfiles.sourceOrders
      (CanonicalLogProfiles.sourceOrders orders) :=
    CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _
        (hprimeOrders CanonicalFullKappaPrime.zero_mem_orders))
  let windowsL := literalRightPoolFactorFreeOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum q n v.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  let windowsR := literalRightPoolFactorFreeOriginalWeightWindows
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδsum q n v.2.2.2.1
    originalWindow hzero htime hprime hi hhi (fun _ hx => hx.2) cap hcap domain
  have htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength = a.n₁ + a.n₂ + a.z := by
    rw [domain.total_length]
  have hcenteredL : (leftAtoms).centered = centered := by
    change (oldLeftAtoms).centered = centered
    simp only [literalRightPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcenteredR : (rightAtoms).centered = centered := by
    change (oldRightAtoms).centered = centered
    simp only [literalRightPoolAtoms, CanonicalLiteralRectangles.Atoms.deleteMask,
      CanonicalLiteralRectangles.Atoms.onAtlas_centered_eq] <;> rfl
  have hcombined := literalRightPoolCombinedProfile_le
    hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    firstFixed hfirst δ₂ hδ₂.le hδsum q n v.2.2.1 v.2.2.2.1
    originalWindow hzero htime hprime hi (zero_le_one.trans hhi)
    (fun _ hx => hx.2) cap hcap hcanonicalWeight
    firstM firstQ maskLength activeLength hfirstRadius hmaskLength hactiveLength
  have hfirstCost : 0 ≤ orbitalFieldFactor K *
      (CanonicalLiteralFirstScalarCost.atomBudget hi originalBound) ^ cap :=
    mul_nonneg (orbitalFieldFactor_nonneg K)
      (pow_nonneg (zero_le_one.trans
        (CanonicalLiteralFirstScalarCost.atomBudget_one hi originalBound)) _)
  have hD : index.1.val.1.1 ≠ 0 := by
    rw [hfirstIndex, ← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : index.1.val.1.2 ≠ 0 := by
    rw [hfirstIndex, ← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  have hsupport : primeSupport index.1.val.1.1 = primeSupport index.1.val.1.2 := by
    rw [hfirstIndex]
    exact b.common_support_eq
  fun analyticLeft analyticRight heightLeft heightRight =>
  v.literalPassiveNormalizedFamily_index_from_combined_atoms
    (P := P) (Rchar := R) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (G := source) (retainedScale := retainedScale) (Z := Z) (g := g)
    (hscale := hscale) (hZ := zero_lt_one.trans hZ) (cutoff := cutoff₂) (hcutoff := hcutoff₂)
    (hnorm := hnorm) (dimension := dimension) (width := width) (character := character) (dyad := dyad)
    (LC := cover) (RC := cover) (exceptional := exceptional) (firstKernel := F) (x := firstPoint)
    (j := j) (hlive := bareLive) (firstSign := (-1))
    (leftAtoms := leftAtoms) (rightAtoms := rightAtoms)
    (leftScalar := leftScalar) (rightScalar := rightScalar)
    (leftBalance := leftBalance) (rightBalance := rightBalance)
    (hleftBalance := hbL) (hrightBalance := hbR)
    (firstSupport := primeSupport DE.1 ∪ {q.val.val.asIdeal})
    (leftProfiles := profilesL) (rightProfiles := profilesR)
    (hbaseLeft := hbaseL) (hbaseRight := hbaseR)
    (F := fixedPhases) (choice := choice) (parent := data ξ) (oldMoving := Q.moving)
    (correction := Q.correction) (hcorr := hcorr) (remaining := Q.remaining) (extra := extra)
    (leftRecipe := recipeL) (rightRecipe := recipeR)
    (profileBound := profileBound) (hprofileBound := hprofileBound) (hprofile := hprofile)
    (a := a) (step := step) (geometry := geometry) (hretained := hretained) (henlargement := henlargement)
    (hsecond := hsecond) (hopposite := hopposite) (hunit := hunit) (hnonunit := hnonunit)
    (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
    (hcolumnLoss := hcolumnLoss) (hcutoffExponent := hcutoffExponent)
    (hcutoffPower := hcutoffPower) (hactiveColumns := hactiveColumns) (hpaidSupport := hpaidSupport)
    (reference := reference) (time := t) (hone := hone) (hroot := hroot) (hemb := hemb)
    (hbackground := hbackground) (hslot := hslot) (hexceptional := hexceptional)
    (domain := domain) (direct := direct) (hsmall := hsmall) (error := error) (herror := herror)
    (hstep := hstep) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
    (lo := lo) (hi := hi) (hlo := hlo) (hhi := hhi) (orders := orders)
    (original := originalWindow) (hreference := hreference) (htime := htime)
    (horders := fun z hz => CanonicalLogProfiles.subset_sourceOrders _
      (CanonicalLogProfiles.subset_sourceOrders _ hz))
    (leftComputed := computedL) (rightComputed := computedR) (hprimeOrders := hprimeOrders)
    (δ := δ) (analyticHeight := analyticHeight) (hδ := hδ) (hδhi := hδhi)
    (cap := cap) (hcountL := windowsL.slots) (hcountR := windowsR.slots)
    (atomBound := CanonicalLiteralMassProfilePower.slotBudget originalBound)
    (hAtomBound := windowsL.atomBound_one)
    (hcostL := windowsL.prime_atoms) (hcostR := windowsR.prime_atoms)
    (hprimeL := windowsL.prime_norm) (hprimeR := windowsR.prime_norm)
    (hslotsL := fun _ => rfl) (hslotsR := fun _ => rfl)
    (hfirstL := windowsL.nominal_scale geometry hfirstFrozen htotal hcenteredL)
    (hfirstR := windowsR.nominal_scale geometry hfirstFrozen htotal hcenteredR)
    (hgaussL := windowsL.nominal_gauss geometry hfirstFrozen htotal)
    (hgaussR := windowsR.nominal_gauss geometry hfirstFrozen htotal)
    (herrorPos := herrorPos) (hannulusThreshold := hannulusThreshold)
    (hscaleThreshold := hscaleThreshold) (hsupportError := hsupportError)
    (hphysicalError := hphysicalError) (firstNormalization := firstNormalization)
    (hfirstNormalization := hfirstNormalization)
    (index := index) (hleftIndex := hleftIndex) (hrightIndex := hrightIndex)
    (hdivisorIndex := hdivisorIndex)
    (parentWidth := firstM + firstQ)
    (total := a.n₁ + a.n₂ + (data ξ).geometry.totalLength + firstQ + maskLength + activeLength)
    (rawProfile := p.weightBound)
    (firstCost := orbitalFieldFactor K *
      (CanonicalLiteralFirstScalarCost.atomBudget hi originalBound) ^ cap)
    (tilt := CanonicalFirstResidualProfileCost.tiltError firstM
      (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) maskLength activeLength δ₁ δ₂)
    (hrawProfile := p.weight_nonneg) (hfirstCost := hfirstCost) (hcombinedProfile := hcombined)
    (hD := hD) (hE := hE) (hsupportFirst := hsupport)
    (Ray₁ := PUnit) (Ray₂ := PUnit)
    (phase₁ := fun _ => (1 : Circle)) (χ₁ := χ)
    (phase₂ := fun _ => (1 : Circle)) (χ₂ := j.2.1)
    (analyticLeft := analyticLeft) (analyticRight := analyticRight)
    (heightLeft := heightLeft) (heightRight := heightRight)

end LiteralRightPoolPassiveIndex

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftPoolPassiveNormalizationIndex
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightPoolPassiveNormalizationIndex
