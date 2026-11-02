import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSourceImageKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalFamilyWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolMonotonicity

set_option linter.unusedSectionVars false

/-!
# Original windows give the actual source-image scalar

The source carrier below is the literal prepared source. Its first
normalization is computed from the original common ideals. Constant
common-atom extraction retains its scalar, and the combined normalized
family uses the same already chosen capacity children.

The original nominal construction supplies the allowance. The constant
fields of the original atom producers supply the atom window. Neither
a rectangle weight bound nor a normalized-kernel mass is an input.
The numerical constant and profile exponent use only fixed original
fibre caps, the annulus, the single-prime cost and the profile orders.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup CommonSupportMass

namespace CanonicalActualSourceMass

variable (K : Type) [Field K] [NumberField K]

def atomDegree (dAmplitude dRow : ℕ) : ℕ := max (2 * dAmplitude) dRow

def weightDegree (cap dFirst dAmplitude dRow : ℕ) : ℕ :=
  dFirst + atomDegree dAmplitude dRow * (3 * cap + 1)

def weightConstant (cap : ℕ) (annulus primeCost firstFiber secondFiber rowFiber : ℝ) : ℝ :=
  (firstFiber * secondFiber) * rowFiber * max 1 (orbitalFieldFactor K) *
    (max 1 (max annulus primeCost)) ^ (3 * cap + 1)

theorem weightConstant_pos (cap : ℕ)
    (annulus primeCost firstFiber secondFiber rowFiber : ℝ)
    (hfirst : 1 ≤ firstFiber) (hsecond : 1 ≤ secondFiber) (hrow : 1 ≤ rowFiber) :
    0 < weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber := by
  sorry

/-- Only the original atom budget and three individual orbital-fibre
caps enter this estimate. No family or child weight occurs here. -/
theorem atomCoefficient_le (cap dFirst dAmplitude dRow : ℕ)
    (annulus amplitude rowCost primeCost profile scalar firstFiber secondFiber rowFiber : ℝ)
    (originalFiber : ℕ) (hannulus : 0 ≤ annulus) (hprofile : 1 ≤ profile)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hscalar : scalar ≤ firstFiber * secondFiber)
    (hfirst : 1 ≤ firstFiber) (hsecond : 1 ≤ secondFiber) (hrow : 1 ≤ rowFiber)
    (hfiber : (originalFiber : ℝ) ≤ rowFiber) :
    scalar * (profile ^ dFirst *
      ((originalFiber : ℝ) *
        OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost ^
          (3 * cap + 1) * orbitalFieldFactor K)) ≤
      weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ weightDegree cap dFirst dAmplitude dRow := by
  sorry

end CanonicalActualSourceMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
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
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Z : ℝ} {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
local instance canonicalActualSourceMassCircleCharacterFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.prepared.CoverHybridPredicates L)

local notation "firstNormalization" => s.canonicalNormalization hZ total
local notation "Live" => R.prepared.liveLeaves L exceptional firstNormalization

variable (extract : ∀ i : (R.prepared.liveLeaves L exceptional (s.canonicalNormalization hZ total)),
  (R.prepared.parentLeaf L exceptional (s.canonicalNormalization hZ total) i.val).ConstantAtomExtraction)
local notation "leaves" => fun i : Live => (extract i).leaf
variable {I : (R.prepared.liveLeaves L exceptional (s.canonicalNormalization hZ total)) → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable (N : ∀ i : (R.prepared.liveLeaves L exceptional (s.canonicalNormalization hZ total)), (extract i).leaf.NormalizationData (ι := I i)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (arithmetic : ∀ i, (N i).ArithmeticInput)
local notation "chosen" => fun i => (N i).withArithmetic (arithmetic i)
local notation "families" => fun i => (chosen i).family
local notation "Labels" => R.prepared.arithmeticLabels L hcap exceptional firstNormalization

variable (b : (ActualHybridFamily.normalizedFamily (fun i : (R.prepared.liveLeaves L exceptional (s.canonicalNormalization hZ total)) => (extract i).leaf) (fun i => (N i).withArithmetic (arithmetic i))).active Finset.univ)
local notation "i" => b.val.1
local notation "raw" => N i
local notation "costs" => arithmetic i
local notation "LF" => (raw).rectangles.leftFrame C b.val.2.1
local notation "RF" => (raw).rectangles.rightFrame C b.val.2.2
local notation "LC" => (LF).arithmeticCalibration ((raw).left b.val.2.1).calibration
  (costs).rowMass ((costs).leftAtoms b.val.2.1)
local notation "RC" => (RF).arithmeticCalibration ((raw).right b.val.2.2).calibration
  (costs).rowMass ((costs).rightAtoms b.val.2.2)

/-- The remaining pointwise hypothesis of the actual direct image-mass
theorem follows from original nominal, atom and profile windows. Its
index and scalar are computed from this very prepared source. -/
theorem canonical_direct_outer_index_weight
    (dFirst dAmplitude dRow : ℕ)
    (profile annulus amplitude rowCost primeCost firstFiber secondFiber rowFiber ε : ℝ)
    (hprofile : 1 ≤ profile) (hannulus : 1 ≤ annulus)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hfirstFiber : 1 ≤ firstFiber) (hsecondFiber : 1 ≤ secondFiber) (hrowFiber : 1 ≤ rowFiber)
    (hfirstCap : (s.fiber : ℝ) ≤ firstFiber)
    (hsecondCap : (R.prepared (i).val.1 (i).val.2.1).directScalarAt L L (i).val.2.2 ≤ secondFiber)
    (hrowCap : ((costs).rowMass.originalFiber : ℝ) ≤ rowFiber)
    (step error mesh : ℝ) (G : OriginalNominalGeometry (K := K) a Z step)
    (htag : G.tag = .direct)
    (hsecond : G.ideals.second.val = (costs).rowMass.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = (costs).rowMass.rightIdeal)
    (hunit : G.ideals.unitPart.val = (costs).rowMass.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = (costs).rowMass.nonunitIdeal.val)
    (bindingL : (LC).OriginalLengthBinding d a step (G.atBase (LF).source.base ((raw).left_base _)))
    (bindingR : (RC).OriginalLengthBinding d a step
      (G.swapSecond.atBase (RF).source.base ((raw).right_base _)))
    (atomsL : (LC).OriginalCapacityAtoms) (atomsR : (RC).OriginalCapacityAtoms)
    (hstep : 0 < step) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hmesh : 0 ≤ mesh) (hfit : d.geometry.fitsMesh mesh)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hcapacityL : (((raw).withArithmetic costs).left b.val.2.1).capacity =
      bindingL.capacityInput hstep mesh hmesh hfit atomsL)
    (hcapacityR : (((raw).withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput hstep mesh hmesh hfit atomsR)
    (hdivisor : (LF).source.allocation.divisor = (RF).source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (LF).normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (RF).normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      (costs).rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (costs).rowMass.mask)).val)
    (hnormalization : R.prepared.firstAllowanceAt L total (i).val =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (herrorBudget : error ≤ 3 * ε / 40) (hmeshBudget : mesh ≤ ε / 8)
    (hleftCount : (extract i).leaf.leftSlots ≤ cap)
    (hrightCount : (extract i).leaf.rightSlots ≤ cap)
    (hcommonLeft : (costs).commonLeftSlots ≤ cap) (hcommonRight : (costs).commonRightSlots ≤ cap)
    (hrow : (costs).rowMass.profileBound = rowCost)
    (hcommonLA : ∀ j, (costs).rowMass.leftAtoms.annulus j = annulus)
    (hcommonLP : ∀ j, (costs).rowMass.leftAtoms.profile j = amplitude ^ 2)
    (hcommonRA : ∀ j, (costs).rowMass.rightAtoms.annulus j = annulus)
    (hcommonRP : ∀ j, (costs).rowMass.rightAtoms.profile j = amplitude ^ 2)
    (hfrozenLA : ∀ j, ((costs).leftAtoms b.val.2.1).annulus j = annulus)
    (hfrozenLP : ∀ j, ((costs).leftAtoms b.val.2.1).profile j = amplitude ^ 2)
    (hfrozenRA : ∀ j, ((costs).rightAtoms b.val.2.2).annulus j = annulus)
    (hfrozenRP : ∀ j, ((costs).rightAtoms b.val.2.2).profile j = amplitude ^ 2)
    (hprimeL : ∀ j, ((raw).left b.val.2.1).bounds j = primeCost)
    (hprimeR : ∀ j, ((raw).right b.val.2.2).bounds j = primeCost)
    (hleftIdeal : (costs).rowMass.leftIdeal = (R.prepared.commonLabel L (i).val).1)
    (hrightIdeal : (costs).rowMass.rightIdeal = (R.prepared.commonLabel L (i).val).2)
    (hsecondDivisor : (LF).source.allocation.divisor = R.prepared.innerDivisor L (i).val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pieces (i).val.1 (i).val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total (i).val.1 (i).val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow * Z ^ (ε / 4)) *
        (Labels).carrier.indexWeight ((Labels).rectangleIndex families b) := by
  sorry

end ActualDirectFirstSource.SecondStages

section Amplified

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

/-- The nominal tag records the very same original prime and valuation. -/
def PoolSourceTag.nominalTag : PoolSourceTag P → OriginalNominalTag K
  | .inl _ => .main
  | .inr (.inl p) => .error .one p.val.val
  | .inr (.inr (.inl p)) => .error .six p.val.val
  | .inr (.inr (.inr p)) => .error .seven p.val.val

namespace OriginalArithmeticLabels

variable {J : Type*} [Fintype J] {cap : ℕ}
variable (labels : OriginalArithmeticLabels K J cap)
variable (tag : J → Option (ℕ × ExteriorPrime A))
variable (tag_mem : ∀ j n p, tag j = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes)

theorem amplified_harmonicWeight_eq_indexWeight (j : J) :
    AmplifiedCommonIndex.harmonicWeight P (labels.mainCarrier tag) (labels.errorCarrier tag)
      (labels.amplifiedIndex tag P tag_mem j) = labels.carrier.indexWeight (labels.index j) := by
  sorry

theorem amplified_originalTagWeight_eq (M B : ℝ) (j : J) :
    AmplifiedCommonIndex.originalTagWeight P M B (labels.mainCarrier tag) (labels.errorCarrier tag)
      (labels.amplifiedIndex tag P tag_mem j) =
      (4 / P.rowDensity M B) *
        (match tag j with
        | none => (M + 6 * ell) / (ell / 2)
        | some q => FirstGaussPoolData.localErrorWeight q.2 q.1) := by
  sorry

end OriginalArithmeticLabels

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := U) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def originalRowExponentAt (j : R.CoveredLeafKey L) : ℝ :=
  match j.2.2.2.2 with
  | .inl _ => ((s.pools j.1 j.2.1).divisorPools.leftData j.2.2.1).rowExponent
  | .inr _ => ((s.pools j.1 j.2.1).divisorPools.rightData j.2.2.1).rowExponent

def originalFrozenExponentAt (j : R.CoveredLeafKey L) : ℝ :=
  match j.2.2.2.2 with
  | .inl _ => ((s.pools j.1 j.2.1).divisorPools.leftData j.2.2.1).frozenExponent
  | .inr _ => ((s.pools j.1 j.2.1).divisorPools.rightData j.2.2.1).frozenExponent

def originalSecondFiberAt (j : R.CoveredLeafKey L) : ℕ :=
  match j.2.2.2.2 with
  | .inl k =>
    let stage := (R j.1 j.2.1).left j.2.2.1 j.2.2.2.1
    let cover := (s.pools j.1 j.2.1).leftSourceCovers L j.2.2.1 j.2.2.2.1
    (stage.tag (stage.leafTag cover k)).fiber
  | .inr k =>
    let stage := (R j.1 j.2.1).right j.2.2.1 j.2.2.2.1
    let cover := (s.pools j.1 j.2.1).rightSourceCovers L j.2.2.1 j.2.2.2.1
    (stage.tag (stage.leafTag cover k)).fiber

def originalNominalTagAt (j : R.CoveredLeafKey L) : OriginalNominalTag K :=
  match j.2.2.2.2 with
  | .inl k =>
    PoolSourceTag.nominalTag (((R j.1 j.2.1).left j.2.2.1 j.2.2.2.1).leafTag
      ((s.pools j.1 j.2.1).leftSourceCovers L j.2.2.1 j.2.2.2.1) k)
  | .inr k =>
    PoolSourceTag.nominalTag (((R j.1 j.2.1).right j.2.2.1 j.2.2.2.1).leafTag
      ((s.pools j.1 j.2.1).rightSourceCovers L j.2.2.1 j.2.2.2.1) k)

theorem originalRowExponentAt_nonneg (j : R.CoveredLeafKey L) :
    0 ≤ R.originalRowExponentAt L j := by
  sorry

variable {cap : ℕ} (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (normalization : s.Normalization)

/-- The exact original pool scalar uses the selected local norm
windows. No comparison with the uniform windows is assumed here. -/
theorem originalScalarAt_eq_originalTagWeight
    (i : R.liveLeaves L exceptional normalization) :
    R.originalScalarAt L i.val =
      (((s.fiber : ℝ) * (R.originalSecondFiberAt L i.val : ℝ)) / 2) *
        AmplifiedCommonIndex.originalTagWeight P (R.originalRowExponentAt L i.val)
          (R.originalFrozenExponentAt L i.val)
          ((R.arithmeticLabels L hcap exceptional normalization).mainCarrier
            (R.arithmeticTag L exceptional normalization))
          ((R.arithmeticLabels L hcap exceptional normalization).errorCarrier
            (R.arithmeticTag L exceptional normalization))
          (R.arithmeticIndex L hcap exceptional normalization i) := by
  sorry

/-- The nominal moving length and main-pool length are already paid
by the amplified index of the same original leaf. -/
theorem originalNominalTagAt_movingLength
    (i : R.liveLeaves L exceptional normalization) :
    (R.originalNominalTagAt L i.val).movingLength Z +
        (R.originalNominalTagAt L i.val).poolLength (3 * ell) =
      AmplifiedCommonIndex.movingLength P
        ((R.arithmeticLabels L hcap exceptional normalization).mainCarrier
          (R.arithmeticTag L exceptional normalization))
        ((R.arithmeticLabels L hcap exceptional normalization).errorCarrier
          (R.arithmeticTag L exceptional normalization))
        (R.arithmeticIndex L hcap exceptional normalization i) := by
  sorry

end ActualFirstSource.SecondStages
namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := U) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.supported.gated.CoverHybridPredicates L)

local notation "firstNormalization" => s.canonicalNormalization hZ total
local notation "Live" => R.supported.gated.liveLeaves L exceptional firstNormalization

variable (extract : ∀ i : (R.supported.gated.liveLeaves L exceptional (s.canonicalNormalization hZ total)),
  (R.supported.gated.parentLeaf L exceptional (s.canonicalNormalization hZ total) i.val).ConstantAtomExtraction)
local notation "leaves" => fun i : Live => (extract i).leaf
variable {I : (R.supported.gated.liveLeaves L exceptional (s.canonicalNormalization hZ total)) → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable (N : ∀ i : (R.supported.gated.liveLeaves L exceptional (s.canonicalNormalization hZ total)), (extract i).leaf.NormalizationData (ι := I i)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (arithmetic : ∀ i, (N i).ArithmeticInput)
local notation "chosen" => fun i => (N i).withArithmetic (arithmetic i)
local notation "families" => fun i => (chosen i).family
local notation "Labels" => R.supported.gated.arithmeticLabels L hcap exceptional firstNormalization
local notation "Tags" => R.supported.gated.arithmeticTag L exceptional firstNormalization
local notation "tagMem" => R.supported.gated.arithmeticTag_mem L exceptional firstNormalization
local notation "Main" => (Labels).mainCarrier Tags
local notation "Errors" => (Labels).errorCarrier Tags

variable (b : (ActualHybridFamily.normalizedFamily (fun i : (R.supported.gated.liveLeaves L exceptional (s.canonicalNormalization hZ total)) => (extract i).leaf) (fun i => (N i).withArithmetic (arithmetic i))).active Finset.univ)
local notation "i" => b.val.1
local notation "raw" => N i
local notation "costs" => arithmetic i
local notation "LF" => (raw).rectangles.leftFrame C b.val.2.1
local notation "RF" => (raw).rectangles.rightFrame C b.val.2.2
local notation "LC" => (LF).arithmeticCalibration ((raw).left b.val.2.1).calibration
  (costs).rowMass ((costs).leftAtoms b.val.2.1)
local notation "RC" => (RF).arithmeticCalibration ((raw).right b.val.2.2).calibration
  (costs).rowMass ((costs).rightAtoms b.val.2.2)

/-- The actual amplified image uses its original prime and valuation.
Its moving norm is paid by that same index; the two original local
window bounds compare one density with the fixed uniform density. -/
theorem canonical_amplified_outer_index_weight
    (dFirst dAmplitude dRow : ℕ)
    (profile annulus amplitude rowCost primeCost firstFiber secondFiber rowFiber ε : ℝ)
    (hprofile : 1 ≤ profile) (hannulus : 1 ≤ annulus)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hfirstFiber : 1 ≤ firstFiber) (hsecondFiber : 1 ≤ secondFiber) (hrowFiber : 1 ≤ rowFiber)
    (hfirstCap : (s.fiber : ℝ) ≤ firstFiber)
    (hsecondCap : (R.supported.gated.originalSecondFiberAt L (i).val : ℝ) ≤ secondFiber)
    (hrowCap : ((costs).rowMass.originalFiber : ℝ) ≤ rowFiber)
    (step error mesh : ℝ) (G : OriginalNominalGeometry (K := K) a Z step)
    (htag : G.tag = R.supported.gated.originalNominalTagAt L (i).val)
    (hstepPool : step = 3 * ell)
    (Mmax Bmax : ℝ)
    (hM : R.supported.gated.originalRowExponentAt L (i).val ≤ Mmax)
    (hB : R.supported.gated.originalFrozenExponentAt L (i).val ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax)
    (hsecond : G.ideals.second.val = (costs).rowMass.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = (costs).rowMass.rightIdeal)
    (hunit : G.ideals.unitPart.val = (costs).rowMass.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = (costs).rowMass.nonunitIdeal.val)
    (bindingL : (LC).OriginalLengthBinding d a step (G.atBase (LF).source.base ((raw).left_base _)))
    (bindingR : (RC).OriginalLengthBinding d a step
      (G.swapSecond.atBase (RF).source.base ((raw).right_base _)))
    (atomsL : (LC).OriginalCapacityAtoms) (atomsR : (RC).OriginalCapacityAtoms)
    (hstep : 0 < step) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hmesh : 0 ≤ mesh) (hfit : d.geometry.fitsMesh mesh)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hcapacityL : (((raw).withArithmetic costs).left b.val.2.1).capacity =
      bindingL.capacityInput hstep mesh hmesh hfit atomsL)
    (hcapacityR : (((raw).withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput hstep mesh hmesh hfit atomsR)
    (hdivisor : (LF).source.allocation.divisor = (RF).source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (LF).normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (RF).normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      (costs).rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (costs).rowMass.mask)).val)
    (hnormalization : R.supported.gated.firstAllowanceAt L total (i).val =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (herrorBudget : error ≤ 3 * ε / 40) (hmeshBudget : mesh ≤ ε / 8)
    (hleftCount : (extract i).leaf.leftSlots ≤ cap)
    (hrightCount : (extract i).leaf.rightSlots ≤ cap)
    (hcommonLeft : (costs).commonLeftSlots ≤ cap) (hcommonRight : (costs).commonRightSlots ≤ cap)
    (hrow : (costs).rowMass.profileBound = rowCost)
    (hcommonLA : ∀ j, (costs).rowMass.leftAtoms.annulus j = annulus)
    (hcommonLP : ∀ j, (costs).rowMass.leftAtoms.profile j = amplitude ^ 2)
    (hcommonRA : ∀ j, (costs).rowMass.rightAtoms.annulus j = annulus)
    (hcommonRP : ∀ j, (costs).rowMass.rightAtoms.profile j = amplitude ^ 2)
    (hfrozenLA : ∀ j, ((costs).leftAtoms b.val.2.1).annulus j = annulus)
    (hfrozenLP : ∀ j, ((costs).leftAtoms b.val.2.1).profile j = amplitude ^ 2)
    (hfrozenRA : ∀ j, ((costs).rightAtoms b.val.2.2).annulus j = annulus)
    (hfrozenRP : ∀ j, ((costs).rightAtoms b.val.2.2).profile j = amplitude ^ 2)
    (hprimeL : ∀ j, ((raw).left b.val.2.1).bounds j = primeCost)
    (hprimeR : ∀ j, ((raw).right b.val.2.2).bounds j = primeCost)
    (hleftIdeal : (costs).rowMass.leftIdeal = (R.supported.gated.commonLabel L (i).val).1)
    (hrightIdeal : (costs).rowMass.rightIdeal = (R.supported.gated.commonLabel L (i).val).2)
    (hsecondDivisor : (LF).source.allocation.divisor = R.supported.gated.innerDivisor L (i).val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pools (i).val.1 (i).val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total (i).val.1 (i).val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow * Z ^ (ε / 4)) *
        amplifiedIndexWeight P Mmax Bmax Main Errors
          ((Labels).rectangleAmplifiedIndex families P Tags tagMem b) := by
  sorry

end ActualFirstSource.SecondStages

end Amplified
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualSourceMass.atomCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.canonical_direct_outer_index_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalScalarAt_eq_originalTagWeight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalNominalTagAt_movingLength

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.canonical_amplified_outer_index_weight
