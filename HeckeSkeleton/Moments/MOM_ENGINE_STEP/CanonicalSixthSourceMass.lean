import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualSourceMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionFamilyMass

set_option linter.unusedSectionVars false

/-!
# The actual source-image weight after complete sixth-root deletion

These are the literal prepared direct and supported amplified sources.
The original scalar identities and real arithmetic-index projections are
reused unchanged.  The capacity inputs, however, are the full-deletion
inputs of these same chosen children: width plus the root and allowance
minus the root are paid by SixthDeletionScalarMass.

The original common/frozen/removed atom windows supply the scalar
constant.  The original first profile pays the first source exponent.
The original pool tag pays its actual moving prime norm once.  The
result is exactly the pointwise argument of the existing source-image
kernel mass theorem, with no aggregate mass or branch-bound premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup CommonSupportMass

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
local instance canonicalSixthSourceMassCircleCharacterFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

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
theorem canonical_direct_sixth_outer_index_weight
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
    (hn : ∀ u, 0 < (raw).rows.rightMultiplicity u)
    (anchor : ((raw).rows.restrictRows (fun h => ¬(extract i).leaf.exceptional h)).rows)
    (bindingL : (LC).OriginalSixthLengthBinding d a step (G.atBase (LF).source.base ((raw).left_base _))
      (idealLogLength (LF).source.base
        (secondSixthRootIdeal (raw).rows.primes (raw).rows.leftMultiplicity (raw).rows.rightMultiplicity).val))
    (bindingR : (RC).OriginalSixthLengthBinding d a step
      (G.swapSecond.atBase (RF).source.base ((raw).right_base _))
      (idealLogLength (RF).source.base
        (secondSixthRootIdeal (raw).rows.swapColumns.primes (raw).rows.swapColumns.leftMultiplicity
          (raw).rows.swapColumns.rightMultiplicity).val))
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
      bindingL.capacityInput (costs).rowMass hn anchor hsecond hopposite hunit hstep mesh hmesh hfit atomsL)
    (hcapacityR : (((raw).withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput ((costs).rowMass.swapColumns hn) (costs).rowMass.left_positive anchor
        hopposite hsecond hunit hstep mesh hmesh hfit atomsR)
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
theorem canonical_amplified_sixth_outer_index_weight
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
    (hn : ∀ u, 0 < (raw).rows.rightMultiplicity u)
    (anchor : ((raw).rows.restrictRows (fun h => ¬(extract i).leaf.exceptional h)).rows)
    (bindingL : (LC).OriginalSixthLengthBinding d a step (G.atBase (LF).source.base ((raw).left_base _))
      (idealLogLength (LF).source.base
        (secondSixthRootIdeal (raw).rows.primes (raw).rows.leftMultiplicity (raw).rows.rightMultiplicity).val))
    (bindingR : (RC).OriginalSixthLengthBinding d a step
      (G.swapSecond.atBase (RF).source.base ((raw).right_base _))
      (idealLogLength (RF).source.base
        (secondSixthRootIdeal (raw).rows.swapColumns.primes (raw).rows.swapColumns.leftMultiplicity
          (raw).rows.swapColumns.rightMultiplicity).val))
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
      bindingL.capacityInput (costs).rowMass hn anchor hsecond hopposite hunit hstep mesh hmesh hfit atomsL)
    (hcapacityR : (((raw).withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput ((costs).rowMass.swapColumns hn) (costs).rowMass.left_positive anchor
        hopposite hsecond hunit hstep mesh hmesh hfit atomsR)
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

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.canonical_direct_sixth_outer_index_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.canonical_amplified_sixth_outer_index_weight
