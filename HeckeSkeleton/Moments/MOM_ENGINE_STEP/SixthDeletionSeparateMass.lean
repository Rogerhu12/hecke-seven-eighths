import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionScalarMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSeparateAtomMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalFamilyWeights

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Full-deletion mass with the original row scalar retained once

The same already chosen normalized pair is used throughout. Its full
sixth-root capacity budget is expanded before the original Gauss and
first-allowance cancellation. The four common/allocated occurrence
windows pay only their own factors; the actual row profile, including
both stripped first scalars, remains a single literal multiplier.

The normalized prime-bound functions are identified with the constant
one produced by the full-kappa constructor, without transporting children. No row-profile upper bound, total branch mass,
child bound or new capacity choice is an input.
-/

noncomputable section
open HeckePort.IdealMobiusDivisorSum HeckeGeneral.Arithmetic
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ω ψ : HeckeCharacter K}
variable [IsPrincipalIdealRing A.R]

section NormalizedPair

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (frozenL : left.source.FrozenAtomBounds) (frozenR : right.source.FrozenAtomBounds)
variable (IL : (left.arithmeticCalibration calL W frozenL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W frozenR).CapacityInput)
variable (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * boundsR i)
variable (lc : (IL.normalized AL hAL boundsL hBL hfL).Child)
variable (rc : (IR.normalized AR hAR boundsR hBR hfR).Child)
variable (parent : MomentData K ω ψ) (a : RealParameters) (Z step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (hbaseL : left.source.base = Z) (hbaseR : right.source.base = Z)
variable (hn : ∀ i, 0 < R.rightMultiplicity i) (anchor : R.rows)
variable (hsecond : G.ideals.second.val = W.leftIdeal)
variable (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
variable (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
variable (hnonunit : G.ideals.nonunitPart.val = W.nonunitIdeal.val)
variable (bindingL : (left.arithmeticCalibration calL W frozenL).OriginalSixthLengthBinding
  parent a step (G.atBase left.source.base hbaseL)
  (idealLogLength left.source.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
variable (bindingR : (right.arithmeticCalibration calR W frozenR).OriginalSixthLengthBinding
  parent a step (G.swapSecond.atBase right.source.base hbaseR)
  (idealLogLength right.source.base
    (secondSixthRootIdeal R.swapColumns.primes R.swapColumns.leftMultiplicity
      R.swapColumns.rightMultiplicity).val))
variable (atomsL : (left.arithmeticCalibration calL W frozenL).OriginalCapacityAtoms)
variable (atomsR : (right.arithmeticCalibration calR W frozenR).OriginalCapacityAtoms)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (hIL : IL =
  bindingL.capacityInput W hn anchor hsecond hopposite hunit hstep mesh hmesh hfit atomsL)
variable (hIR : IR =
  bindingR.capacityInput (W.swapColumns hn) W.left_positive anchor
    hopposite hsecond hunit hstep mesh hmesh hfit atomsR)

include hnonunit hIL hIR in
/-- This is the actual normalized pair after full deletion.  The two
input equalities identify its existing capacity data; they do not select
new children or new removed sets.  Every scalar inequality is derived
from the original windows below. -/
theorem normalized_sixth_pair_original_allowance_separate
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hboundsL : boundsL = fun _ => 1) (hboundsR : boundsR = fun _ => 1)
    (hleft : k ≤ cap) (hright : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
      frozenL.annulus i * frozenL.profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
      frozenR.annulus i * frozenR.profile i ≤ B)
    (firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (annulus error : ℝ) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z 0 /
        firstNormalization ≤
      ((W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) * orbitalFieldFactor K) *
        Z ^ (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) *
          (1 / (Ideal.absNorm (commonRadical W.leftIdeal W.rightIdeal) : ℝ)) /
            (Ideal.absNorm left.source.allocation.divisor : ℝ) := by
  sorry

variable {branch : TwoDivisorCommonBranch (K := K)}
variable {Ray₁ Ray₂ : Type*}
  [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

include hnonunit hIL hIR in
/-- The original first and second divisors, including both Möbius
coefficients, belong to the same finite arithmetic index as the chosen
normalized pair.  The complete sixth root has already been paid. -/
theorem normalized_sixth_pair_original_index_separate
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hboundsL : boundsL = fun _ => 1) (hboundsR : boundsR = fun _ => 1)
    (hleftCount : k ≤ cap) (hrightCount : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
      W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
      W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ left.source.allocation.keep,
      frozenL.annulus i * frozenL.profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ right.source.allocation.keep,
      frozenR.annulus i * frozenR.profile i ≤ B)
    (firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (annulus error : ℝ) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hdivisor : left.source.allocation.divisor = right.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ left.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ right.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      W.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) W.mask)).val)
    (j : branch.Index)
    (hleft : W.leftIdeal = j.2.2.1.val.1.1)
    (hright : W.rightIdeal = j.2.2.1.val.1.2)
    (hdivisorIndex : left.source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupportFirst : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle) :
    (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
      ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
      ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) *
      (normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z 0 /
        firstNormalization) ≤
      firstCost * ((W.originalFiber : ℝ) * W.profileBound * B ^ (2 * cap) * orbitalFieldFactor K) *
        Z ^ (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) *
          branch.indexWeight j := by
  sorry


end NormalizedPair
section ActualFamily

variable {H U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (leaves : J → ActualHybridLeaf K H U E)
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (arithmetic : ∀ j, (N j).ArithmeticInput)
variable (b : (normalizedFamily leaves (fun j => (N j).withArithmetic (arithmetic j))).active Finset.univ)

local notation "raw" => N b.val.1
local notation "costs" => arithmetic b.val.1
local notation "chosen" => fun j => (N j).withArithmetic (arithmetic j)
local notation "rectangle" => activeRectangle leaves chosen b
local notation "leftFrame" => (raw).rectangles.leftFrame C b.val.2.1
local notation "rightFrame" => (raw).rectangles.rightFrame C b.val.2.2
local notation "rows" => (raw).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)
local notation "LC" => (leftFrame).arithmeticCalibration ((raw).left b.val.2.1).calibration
  (costs).rowMass ((costs).leftAtoms b.val.2.1)
local notation "RC" => (rightFrame).arithmeticCalibration ((raw).right b.val.2.2).calibration
  (costs).rowMass ((costs).rightAtoms b.val.2.2)

variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (hn : ∀ i, 0 <
  ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).rightMultiplicity i)
variable (anchor : ((N b.val.1).rows.restrictRows
  (fun h => ¬(leaves b.val.1).exceptional h)).rows)
variable (hsecond : G.ideals.second.val = (arithmetic b.val.1).rowMass.leftIdeal)
variable (hopposite : G.ideals.secondOpposite.val = (arithmetic b.val.1).rowMass.rightIdeal)
variable (hunit : G.ideals.unitPart.val = (arithmetic b.val.1).rowMass.unitIdeal.val)
variable (hnonunit : G.ideals.nonunitPart.val = (arithmetic b.val.1).rowMass.nonunitIdeal.val)
variable (bindingL :
  (((N b.val.1).rectangles.leftFrame C b.val.2.1).arithmeticCalibration
    ((N b.val.1).left b.val.2.1).calibration (arithmetic b.val.1).rowMass
    ((arithmetic b.val.1).leftAtoms b.val.2.1)).OriginalSixthLengthBinding parent a step
  (G.atBase ((N b.val.1).rectangles.leftFrame C b.val.2.1).source.base
    ((N b.val.1).left_base b.val.2.1))
  (idealLogLength ((N b.val.1).rectangles.leftFrame C b.val.2.1).source.base
    (secondSixthRootIdeal
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).primes
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).leftMultiplicity
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).rightMultiplicity).val))
variable (bindingR :
  (((N b.val.1).rectangles.rightFrame C b.val.2.2).arithmeticCalibration
    ((N b.val.1).right b.val.2.2).calibration (arithmetic b.val.1).rowMass
    ((arithmetic b.val.1).rightAtoms b.val.2.2)).OriginalSixthLengthBinding parent a step
  (G.swapSecond.atBase ((N b.val.1).rectangles.rightFrame C b.val.2.2).source.base
    ((N b.val.1).right_base b.val.2.2))
  (idealLogLength ((N b.val.1).rectangles.rightFrame C b.val.2.2).source.base
    (secondSixthRootIdeal
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).swapColumns.primes
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).swapColumns.leftMultiplicity
      ((N b.val.1).rows.restrictRows (fun h => ¬(leaves b.val.1).exceptional h)).swapColumns.rightMultiplicity).val))
variable (atomsL :
  (((N b.val.1).rectangles.leftFrame C b.val.2.1).arithmeticCalibration
    ((N b.val.1).left b.val.2.1).calibration (arithmetic b.val.1).rowMass
    ((arithmetic b.val.1).leftAtoms b.val.2.1)).OriginalCapacityAtoms)
variable (atomsR :
  (((N b.val.1).rectangles.rightFrame C b.val.2.2).arithmeticCalibration
    ((N b.val.1).right b.val.2.2).calibration (arithmetic b.val.1).rowMass
    ((arithmetic b.val.1).rightAtoms b.val.2.2)).OriginalCapacityAtoms)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (hcapacityL : (((N b.val.1).withArithmetic (arithmetic b.val.1)).left b.val.2.1).capacity =
  bindingL.capacityInput (arithmetic b.val.1).rowMass hn anchor hsecond hopposite hunit
    hstep mesh hmesh hfit atomsL)
variable (hcapacityR : (((N b.val.1).withArithmetic (arithmetic b.val.1)).right b.val.2.2).capacity =
  bindingR.capacityInput ((arithmetic b.val.1).rowMass.swapColumns hn)
    (arithmetic b.val.1).rowMass.left_positive anchor
    hopposite hsecond hunit hstep mesh hmesh hfit atomsR)
variable {branch : TwoDivisorCommonBranch (K := K)}
variable {Ray₁ Ray₂ : Type*}
  [CommGroup Ray₁] [Fintype Ray₁] [CommGroup Ray₂] [Fintype Ray₂]

include hnonunit hcapacityL hcapacityR in
/-- The actual combined family has the original two-divisor index
bound with full sixth-root deletion.  Its local pair is the existing
`activeRectangle`, so both chosen children, their removed sets, data and
Fourier kernels coincide with those in the signed parent estimate.

The outer scalar is the exact source identity, including the first
fibre and the real pool/valuation tag where present.  It is not replaced
by an assumed branch bound. -/
theorem arithmetic_sixth_outer_index_separate
    (hZ : 1 < Z) (cap : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hleftBounds : ((raw).left b.val.2.1).bounds = fun _ => 1)
    (hrightBounds : ((raw).right b.val.2.2).bounds = fun _ => 1)
    (hleftCount : (leaves b.val.1).leftSlots ≤ cap)
    (hrightCount : (leaves b.val.1).rightSlots ≤ cap)
    (hcommonLeft : (costs).commonLeftSlots ≤ cap)
    (hcommonRight : (costs).commonRightSlots ≤ cap)
    (hcommonL : ∀ i ∈ Finset.univ \ (costs).rowMass.leftAtoms.keep,
      (costs).rowMass.leftAtoms.annulus i * (costs).rowMass.leftAtoms.profile i ≤ B)
    (hcommonR : ∀ i ∈ Finset.univ \ (costs).rowMass.rightAtoms.keep,
      (costs).rowMass.rightAtoms.annulus i * (costs).rowMass.rightAtoms.profile i ≤ B)
    (hfrozenL : ∀ i ∈ Finset.univ \ (leftFrame).source.allocation.keep,
      ((costs).leftAtoms b.val.2.1).annulus i * ((costs).leftAtoms b.val.2.1).profile i ≤ B)
    (hfrozenR : ∀ i ∈ Finset.univ \ (rightFrame).source.allocation.keep,
      ((costs).rightAtoms b.val.2.2).annulus i * ((costs).rightAtoms b.val.2.2).profile i ≤ B)
    (firstNormalization : ℝ)
    (hN : firstNormalization =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (annulus error : ℝ) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hdivisor : (leftFrame).source.allocation.divisor = (rightFrame).source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (leftFrame).normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ (rightFrame).normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      (costs).rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (costs).rowMass.mask)).val)
    (j : branch.Index)
    (hleft : (costs).rowMass.leftIdeal = j.2.2.1.val.1.1)
    (hright : (costs).rowMass.rightIdeal = j.2.2.1.val.1.2)
    (hdivisorIndex : (leftFrame).source.allocation.divisor = j.2.2.2.1.val)
    (parentWidth total rawProfile firstCost : ℝ)
    (hfirst : 0 ≤ firstCost)
    (hprofile : rawProfile ≤ firstCost * Z ^ (parentWidth - total))
    (hD : j.1.val.1.1 ≠ 0) (hE : j.1.val.1.2 ≠ 0)
    (hsupportFirst : primeSupport j.1.val.1.1 = primeSupport j.1.val.1.2)
    (phase₁ : Ray₁ × Ray₁ → Circle) (χ₁ : (Ray₁ × Ray₁) →* Circle)
    (phase₂ : Ray₂ × Ray₂ → Circle) (χ₂ : (Ray₂ × Ray₂) →* Circle)
    (factor : ℝ) (hfactor : 0 ≤ factor)
    (houter : (leaves b.val.1).weight / Z ^ parentWidth =
      factor *
        (firstOriginalAllowanceWeight Z parentWidth total rawProfile j.1.val.1.1 j.1.val.1.2 *
          ‖(moebius j.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₁ phase₁ χ₁‖ *
          ‖(moebius j.2.2.2.1.val : ℂ)‖ * ‖fixedPhaseCoefficient Ray₂ phase₂ χ₂‖) /
        firstNormalization) :
    outerWeights leaves b.val *
        (normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      factor *
        (firstCost * (((costs).rowMass.originalFiber : ℝ) * (costs).rowMass.profileBound * B ^ (2 * cap) * orbitalFieldFactor K) *
          Z ^ (G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh) *
            branch.indexWeight j) := by
  sorry

end ActualHybridFamily
end ActualFamily


end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalized_sixth_pair_original_allowance_separate

#print axioms HeckeSkeleton.Moments.EngineStep.normalized_sixth_pair_original_index_separate

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.arithmetic_sixth_outer_index_separate
