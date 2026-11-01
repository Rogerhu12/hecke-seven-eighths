import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualSourceMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalNormalizedPrimeAtoms

/-!
# The actual source weights with the original prime loss

Both exports use the same prepared or supported-and-gated source, the
same common and allocation atoms, and the same chosen children as the
original source-mass producer. The normalized prime costs may now vary
with the original scale. Their bound is paid by the same enlarged
profile used for the original logarithmic atoms.

Only the fixed coefficient of that prime bound enters weightConstant.
The full original prime cost remains in every actual atom and removed
product. In particular Cprime * Z ^ epsPrime is not passed off as a
fixed constant. CanonicalNormalizedPrimeAtoms constructs that cost from
the independent original canonical-prime theorem and proves its small
power fits inside the same profile envelope.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup CommonSupportMass

namespace CanonicalPrimeActualSourceMass

open CanonicalActualSourceMass

variable (K : Type) [Field K] [NumberField K]

/-- Only the original atom budget and three individual orbital-fibre
caps enter this estimate. No family or child weight occurs here. -/
theorem atomCoefficient_le (cap dFirst dAmplitude dRow dPrime : ℕ)
    (annulus amplitude rowCost primeCost fixedPrimeCost profile scalar firstFiber secondFiber rowFiber : ℝ)
    (originalFiber : ℕ) (hannulus : 0 ≤ annulus) (hprofile : 1 ≤ profile)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hprimeCost : primeCost ≤ fixedPrimeCost * profile ^ dPrime)
    (hscalar : scalar ≤ firstFiber * secondFiber)
    (hfirst : 1 ≤ firstFiber) (hsecond : 1 ≤ secondFiber) (hrow : 1 ≤ rowFiber)
    (hfiber : (originalFiber : ℝ) ≤ rowFiber) :
    scalar * (profile ^ dFirst *
      ((originalFiber : ℝ) *
        OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost ^
          (3 * cap + 1) * orbitalFieldFactor K)) ≤
      weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber *
        profile ^ weightDegree cap dFirst dAmplitude (max dRow dPrime) := by
  let B := OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost
  let C := max 1 (max annulus fixedPrimeCost)
  have hB : 0 ≤ B :=
    zero_le_one.trans (OriginalProfileAtomBounds.atomBudget_one _ _ _ _)
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hP : 0 ≤ profile := zero_le_one.trans hprofile
  have hR : 0 ≤ rowFiber := zero_le_one.trans hrow
  have hF : 0 ≤ firstFiber * secondFiber :=
    mul_nonneg (zero_le_one.trans hfirst) (zero_le_one.trans hsecond)
  have hOrbital := orbitalFieldFactor_nonneg K
  have hBbound : B ≤ C * profile ^ atomDegree dAmplitude (max dRow dPrime) :=
    CanonicalNormalizedPrimeAtoms.atomBudget_le_profile_power_with_prime
      annulus amplitude rowCost primeCost fixedPrimeCost profile dAmplitude dRow dPrime
      hannulus hprofile hamplitude hamp hrowCost hprimeCost
  have hpow := pow_le_pow_left₀ hB hBbound (3 * cap + 1)
  have hrowBound := mul_le_mul hfiber hpow (pow_nonneg hB _) hR
  have hcost := mul_le_mul hrowBound (le_max_right 1 (orbitalFieldFactor K))
    hOrbital (mul_nonneg hR (pow_nonneg (mul_nonneg hC (pow_nonneg hP _)) _))
  have hcoeff := mul_le_mul hscalar
    (mul_le_mul_of_nonneg_left hcost (pow_nonneg hP _))
    (mul_nonneg (pow_nonneg hP _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB _)) hOrbital)) hF
  calc
    _ ≤ (firstFiber * secondFiber) * (profile ^ dFirst *
        (rowFiber * (C * profile ^ atomDegree dAmplitude (max dRow dPrime)) ^ (3 * cap + 1) *
          max 1 (orbitalFieldFactor K))) := hcoeff
    _ = _ := by
      simp only [weightConstant, weightDegree, mul_pow, ← pow_mul, pow_add, C] <;> ring

end CanonicalPrimeActualSourceMass

namespace InternalMassAssembly.ProfileWindows

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]

/-- Enlarging the common scalar profile budget leaves the actual
family, child radii, kernels, outer weights and all degrees unchanged.
This permits adding the fixed prime constant to the previously chosen
analytic constant after both have been selected before Z. -/
def monoProfile {Λ : Type*} {Z : ℝ}
    {family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z}
    {labels : Finset Λ} {F₁ : Λ → 𝓢(U, ℂ)} {F₂ : Λ → 𝓢(E, ℂ)}
    {outer B₁ B₂ : Λ → ℝ} {P P' : ℝ}
    {cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ : ℕ}
    {seminorms₁ seminorms₂ : Finset (ℕ × ℕ)}
    (W : InternalMassAssembly.ProfileWindows family labels F₁ F₂ outer B₁ B₂ P
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂)
    (hP : 0 ≤ P) (hPP' : P ≤ P') :
    InternalMassAssembly.ProfileWindows family labels F₁ F₂ outer B₁ B₂ P'
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ :=
  { W with
    left_radius_power := fun b hb =>
      (W.left_radius_power b hb).trans (pow_le_pow_left₀ hP hPP' _)
    right_radius_power := fun b hb =>
      (W.right_radius_power b hb).trans (pow_le_pow_left₀ hP hPP' _)
    first_kernel_power := fun b hb =>
      (W.first_kernel_power b hb).trans (pow_le_pow_left₀ hP hPP' _)
    second_kernel_power := fun b hb =>
      (W.second_kernel_power b hb).trans (pow_le_pow_left₀ hP hPP' _) }

end InternalMassAssembly.ProfileWindows

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
local instance canonicalPrimeActualSourceMassCircleCharacterFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

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
theorem canonical_direct_outer_index_weight_prime_loss
    (dFirst dAmplitude dRow dPrime : ℕ)
    (profile annulus amplitude rowCost primeCost fixedPrimeCost firstFiber secondFiber rowFiber ε : ℝ)
    (hprofile : 1 ≤ profile) (hannulus : 1 ≤ annulus)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hprimeCost : primeCost ≤ fixedPrimeCost * profile ^ dPrime)
    (hfirstFiber : 1 ≤ firstFiber) (hsecondFiber : 1 ≤ secondFiber) (hrowFiber : 1 ≤ rowFiber)
    (hfirstCap : (s.fiber : ℝ) ≤ firstFiber)
    (hsecondCap : (R.prepared i.val.1 i.val.2.1).directScalarAt L L i.val.2.2 ≤ secondFiber)
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
    (hnormalization : R.prepared.firstAllowanceAt L total i.val =
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
    (hleftIdeal : (costs).rowMass.leftIdeal = (R.prepared.commonLabel L i.val).1)
    (hrightIdeal : (costs).rowMass.rightIdeal = (R.prepared.commonLabel L i.val).2)
    (hsecondDivisor : (LF).source.allocation.divisor = R.prepared.innerDivisor L i.val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pieces i.val.1 i.val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total i.val.1 i.val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude (max dRow dPrime) * Z ^ (ε / 4)) *
        (Labels).carrier.indexWeight ((Labels).rectangleIndex families b) := by
  let j := (Labels).rectangleIndex families b
  let B := OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost
  let remaining := G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh
  have allowance := OriginalPairAllowanceWindow.ofNominalGeometry LF RF
    ((raw).left b.val.2.1).calibration ((raw).right b.val.2.2).calibration (costs).rowMass
    ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
    d a Z step G ((raw).left_base _) ((raw).right_base _)
    hsecond hopposite hunit hnonunit bindingL bindingR atomsL atomsR hstep annulus error mesh
    herror hthreshold hmesh hfit hannulusLL hannulusLR hannulusRL hannulusRR
    hsupport hrawL hrawR hwidthL hwidthR hdivisor hscaleL hscaleR hradius
  have pairWindow : OriginalPairAllowanceWindow LF RF
      ((raw).left b.val.2.1).calibration ((raw).right b.val.2.2).calibration (costs).rowMass
      ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
      (((raw).withArithmetic costs).left b.val.2.1).capacity
      (((raw).withArithmetic costs).right b.val.2.2).capacity
      Z (R.prepared.firstAllowanceAt L total i.val) remaining := by
    simpa only [hcapacityL, hcapacityR, hnormalization] using allowance
  have atomWindow := CanonicalCapacityKernelMass.OriginalAtomWindow.ofConstantOriginalAtoms
    LF RF (costs).rowMass ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
    ((raw).left b.val.2.1).bounds ((raw).right b.val.2.2).bounds
    cap annulus amplitude rowCost primeCost hleftCount hrightCount hcommonLeft hcommonRight
    hrow hcommonLA hcommonLP hcommonRA hcommonRP hfrozenLA hfrozenLP hfrozenRA hfrozenRP hprimeL hprimeR
  have hfirst := actual_common_pair_properties _ _ _ _ i.val.1
  have hdivisorIndex : (LF).source.allocation.divisor = j.2.2.2.1.val := by
    change (LF).source.allocation.divisor = ((Labels).allocation i).1
    rw [R.prepared.arithmeticLabels_secondDivisor]
    exact hsecondDivisor
  have hinnerIndex : j.2.2.2.1.val = R.prepared.innerDivisor L i.val :=
    R.prepared.arithmeticLabels_secondDivisor L hcap exceptional firstNormalization i
  have houter := R.prepared.extracted_parentLeaf_weight_original_relative L hZ total
    exceptional parentWidth i.val (extract i)
  rw [← hinnerIndex] at houter
  have hscalar0 : 0 ≤ R.prepared.originalScalarAt L i.val := by
    unfold originalScalarAt FirstBlockDirectData.SecondStages.directScalarAt
    split <;> positivity
  have hraw := ActualHybridFamily.arithmetic_outer_index_weight leaves N arithmetic b pairWindow
    hZ cap B (OriginalProfileAtomBounds.atomBudget_one _ _ _ _) atomWindow
    j hleftIdeal hrightIdeal hdivisorIndex parentWidth (total i.val.1 i.val.2.1)
    (s.pieces i.val.1 i.val.2.1).weightBound (profile ^ dFirst)
    (pow_nonneg (zero_le_one.trans hprofile) _) hfirstProfile hfirst.1 hfirst.2.1 hfirst.2.2
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) i.val.2.2.2.1
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle))
    (R.prepared.secondPhaseAt L i.val) (R.prepared.originalScalarAt L i.val) hscalar0 houter
  have hscalar : R.prepared.originalScalarAt L i.val ≤ firstFiber * secondFiber := by
    have hs : 0 ≤ (R.prepared i.val.1 i.val.2.1).directScalarAt L L i.val.2.2 := by
      unfold FirstBlockDirectData.SecondStages.directScalarAt
      split <;> exact Nat.cast_nonneg _
    have hprod : 0 ≤ firstFiber * secondFiber :=
      mul_nonneg (zero_le_one.trans hfirstFiber) (zero_le_one.trans hsecondFiber)
    calc
      _ ≤ (firstFiber * secondFiber) / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hfirstCap hsecondCap hs (zero_le_one.trans hfirstFiber)) (by norm_num)
      _ ≤ firstFiber * secondFiber := by linarith
  have hcoefficient := CanonicalPrimeActualSourceMass.atomCoefficient_le K cap dFirst dAmplitude dRow dPrime
    annulus amplitude rowCost primeCost fixedPrimeCost profile (R.prepared.originalScalarAt L i.val)
    firstFiber secondFiber rowFiber (costs).rowMass.originalFiber (zero_le_one.trans hannulus)
    hprofile hamplitude hamp hrowCost hprimeCost hscalar hfirstFiber hsecondFiber hrowFiber hrowCap
  have hremaining : remaining ≤ ε / 4 := by
    simpa only [remaining, OriginalNominalGeometry.skeleton, htag,
      OriginalNominalTag.movingLength, OriginalNominalTag.poolLength, zero_add, add_zero] using
      OriginalPairAllowanceProduction.remaining_le_quarter 0 0 error mesh ε herrorBudget hmeshBudget
  have hj := (Labels).carrier.indexWeight_nonneg j
  have hC := (CanonicalActualSourceMass.weightConstant_pos K cap annulus fixedPrimeCost
    firstFiber secondFiber rowFiber hfirstFiber hsecondFiber hrowFiber).le
  calc
    _ ≤ R.prepared.originalScalarAt L i.val *
        (profile ^ dFirst * (((costs).rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
          orbitalFieldFactor K) * Z ^ remaining * (Labels).carrier.indexWeight j) := hraw
    _ = (R.prepared.originalScalarAt L i.val *
        (profile ^ dFirst * (((costs).rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
          orbitalFieldFactor K))) * Z ^ remaining * (Labels).carrier.indexWeight j := by ring
    _ ≤ (CanonicalActualSourceMass.weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude (max dRow dPrime)) *
        Z ^ remaining * (Labels).carrier.indexWeight j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hj
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hremaining)
        (mul_nonneg hC (pow_nonneg (zero_le_one.trans hprofile) _))) hj

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
theorem canonical_amplified_outer_index_weight_prime_loss
    (dFirst dAmplitude dRow dPrime : ℕ)
    (profile annulus amplitude rowCost primeCost fixedPrimeCost firstFiber secondFiber rowFiber ε : ℝ)
    (hprofile : 1 ≤ profile) (hannulus : 1 ≤ annulus)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrowCost : rowCost ≤ profile ^ dRow)
    (hprimeCost : primeCost ≤ fixedPrimeCost * profile ^ dPrime)
    (hfirstFiber : 1 ≤ firstFiber) (hsecondFiber : 1 ≤ secondFiber) (hrowFiber : 1 ≤ rowFiber)
    (hfirstCap : (s.fiber : ℝ) ≤ firstFiber)
    (hsecondCap : (R.supported.gated.originalSecondFiberAt L i.val : ℝ) ≤ secondFiber)
    (hrowCap : ((costs).rowMass.originalFiber : ℝ) ≤ rowFiber)
    (step error mesh : ℝ) (G : OriginalNominalGeometry (K := K) a Z step)
    (htag : G.tag = R.supported.gated.originalNominalTagAt L i.val)
    (hstepPool : step = 3 * ell)
    (Mmax Bmax : ℝ)
    (hM : R.supported.gated.originalRowExponentAt L i.val ≤ Mmax)
    (hB : R.supported.gated.originalFrozenExponentAt L i.val ≤ Bmax)
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
    (hnormalization : R.supported.gated.firstAllowanceAt L total i.val =
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
    (hleftIdeal : (costs).rowMass.leftIdeal = (R.supported.gated.commonLabel L i.val).1)
    (hrightIdeal : (costs).rowMass.rightIdeal = (R.supported.gated.commonLabel L i.val).2)
    (hsecondDivisor : (LF).source.allocation.divisor = R.supported.gated.innerDivisor L i.val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pools i.val.1 i.val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total i.val.1 i.val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude (max dRow dPrime) * Z ^ (ε / 4)) *
        amplifiedIndexWeight P Mmax Bmax Main Errors
          ((Labels).rectangleAmplifiedIndex families P Tags tagMem b) := by
  let j := (Labels).rectangleIndex families b
  let key := R.supported.gated.arithmeticIndex L hcap exceptional firstNormalization i
  let B := OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost
  let remaining := G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh
  let fiberScalar := ((s.fiber : ℝ) * (R.supported.gated.originalSecondFiberAt L i.val : ℝ)) / 2
  let tagWeight := AmplifiedCommonIndex.originalTagWeight P
    (R.supported.gated.originalRowExponentAt L i.val)
    (R.supported.gated.originalFrozenExponentAt L i.val) Main Errors key
  have htag0 : 0 ≤ tagWeight := AmplifiedCommonIndex.originalTagWeight_nonneg P _ _ Main Errors
    P.exponent_pos (R.supported.gated.originalRowExponentAt_nonneg L i.val)
    (P.rowDensity_pos_of_uniform hM hB hdensity).le key
  have hscalarEq : R.supported.gated.originalScalarAt L i.val = fiberScalar * tagWeight :=
    R.supported.gated.originalScalarAt_eq_originalTagWeight L hcap exceptional firstNormalization i
  have hharmonic : AmplifiedCommonIndex.harmonicWeight P Main Errors key =
      (Labels).carrier.indexWeight j :=
    (Labels).amplified_harmonicWeight_eq_indexWeight Tags tagMem i
  have allowance := OriginalPairAllowanceWindow.ofNominalGeometry LF RF
    ((raw).left b.val.2.1).calibration ((raw).right b.val.2.2).calibration (costs).rowMass
    ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
    d a Z step G ((raw).left_base _) ((raw).right_base _)
    hsecond hopposite hunit hnonunit bindingL bindingR atomsL atomsR hstep annulus error mesh
    herror hthreshold hmesh hfit hannulusLL hannulusLR hannulusRL hannulusRR
    hsupport hrawL hrawR hwidthL hwidthR hdivisor hscaleL hscaleR hradius
  have pairWindow : OriginalPairAllowanceWindow LF RF
      ((raw).left b.val.2.1).calibration ((raw).right b.val.2.2).calibration (costs).rowMass
      ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
      (((raw).withArithmetic costs).left b.val.2.1).capacity
      (((raw).withArithmetic costs).right b.val.2.2).capacity
      Z (R.supported.gated.firstAllowanceAt L total i.val) remaining := by
    simpa only [hcapacityL, hcapacityR, hnormalization] using allowance
  have atomWindow := CanonicalCapacityKernelMass.OriginalAtomWindow.ofConstantOriginalAtoms
    LF RF (costs).rowMass ((costs).leftAtoms b.val.2.1) ((costs).rightAtoms b.val.2.2)
    ((raw).left b.val.2.1).bounds ((raw).right b.val.2.2).bounds
    cap annulus amplitude rowCost primeCost hleftCount hrightCount hcommonLeft hcommonRight
    hrow hcommonLA hcommonLP hcommonRA hcommonRP hfrozenLA hfrozenLP hfrozenRA hfrozenRP hprimeL hprimeR
  have hfirst := actual_common_pair_properties _ _ _ _ i.val.1
  have hdivisorIndex : (LF).source.allocation.divisor = j.2.2.2.1.val := by
    change (LF).source.allocation.divisor = ((Labels).allocation i).1
    rw [R.supported.gated.arithmeticLabels_secondDivisor]
    exact hsecondDivisor
  have hinnerIndex : j.2.2.2.1.val = R.supported.gated.innerDivisor L i.val :=
    R.supported.gated.arithmeticLabels_secondDivisor L hcap exceptional firstNormalization i
  have houter := R.supported.gated.extracted_parentLeaf_weight_original_relative L hZ total
    exceptional parentWidth i.val (extract i)
  rw [← hinnerIndex] at houter
  have hscalar0 : 0 ≤ R.supported.gated.originalScalarAt L i.val := by
    rw [hscalarEq]
    exact mul_nonneg (by positivity : 0 ≤ fiberScalar) htag0
  have hraw := ActualHybridFamily.arithmetic_outer_index_weight leaves N arithmetic b pairWindow
    hZ cap B (OriginalProfileAtomBounds.atomBudget_one _ _ _ _) atomWindow
    j hleftIdeal hrightIdeal hdivisorIndex parentWidth (total i.val.1 i.val.2.1)
    (s.pools i.val.1 i.val.2.1).weightBound (profile ^ dFirst)
    (pow_nonneg (zero_le_one.trans hprofile) _) hfirstProfile hfirst.1 hfirst.2.1 hfirst.2.2
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle)) i.val.2.2.2.1
    (fun _ : PUnit.{1} × PUnit.{1} => (1 : Circle))
    (R.supported.gated.secondPhaseAt L i.val) (R.supported.gated.originalScalarAt L i.val) hscalar0 houter
  have hscalar : fiberScalar ≤ firstFiber * secondFiber := by
    have hprod : 0 ≤ firstFiber * secondFiber :=
      mul_nonneg (zero_le_one.trans hfirstFiber) (zero_le_one.trans hsecondFiber)
    calc
      _ ≤ (firstFiber * secondFiber) / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hfirstCap hsecondCap (Nat.cast_nonneg _) (zero_le_one.trans hfirstFiber))
          (by norm_num)
      _ ≤ firstFiber * secondFiber := by linarith
  have hcoefficient := CanonicalPrimeActualSourceMass.atomCoefficient_le K cap dFirst dAmplitude dRow dPrime
    annulus amplitude rowCost primeCost fixedPrimeCost profile fiberScalar
    firstFiber secondFiber rowFiber (costs).rowMass.originalFiber (zero_le_one.trans hannulus)
    hprofile hamplitude hamp hrowCost hprimeCost hscalar hfirstFiber hsecondFiber hrowFiber hrowCap
  have hnominal : G.skeleton.wo + G.tag.poolLength step =
      AmplifiedCommonIndex.movingLength P Main Errors key := by
    simpa only [OriginalNominalGeometry.skeleton, htag, hstepPool] using
      R.supported.gated.originalNominalTagAt_movingLength L hcap exceptional firstNormalization i
  have hremaining : remaining ≤ ε / 4 + AmplifiedCommonIndex.movingLength P Main Errors key := by
    calc
      _ ≤ ε / 4 + (G.skeleton.wo + G.tag.poolLength step) :=
        OriginalPairAllowanceProduction.remaining_le_quarter _ _ error mesh ε herrorBudget hmeshBudget
      _ = _ := by rw [hnominal]
  have hj := (Labels).carrier.indexWeight_nonneg j
  have hC := (CanonicalActualSourceMass.weightConstant_pos K cap annulus fixedPrimeCost
    firstFiber secondFiber rowFiber hfirstFiber hsecondFiber hrowFiber).le
  have hupper : ActualHybridFamily.outerWeights leaves b.val *
      (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
        CanonicalActualSourceMass.weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber *
          profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude (max dRow dPrime) *
          tagWeight * Z ^ remaining * AmplifiedCommonIndex.harmonicWeight P Main Errors key := by
    rw [hharmonic]
    calc
      _ ≤ R.supported.gated.originalScalarAt L i.val *
          (profile ^ dFirst * (((costs).rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
            orbitalFieldFactor K) * Z ^ remaining * (Labels).carrier.indexWeight j) := hraw
      _ = (fiberScalar *
          (profile ^ dFirst * (((costs).rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
            orbitalFieldFactor K))) * tagWeight * Z ^ remaining * (Labels).carrier.indexWeight j := by
        rw [hscalarEq]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient htag0)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hj
  exact AmplifiedCommonIndex.pointwise_of_original_tag_uniform P Main Errors
    (R.supported.gated.originalRowExponentAt_nonneg L i.val) hM hB hdensity key _
    (CanonicalActualSourceMass.weightConstant K cap annulus fixedPrimeCost firstFiber secondFiber rowFiber)
    (profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude (max dRow dPrime))
    remaining (ε / 4) hC (pow_nonneg (zero_le_one.trans hprofile) _) hremaining hupper

end ActualFirstSource.SecondStages

end Amplified
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimeActualSourceMass.atomCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.ProfileWindows.monoProfile
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.canonical_direct_outer_index_weight_prime_loss
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.canonical_amplified_outer_index_weight_prime_loss
