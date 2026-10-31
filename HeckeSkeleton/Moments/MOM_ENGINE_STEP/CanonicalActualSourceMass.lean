import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSourceImageKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedOriginalFamilyWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalParentWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalPairAllowance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolMonotonicity

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
  have h₁ : 0 < firstFiber := zero_lt_one.trans_le hfirst
  have h₂ : 0 < secondFiber := zero_lt_one.trans_le hsecond
  have h₃ : 0 < rowFiber := zero_lt_one.trans_le hrow
  unfold weightConstant
  positivity

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
  let B := OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost
  let C := max 1 (max annulus primeCost)
  have hB : 0 ≤ B :=
    zero_le_one.trans (OriginalProfileAtomBounds.atomBudget_one _ _ _ _)
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hP : 0 ≤ profile := zero_le_one.trans hprofile
  have hR : 0 ≤ rowFiber := zero_le_one.trans hrow
  have hF : 0 ≤ firstFiber * secondFiber :=
    mul_nonneg (zero_le_one.trans hfirst) (zero_le_one.trans hsecond)
  have hOrbital := orbitalFieldFactor_nonneg K
  have hBbound : B ≤ C * profile ^ atomDegree dAmplitude dRow :=
    OriginalProfileAtomBounds.atomBudget_le_profile_power annulus amplitude rowCost primeCost
      profile dAmplitude dRow hannulus hprofile hamplitude hamp hrowCost
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
        (rowFiber * (C * profile ^ atomDegree dAmplitude dRow) ^ (3 * cap + 1) *
          max 1 (orbitalFieldFactor K))) := hcoeff
    _ = _ := by
      simp only [weightConstant, weightDegree, mul_pow, ← pow_mul, pow_add, C] <;> ring

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
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
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

variable (extract : ∀ i : Live,
  (R.prepared.parentLeaf L exceptional firstNormalization i.val).ConstantAtomExtraction)
local notation "leaves" => fun i : Live => (extract i).leaf
variable {I : Live → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable (N : ∀ i : Live, (extract i).leaf.NormalizationData (ι := I i)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (arithmetic : ∀ i, (N i).ArithmeticInput)
local notation "chosen" => fun i => (N i).withArithmetic (arithmetic i)
local notation "families" => fun i => (chosen i).family
local notation "Labels" => R.prepared.arithmeticLabels L hcap exceptional firstNormalization

variable (b : (ActualHybridFamily.normalizedFamily leaves chosen).active Finset.univ)
local notation "i" => b.val.1
local notation "raw" => N i
local notation "costs" => arithmetic i
local notation "LF" => raw.rectangles.leftFrame C b.val.2.1
local notation "RF" => raw.rectangles.rightFrame C b.val.2.2
local notation "LC" => LF.arithmeticCalibration (raw.left b.val.2.1).calibration
  costs.rowMass (costs.leftAtoms b.val.2.1)
local notation "RC" => RF.arithmeticCalibration (raw.right b.val.2.2).calibration
  costs.rowMass (costs.rightAtoms b.val.2.2)

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
    (hsecondCap : (R.prepared i.val.1 i.val.2.1).directScalarAt L L i.val.2.2 ≤ secondFiber)
    (hrowCap : (costs.rowMass.originalFiber : ℝ) ≤ rowFiber)
    (step error mesh : ℝ) (G : OriginalNominalGeometry (K := K) a Z step)
    (htag : G.tag = .direct)
    (hsecond : G.ideals.second.val = costs.rowMass.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = costs.rowMass.rightIdeal)
    (hunit : G.ideals.unitPart.val = costs.rowMass.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = costs.rowMass.nonunitIdeal.val)
    (bindingL : LC.OriginalLengthBinding d a step (G.atBase LF.source.base (raw.left_base _)))
    (bindingR : RC.OriginalLengthBinding d a step
      (G.swapSecond.atBase RF.source.base (raw.right_base _)))
    (atomsL : LC.OriginalCapacityAtoms) (atomsR : RC.OriginalCapacityAtoms)
    (hstep : 0 < step) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hmesh : 0 ≤ mesh) (hfit : d.geometry.fitsMesh mesh)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hcapacityL : ((raw.withArithmetic costs).left b.val.2.1).capacity =
      bindingL.capacityInput hstep mesh hmesh hfit atomsL)
    (hcapacityR : ((raw.withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput hstep mesh hmesh hfit atomsR)
    (hdivisor : LF.source.allocation.divisor = RF.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ LF.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ RF.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      costs.rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) costs.rowMass.mask)).val)
    (hnormalization : R.prepared.firstAllowanceAt L total i.val =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (herrorBudget : error ≤ 3 * ε / 40) (hmeshBudget : mesh ≤ ε / 8)
    (hleftCount : (extract i).leaf.leftSlots ≤ cap)
    (hrightCount : (extract i).leaf.rightSlots ≤ cap)
    (hcommonLeft : costs.commonLeftSlots ≤ cap) (hcommonRight : costs.commonRightSlots ≤ cap)
    (hrow : costs.rowMass.profileBound = rowCost)
    (hcommonLA : ∀ j, costs.rowMass.leftAtoms.annulus j = annulus)
    (hcommonLP : ∀ j, costs.rowMass.leftAtoms.profile j = amplitude ^ 2)
    (hcommonRA : ∀ j, costs.rowMass.rightAtoms.annulus j = annulus)
    (hcommonRP : ∀ j, costs.rowMass.rightAtoms.profile j = amplitude ^ 2)
    (hfrozenLA : ∀ j, (costs.leftAtoms b.val.2.1).annulus j = annulus)
    (hfrozenLP : ∀ j, (costs.leftAtoms b.val.2.1).profile j = amplitude ^ 2)
    (hfrozenRA : ∀ j, (costs.rightAtoms b.val.2.2).annulus j = annulus)
    (hfrozenRP : ∀ j, (costs.rightAtoms b.val.2.2).profile j = amplitude ^ 2)
    (hprimeL : ∀ j, (raw.left b.val.2.1).bounds j = primeCost)
    (hprimeR : ∀ j, (raw.right b.val.2.2).bounds j = primeCost)
    (hleftIdeal : costs.rowMass.leftIdeal = (R.prepared.commonLabel L i.val).1)
    (hrightIdeal : costs.rowMass.rightIdeal = (R.prepared.commonLabel L i.val).2)
    (hsecondDivisor : LF.source.allocation.divisor = R.prepared.innerDivisor L i.val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pieces i.val.1 i.val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total i.val.1 i.val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow * Z ^ (ε / 4)) *
        Labels.carrier.indexWeight (Labels.rectangleIndex families b) := by
  let j := Labels.rectangleIndex families b
  let B := OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost
  let remaining := G.skeleton.wo + G.tag.poolLength step + 5 * error / 3 + mesh
  have allowance := OriginalPairAllowanceWindow.ofNominalGeometry LF RF
    (raw.left b.val.2.1).calibration (raw.right b.val.2.2).calibration costs.rowMass
    (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
    d a Z step G (raw.left_base _) (raw.right_base _)
    hsecond hopposite hunit hnonunit bindingL bindingR atomsL atomsR hstep annulus error mesh
    herror hthreshold hmesh hfit hannulusLL hannulusLR hannulusRL hannulusRR
    hsupport hrawL hrawR hwidthL hwidthR hdivisor hscaleL hscaleR hradius
  have pairWindow : OriginalPairAllowanceWindow LF RF
      (raw.left b.val.2.1).calibration (raw.right b.val.2.2).calibration costs.rowMass
      (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
      ((raw.withArithmetic costs).left b.val.2.1).capacity
      ((raw.withArithmetic costs).right b.val.2.2).capacity
      Z (R.prepared.firstAllowanceAt L total i.val) remaining := by
    simpa only [hcapacityL, hcapacityR, hnormalization] using allowance
  have atomWindow := CanonicalCapacityKernelMass.OriginalAtomWindow.ofConstantOriginalAtoms
    LF RF costs.rowMass (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
    (raw.left b.val.2.1).bounds (raw.right b.val.2.2).bounds
    cap annulus amplitude rowCost primeCost hleftCount hrightCount hcommonLeft hcommonRight
    hrow hcommonLA hcommonLP hcommonRA hcommonRP hfrozenLA hfrozenLP hfrozenRA hfrozenRP hprimeL hprimeR
  have hfirst := actual_common_pair_properties _ _ _ _ i.val.1
  have hdivisorIndex : LF.source.allocation.divisor = j.2.2.2.1.val := by
    change LF.source.allocation.divisor = (Labels.allocation i).1
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
  have hcoefficient := CanonicalActualSourceMass.atomCoefficient_le K cap dFirst dAmplitude dRow
    annulus amplitude rowCost primeCost profile (R.prepared.originalScalarAt L i.val)
    firstFiber secondFiber rowFiber costs.rowMass.originalFiber (zero_le_one.trans hannulus)
    hprofile hamplitude hamp hrowCost hscalar hfirstFiber hsecondFiber hrowFiber hrowCap
  have hremaining : remaining ≤ ε / 4 := by
    simpa only [remaining, OriginalNominalGeometry.skeleton, htag,
      OriginalNominalTag.movingLength, OriginalNominalTag.poolLength, zero_add, add_zero] using
      OriginalPairAllowanceProduction.remaining_le_quarter 0 0 error mesh ε herrorBudget hmeshBudget
  have hj := Labels.carrier.indexWeight_nonneg j
  have hC := (CanonicalActualSourceMass.weightConstant_pos K cap annulus primeCost
    firstFiber secondFiber rowFiber hfirstFiber hsecondFiber hrowFiber).le
  calc
    _ ≤ R.prepared.originalScalarAt L i.val *
        (profile ^ dFirst * ((costs.rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
          orbitalFieldFactor K) * Z ^ remaining * Labels.carrier.indexWeight j) := hraw
    _ = (R.prepared.originalScalarAt L i.val *
        (profile ^ dFirst * ((costs.rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
          orbitalFieldFactor K))) * Z ^ remaining * Labels.carrier.indexWeight j := by ring
    _ ≤ (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow) *
        Z ^ remaining * Labels.carrier.indexWeight j :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hj
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hremaining)
        (mul_nonneg hC (pow_nonneg (zero_le_one.trans hprofile) _))) hj

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
  unfold amplifiedIndex
  split <;> rfl

theorem amplified_originalTagWeight_eq (M B : ℝ) (j : J) :
    AmplifiedCommonIndex.originalTagWeight P M B (labels.mainCarrier tag) (labels.errorCarrier tag)
      (labels.amplifiedIndex tag P tag_mem j) =
      (4 / P.rowDensity M B) *
        (match tag j with
        | none => (M + 6 * ell) / (ell / 2)
        | some q => FirstGaussPoolData.localErrorWeight q.2 q.1) := by
  cases ht : tag j with
  | none => simp only [amplifiedIndex, ht, AmplifiedCommonIndex.originalTagWeight]
  | some q => simp only [amplifiedIndex, ht, AmplifiedCommonIndex.originalTagWeight]

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
  unfold originalRowExponentAt
  split
  · exact ((s.pools j.1 j.2.1).divisorPools.leftData j.2.2.1).rowExponent_nonneg
  · exact ((s.pools j.1 j.2.1).divisorPools.rightData j.2.2.1).rowExponent_nonneg

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
  rw [arithmeticIndex, OriginalArithmeticLabels.amplified_originalTagWeight_eq]
  rcases i with ⟨⟨v, D, S, χ, j | j⟩, hi⟩
  all_goals
    rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩)) <;>
      simp only [originalScalarAt, FirstBlockPoolData.SecondStages.poolScalarAt,
        originalSecondFiberAt, originalRowExponentAt, originalFrozenExponentAt,
        arithmeticTag, FirstBlockPoolData.SecondStages.amplifierTag,
        ActualPoolStages.amplifierTag, ActualPoolStages.leafTag,
        FirstGaussPoolData.tagWeight, FirstGaussPoolData.density,
        FirstGaussPoolData.multiplicity] <;> ring

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
  rcases i with ⟨⟨v, D, S, χ, j | j⟩, hi⟩
  all_goals
    rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩)) <;>
      simp only [originalNominalTagAt, PoolSourceTag.nominalTag, ActualPoolStages.leafTag,
        arithmeticIndex, OriginalArithmeticLabels.amplifiedIndex,
        arithmeticTag, FirstBlockPoolData.SecondStages.amplifierTag, ActualPoolStages.amplifierTag,
        AmplifiedCommonIndex.movingLength, OriginalNominalTag.movingLength,
        OriginalNominalTag.poolLength, AmplifierValuation.movingMultiplicity,
        amplifierMovingExponent] <;> ring

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

variable (extract : ∀ i : Live,
  (R.supported.gated.parentLeaf L exceptional firstNormalization i.val).ConstantAtomExtraction)
local notation "leaves" => fun i : Live => (extract i).leaf
variable {I : Live → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable (N : ∀ i : Live, (extract i).leaf.NormalizationData (ι := I i)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (arithmetic : ∀ i, (N i).ArithmeticInput)
local notation "chosen" => fun i => (N i).withArithmetic (arithmetic i)
local notation "families" => fun i => (chosen i).family
local notation "Labels" => R.supported.gated.arithmeticLabels L hcap exceptional firstNormalization
local notation "Tags" => R.supported.gated.arithmeticTag L exceptional firstNormalization
local notation "tagMem" => R.supported.gated.arithmeticTag_mem L exceptional firstNormalization
local notation "Main" => Labels.mainCarrier Tags
local notation "Errors" => Labels.errorCarrier Tags

variable (b : (ActualHybridFamily.normalizedFamily leaves chosen).active Finset.univ)
local notation "i" => b.val.1
local notation "raw" => N i
local notation "costs" => arithmetic i
local notation "LF" => raw.rectangles.leftFrame C b.val.2.1
local notation "RF" => raw.rectangles.rightFrame C b.val.2.2
local notation "LC" => LF.arithmeticCalibration (raw.left b.val.2.1).calibration
  costs.rowMass (costs.leftAtoms b.val.2.1)
local notation "RC" => RF.arithmeticCalibration (raw.right b.val.2.2).calibration
  costs.rowMass (costs.rightAtoms b.val.2.2)

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
    (hsecondCap : (R.supported.gated.originalSecondFiberAt L i.val : ℝ) ≤ secondFiber)
    (hrowCap : (costs.rowMass.originalFiber : ℝ) ≤ rowFiber)
    (step error mesh : ℝ) (G : OriginalNominalGeometry (K := K) a Z step)
    (htag : G.tag = R.supported.gated.originalNominalTagAt L i.val)
    (hstepPool : step = 3 * ell)
    (Mmax Bmax : ℝ)
    (hM : R.supported.gated.originalRowExponentAt L i.val ≤ Mmax)
    (hB : R.supported.gated.originalFrozenExponentAt L i.val ≤ Bmax)
    (hdensity : 0 < P.rowDensity Mmax Bmax)
    (hsecond : G.ideals.second.val = costs.rowMass.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = costs.rowMass.rightIdeal)
    (hunit : G.ideals.unitPart.val = costs.rowMass.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = costs.rowMass.nonunitIdeal.val)
    (bindingL : LC.OriginalLengthBinding d a step (G.atBase LF.source.base (raw.left_base _)))
    (bindingR : RC.OriginalLengthBinding d a step
      (G.swapSecond.atBase RF.source.base (raw.right_base _)))
    (atomsL : LC.OriginalCapacityAtoms) (atomsR : RC.OriginalCapacityAtoms)
    (hstep : 0 < step) (herror : 0 < error)
    (hthreshold : OriginalPairAllowanceProduction.annulusThreshold annulus error ≤ Z)
    (hmesh : 0 ≤ mesh) (hfit : d.geometry.fitsMesh mesh)
    (hannulusLL : atomsL.leftAnnulus ≤ annulus) (hannulusLR : atomsL.rightAnnulus ≤ annulus)
    (hannulusRL : atomsR.leftAnnulus ≤ annulus) (hannulusRR : atomsR.rightAnnulus ≤ annulus)
    (hsupport : G.supportError ≤ error)
    (hrawL : bindingL.rawScaleError ≤ error) (hrawR : bindingR.rawScaleError ≤ error)
    (hwidthL : bindingL.scales.error ≤ error) (hwidthR : bindingR.scales.error ≤ error)
    (hcapacityL : ((raw.withArithmetic costs).left b.val.2.1).capacity =
      bindingL.capacityInput hstep mesh hmesh hfit atomsL)
    (hcapacityR : ((raw.withArithmetic costs).right b.val.2.2).capacity =
      bindingR.capacityInput hstep mesh hmesh hfit atomsR)
    (hdivisor : LF.source.allocation.divisor = RF.source.allocation.divisor)
    (hscaleL : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ LF.normalizationScale)
    (hscaleR : Z ^ (G.skeleton.A - G.skeleton.c - G.skeleton.w) ≤ RF.normalizationScale)
    (hradius : Z ^ (-G.skeleton.Krow - G.skeleton.g) ≤
      costs.rowMass.radius.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) costs.rowMass.mask)).val)
    (hnormalization : R.supported.gated.firstAllowanceAt L total i.val =
      firstLeftAllowance Z (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
        G.ideals.first.val G.ideals.opposite.val)
    (herrorBudget : error ≤ 3 * ε / 40) (hmeshBudget : mesh ≤ ε / 8)
    (hleftCount : (extract i).leaf.leftSlots ≤ cap)
    (hrightCount : (extract i).leaf.rightSlots ≤ cap)
    (hcommonLeft : costs.commonLeftSlots ≤ cap) (hcommonRight : costs.commonRightSlots ≤ cap)
    (hrow : costs.rowMass.profileBound = rowCost)
    (hcommonLA : ∀ j, costs.rowMass.leftAtoms.annulus j = annulus)
    (hcommonLP : ∀ j, costs.rowMass.leftAtoms.profile j = amplitude ^ 2)
    (hcommonRA : ∀ j, costs.rowMass.rightAtoms.annulus j = annulus)
    (hcommonRP : ∀ j, costs.rowMass.rightAtoms.profile j = amplitude ^ 2)
    (hfrozenLA : ∀ j, (costs.leftAtoms b.val.2.1).annulus j = annulus)
    (hfrozenLP : ∀ j, (costs.leftAtoms b.val.2.1).profile j = amplitude ^ 2)
    (hfrozenRA : ∀ j, (costs.rightAtoms b.val.2.2).annulus j = annulus)
    (hfrozenRP : ∀ j, (costs.rightAtoms b.val.2.2).profile j = amplitude ^ 2)
    (hprimeL : ∀ j, (raw.left b.val.2.1).bounds j = primeCost)
    (hprimeR : ∀ j, (raw.right b.val.2.2).bounds j = primeCost)
    (hleftIdeal : costs.rowMass.leftIdeal = (R.supported.gated.commonLabel L i.val).1)
    (hrightIdeal : costs.rowMass.rightIdeal = (R.supported.gated.commonLabel L i.val).2)
    (hsecondDivisor : LF.source.allocation.divisor = R.supported.gated.innerDivisor L i.val)
    (parentWidth : ℝ)
    (hfirstProfile : (s.pools i.val.1 i.val.2.1).weightBound ≤
      profile ^ dFirst * Z ^ (parentWidth - total i.val.1 i.val.2.1)) :
    ActualHybridFamily.outerWeights leaves b.val *
        (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
      (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
        profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow * Z ^ (ε / 4)) *
        amplifiedIndexWeight P Mmax Bmax Main Errors
          (Labels.rectangleAmplifiedIndex families P Tags tagMem b) := by
  let j := Labels.rectangleIndex families b
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
      Labels.carrier.indexWeight j :=
    Labels.amplified_harmonicWeight_eq_indexWeight Tags tagMem i
  have allowance := OriginalPairAllowanceWindow.ofNominalGeometry LF RF
    (raw.left b.val.2.1).calibration (raw.right b.val.2.2).calibration costs.rowMass
    (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
    d a Z step G (raw.left_base _) (raw.right_base _)
    hsecond hopposite hunit hnonunit bindingL bindingR atomsL atomsR hstep annulus error mesh
    herror hthreshold hmesh hfit hannulusLL hannulusLR hannulusRL hannulusRR
    hsupport hrawL hrawR hwidthL hwidthR hdivisor hscaleL hscaleR hradius
  have pairWindow : OriginalPairAllowanceWindow LF RF
      (raw.left b.val.2.1).calibration (raw.right b.val.2.2).calibration costs.rowMass
      (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
      ((raw.withArithmetic costs).left b.val.2.1).capacity
      ((raw.withArithmetic costs).right b.val.2.2).capacity
      Z (R.supported.gated.firstAllowanceAt L total i.val) remaining := by
    simpa only [hcapacityL, hcapacityR, hnormalization] using allowance
  have atomWindow := CanonicalCapacityKernelMass.OriginalAtomWindow.ofConstantOriginalAtoms
    LF RF costs.rowMass (costs.leftAtoms b.val.2.1) (costs.rightAtoms b.val.2.2)
    (raw.left b.val.2.1).bounds (raw.right b.val.2.2).bounds
    cap annulus amplitude rowCost primeCost hleftCount hrightCount hcommonLeft hcommonRight
    hrow hcommonLA hcommonLP hcommonRA hcommonRP hfrozenLA hfrozenLP hfrozenRA hfrozenRP hprimeL hprimeR
  have hfirst := actual_common_pair_properties _ _ _ _ i.val.1
  have hdivisorIndex : LF.source.allocation.divisor = j.2.2.2.1.val := by
    change LF.source.allocation.divisor = (Labels.allocation i).1
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
  have hcoefficient := CanonicalActualSourceMass.atomCoefficient_le K cap dFirst dAmplitude dRow
    annulus amplitude rowCost primeCost profile fiberScalar
    firstFiber secondFiber rowFiber costs.rowMass.originalFiber (zero_le_one.trans hannulus)
    hprofile hamplitude hamp hrowCost hscalar hfirstFiber hsecondFiber hrowFiber hrowCap
  have hnominal : G.skeleton.wo + G.tag.poolLength step =
      AmplifiedCommonIndex.movingLength P Main Errors key := by
    simpa only [OriginalNominalGeometry.skeleton, htag, hstepPool] using
      R.supported.gated.originalNominalTagAt_movingLength L hcap exceptional firstNormalization i
  have hremaining : remaining ≤ ε / 4 + AmplifiedCommonIndex.movingLength P Main Errors key := by
    calc
      _ ≤ ε / 4 + (G.skeleton.wo + G.tag.poolLength step) :=
        OriginalPairAllowanceProduction.remaining_le_quarter _ _ error mesh ε herrorBudget hmeshBudget
      _ = _ := by rw [hnominal]
  have hj := Labels.carrier.indexWeight_nonneg j
  have hC := (CanonicalActualSourceMass.weightConstant_pos K cap annulus primeCost
    firstFiber secondFiber rowFiber hfirstFiber hsecondFiber hrowFiber).le
  have hupper : ActualHybridFamily.outerWeights leaves b.val *
      (ActualHybridFamily.normalizedFamily leaves chosen).weight Finset.univ parentWidth b ≤
        CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber *
          profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow *
          tagWeight * Z ^ remaining * AmplifiedCommonIndex.harmonicWeight P Main Errors key := by
    rw [hharmonic]
    calc
      _ ≤ R.supported.gated.originalScalarAt L i.val *
          (profile ^ dFirst * ((costs.rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
            orbitalFieldFactor K) * Z ^ remaining * Labels.carrier.indexWeight j) := hraw
      _ = (fiberScalar *
          (profile ^ dFirst * ((costs.rowMass.originalFiber : ℝ) * B ^ (3 * cap + 1) *
            orbitalFieldFactor K))) * tagWeight * Z ^ remaining * Labels.carrier.indexWeight j := by
        rw [hscalarEq]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient htag0)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hj
  exact AmplifiedCommonIndex.pointwise_of_original_tag_uniform P Main Errors
    (R.supported.gated.originalRowExponentAt_nonneg L i.val) hM hB hdensity key _
    (CanonicalActualSourceMass.weightConstant K cap annulus primeCost firstFiber secondFiber rowFiber)
    (profile ^ CanonicalActualSourceMass.weightDegree cap dFirst dAmplitude dRow)
    remaining (ε / 4) hC (pow_nonneg (zero_le_one.trans hprofile) _) hremaining hupper

end ActualFirstSource.SecondStages

end Amplified
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualSourceMass.atomCoefficient_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.canonical_direct_outer_index_weight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalScalarAt_eq_originalTagWeight
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalNominalTagAt_movingLength

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.canonical_amplified_outer_index_weight
