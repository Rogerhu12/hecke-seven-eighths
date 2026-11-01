import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectTerminalWindows

/-!
# Complete direct terminal budgets from the original profiles

The constants in the original divisor and tuple summation are selected
before the moving source, scale and profile values. Both public bounds
construct their original first windows and their actual second amplitude
windows internally. The original first normalization and the same direct
terminal family are retained throughout the finite sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
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

namespace CanonicalPrimitiveDirectTerminalBudget

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (cap : ℕ) (columnBound εsum : ℝ)
variable (hcolumnBound : 0 ≤ columnBound) (hεsum : 0 < εsum)

local notation "zeroExists" => actual_direct_second_dual_zero_from_combined_windows
  (E := ℝ) (W := ℝ) (C := C)
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum
local notation "tailExists" => actual_direct_second_dual_tail_from_combined_windows
  (E := ℝ) (W := ℝ) (C := C)
  (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
  (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum

/-- Fixed before every source and scale. -/
def zeroSumConstant : ℝ := Classical.choose zeroExists

/-- The same ordering of quantifiers for the complete tail sum. -/
def tailSumConstant : ℝ := Classical.choose tailExists

theorem zeroSumConstant_pos :
    0 < zeroSumConstant μv C hDiff cap columnBound εsum hcolumnBound hεsum :=
  (Classical.choose_spec zeroExists).1

theorem tailSumConstant_pos :
    0 < tailSumConstant μv C hDiff cap columnBound εsum hcolumnBound hεsum :=
  (Classical.choose_spec tailExists).1

end CanonicalPrimitiveDirectTerminalBudget

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => atoms.raw Y₁ Y₂


local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

variable (cap : ℕ) (annulus loss cutoffExponent : ℝ)
variable (hannulus : 1 ≤ annulus) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (orders : Finset (ℕ × ℕ)) (amplitude : ℝ)
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (step : ℝ) (hstep : 0 < step)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)

variable (lo : ℝ) (hlo : 0 < lo) (hloOne : lo ≤ 1)
variable (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
variable (hlowerWindow : window ⊆ Set.Ici lo) (hamplitude : 1 ≤ amplitude)
variable (leftExponent rightExponent lengthBound columnBound : ℝ)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
variable (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
variable (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ columnBound)
variable (hlossOne : loss ≤ 1)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (sTail sZero : Finset (ℕ × ℕ)) (Nsave decay : ℝ) (hdecay : 1 < decay)

local notation "degree" => CanonicalOriginalTerminalPowers.primitiveDegree
  cap lengthBound columnBound step loss cutoffExponent
local notation "cutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z
local notation "hcutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z hZ.le hdecay
local notation "leftGeometry" => Q.literalPrimitiveLeftDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent
local notation "rightGeometry" => Q.literalPrimitiveRightDirectGeometry μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  loss cutoffExponent step hloss hcutoffExponent
local notation "stages" => Q.literalPrimitiveDirectStages μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss cutoffExponent hannulus hcap hannulusZ domain profiles hrows ht hwindow
  hcutoffPower step hstep hloss hcutoffExponent hDiff δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂

local notation "terminal" => Q.literalPrimitiveDirectDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstShift" => fun DE D =>
  Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
    hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D (firstTotal DE D)
local notation "zeroConstant" =>
  CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) cap amplitude sZero
local notation "tailConstant" =>
  CanonicalPrimitiveDirectTerminalWindows.profileConstant (A := A) cap amplitude sTail

local notation "firstKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv ν δ₁ hδ₁ hδ₁half
local notation "kernelBound" => (firstTerminalFourierControl (W := ℝ)).seminorms.sup
  (schwartzSeminormFamily ℝ ℝ ℂ) firstKernel

variable (hcolumnBound : 0 ≤ columnBound) (εsum : ℝ) (hεsum : 0 < εsum)

local notation "originalWindows" => Q.literalPrimitiveFirstTerminalWindows μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ hcolumnBound
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
local notation "zeroSumConstant" => CanonicalPrimitiveDirectTerminalBudget.zeroSumConstant
  μv C hDiff cap columnBound εsum hcolumnBound hεsum
local notation "tailSumConstant" => CanonicalPrimitiveDirectTerminalBudget.tailSumConstant
  μv C hDiff cap columnBound εsum hcolumnBound hεsum

local notation "zeroWindows" => Q.literalPrimitiveDirectZeroAmplitudeWindows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

local notation "tailWindows" => Q.literalPrimitiveDirectTailAmplitudeWindows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay)

/-- The complete zero budget, on the original first arithmetic carrier.
The sharp central degree cancels before the label sum. -/
theorem literalPrimitiveDirectDualZeroBudget_le
    (εzero Czero : ℝ) (hεzero : 0 ≤ εzero) (hCzero : 0 ≤ Czero) :
    stages.dualSecondZeroBudget terminal
      (Q.literalPrimitiveFirstNormalization μv ν C hroot hemb W ξ
        a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half)
      εzero Czero / Z ^ (a.m + a.q) ≤
    Czero * orbitalFieldFactor K * kernelBound * zeroConstant * zeroSumConstant *
      Z ^ (CanonicalPrimitiveDirectTerminalWindows.zeroLoss
        padding step loss cutoffExponent lengthBound columnBound δ₁ εzero + εsum) := by
  have hsum := (Classical.choose_spec
    (actual_direct_second_dual_zero_from_combined_windows
      (E := ℝ) (W := ℝ) (C := C)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
      (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum)).2
  have h := hsum Z hZ centered (data ξ) internal t Y₁ Y₂ cutoff hcutoff
    source stages sTail sZero degree Nsave decay terminal εzero Czero (a.m + a.q)
    (CanonicalPrimitiveDirectTerminalWindows.zeroLoss
      padding step loss cutoffExponent lengthBound columnBound δ₁ εzero)
    (orbitalFieldFactor K) kernelBound zeroConstant 1 hCzero
    (orbitalFieldFactor_nonneg K) (apply_nonneg _ _)
    (CanonicalPrimitiveDirectTerminalWindows.profileConstant_nonneg (A := A) cap amplitude sZero)
    firstTotal firstShift originalWindows (zeroWindows εzero hεzero)
  have hmask : originalWindows.oldMask = (1 : Ideal (𝓞 K)) := rfl
  simpa only [Q.literalPrimitiveFirstSource_fiber, hmask, map_one, Nat.cast_one,
    one_mul, mul_one, div_one] using h

/-- The coarse complete-column tail is paid by the fixed saving;
the original internal divisor density is summed only once. -/
theorem literalPrimitiveDirectDualTailBudget_le
    (Cerror : ℝ) (hCerror : 0 ≤ Cerror) (hsaving : 2 * columnBound ≤ Nsave) :
    stages.dualSecondTailBudget terminal
      (Q.literalPrimitiveFirstNormalization μv ν C hroot hemb W ξ
        a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half)
      Cerror / Z ^ (a.m + a.q) ≤
    Cerror * orbitalFieldFactor K * kernelBound * tailConstant * tailSumConstant *
      Z ^ (loss + εsum) := by
  have hsum := (Classical.choose_spec
    (actual_direct_second_dual_tail_from_combined_windows
      (E := ℝ) (W := ℝ) (C := C)
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (finiteTest := rowBallFiniteFamily K A.Sf 1)
      (2 * (cap + 2)) columnBound εsum hcolumnBound hεsum)).2
  have h := hsum Z hZ centered (data ξ) internal t Y₁ Y₂ cutoff hcutoff
    source stages sTail sZero degree Nsave decay terminal Cerror (a.m + a.q)
    loss (orbitalFieldFactor K) kernelBound tailConstant 1 hCerror
    (orbitalFieldFactor_nonneg K) (apply_nonneg _ _)
    (CanonicalPrimitiveDirectTerminalWindows.profileConstant_nonneg (A := A) cap amplitude sTail)
    firstTotal firstShift originalWindows (tailWindows hsaving)
  have hmask : originalWindows.oldMask = (1 : Ideal (𝓞 K)) := rfl
  simpa only [Q.literalPrimitiveFirstSource_fiber, hmask, map_one, Nat.cast_one,
    one_mul, mul_one, div_one] using h

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveDirectTerminalBudget.zeroSumConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveDirectTerminalBudget.tailSumConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectDualZeroBudget_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectDualTailBudget_le
