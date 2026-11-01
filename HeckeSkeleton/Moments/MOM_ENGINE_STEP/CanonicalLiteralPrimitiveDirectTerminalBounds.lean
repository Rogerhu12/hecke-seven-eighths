import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitiveDirectTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStageFibres

/-!
# Closed bounds on the actual direct terminal family

The calibration is the already constructed whole family. Its tuple
multiplicity and zero-product exponent are exact projections. A nonzero
physical fibre supplies the row used by the sharp amplitude theorem;
coefficient activity is still handled inside the same calibration.
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

/-- Exact counting data and sharp original amplitudes for the left source. -/
theorem literalPrimitiveDirectDualCalibration_left_bounds
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pieces DE D).rightData.columns
      (fun j => ((source.pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((terminal DE D).left S χ).windows.multiplicity =
        idealDivisorCount (DE.val.1 ^ 2) ^ (2 * (cap + 2)) ∧
      ((terminal DE D).left S χ).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.1) ∧
      (((stages DE D).left S χ).fiber ≠ 0 →
        ((terminal DE D).left S χ).tailAmplitude ≤
            ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
              sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                (CanonicalRowBall.archTest K A.Sf 1) ∧
          ((terminal DE D).left S χ).zeroAmplitude ≤
            (((2 * amplitude ^ (cap + 2)) ^ 2 *
              sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
              Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
                2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.1) * δ₁ +
                ((leftGeometry DE D).retainedLength + (leftGeometry DE D).enlargement) + 2 * loss)) := by
  have hN := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : internal.n₁ + internal.n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound hN DE D
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal hN DE D false (leftGeometry DE D) rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal hN DE D true (rightGeometry DE D) rfl
  have hmetadata := canonicalLeftOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := source.block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := source.radius)
    (firstMask := D.val) (δ := δ₁) (hδ := hδ₁)
    (hδhalf := hδ₁half) (cap := cap) (hcap := hcap)
    (orders := orders) (B := amplitude) (lo := lo)
    (hi := annulus) (loss := loss) (leftExponent := leftExponent)
    (rightExponent := rightExponent) (hB := hamplitude) (hlo := hlo)
    (hloOne := hloOne) (hhi := hannulus) (hlowerThreshold := hlowerThreshold)
    (hupperThreshold := hannulusZ) (domain := domainInternal) (hY₁ := hY₁)
    (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower)
    (hY₁le := hY₁le) (hY₂le := hY₂le) (profiles := profiles)
    (hrows := hrowsInternal) (ht := ht) (hlowerWindow := hlowerWindow)
    (hupperWindow := hwindow) (sTail := sTail) (sZero := sZero)
    (totalBound := lengthBound) (coarseBound := columnBound) (frozenBound := columnBound + 7 * (step / 3))
    (radiusBound := 4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step) (Nsave := Nsave) (decay := decay)
    (htotal := htotalInternal) (hcoarseNonneg := hcoarseNonneg) (hcoarse := hcolumn)
    (hloss := hlossOne) (p := source.pieces DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := (leftGeometry DE D).retainedLength + (leftGeometry DE D).enlargement) (hinverse := hleftRadius)
    (s := (stages DE D).left S χ) (hfrozen := hlengths.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := ((leftGeometry DE D).canonical_inverse_radius hZ).le) (hcutoff := rfl)
  refine ⟨hmetadata.1, hmetadata.2, ?_⟩
  intro hphysicalFiber
  have hphysical : ((source.pieces DE D).leftData.directSource
      ((source.pieces DE D).leftDivisorCoefficient S χ)).rows.Nonempty :=
    engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
  exact canonicalLeftOriginalDualCalibration_amplitude_bounds
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := source.block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := source.radius)
    (firstMask := D.val) (δ := δ₁) (hδ := hδ₁)
    (hδhalf := hδ₁half) (cap := cap) (hcap := hcap)
    (orders := orders) (B := amplitude) (lo := lo)
    (hi := annulus) (loss := loss) (leftExponent := leftExponent)
    (rightExponent := rightExponent) (hB := hamplitude) (hlo := hlo)
    (hloOne := hloOne) (hhi := hannulus) (hlowerThreshold := hlowerThreshold)
    (hupperThreshold := hannulusZ) (domain := domainInternal) (hY₁ := hY₁)
    (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower)
    (hY₁le := hY₁le) (hY₂le := hY₂le) (profiles := profiles)
    (hrows := hrowsInternal) (ht := ht) (hlowerWindow := hlowerWindow)
    (hupperWindow := hwindow) (sTail := sTail) (sZero := sZero)
    (totalBound := lengthBound) (coarseBound := columnBound) (frozenBound := columnBound + 7 * (step / 3))
    (radiusBound := 4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step) (Nsave := Nsave) (decay := decay)
    (htotal := htotalInternal) (hcoarseNonneg := hcoarseNonneg) (hcoarse := hcolumn)
    (hloss := hlossOne) (p := source.pieces DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := (leftGeometry DE D).retainedLength + (leftGeometry DE D).enlargement) (hinverse := hleftRadius)
    (s := (stages DE D).left S χ) (hfrozen := hlengths.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := ((leftGeometry DE D).canonical_inverse_radius hZ).le) (hcutoff := rfl) (hphysical := hphysical)

/-- Exact counting data and sharp original amplitudes for the right source. -/
theorem literalPrimitiveDirectDualCalibration_right_bounds
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset)
    (S : divisorPool (source.pieces DE D).rightData.columns
      (fun j => ((source.pieces DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    ((terminal DE D).right S χ).windows.multiplicity =
        idealDivisorCount (DE.val.2 ^ 2) ^ (2 * (cap + 2)) ∧
      ((terminal DE D).right S χ).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.2) ∧
      (((stages DE D).right S χ).fiber ≠ 0 →
        ((terminal DE D).right S χ).tailAmplitude ≤
            ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
              sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                (CanonicalRowBall.archTest K A.Sf 1) ∧
          ((terminal DE D).right S χ).zeroAmplitude ≤
            (((2 * amplitude ^ (cap + 2)) ^ 2 *
              sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
                (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
              Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
                2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.2) * δ₁ +
                ((rightGeometry DE D).retainedLength + (rightGeometry DE D).enlargement) + 2 * loss)) := by
  have hN := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : internal.n₁ + internal.n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound hN DE D
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal hN DE D false (leftGeometry DE D) rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal hN DE D true (rightGeometry DE D) rfl
  have hmetadata := canonicalRightOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := source.block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := source.radius)
    (firstMask := D.val) (δ := δ₁) (hδ := hδ₁)
    (hδhalf := hδ₁half) (cap := cap) (hcap := hcap)
    (orders := orders) (B := amplitude) (lo := lo)
    (hi := annulus) (loss := loss) (leftExponent := leftExponent)
    (rightExponent := rightExponent) (hB := hamplitude) (hlo := hlo)
    (hloOne := hloOne) (hhi := hannulus) (hlowerThreshold := hlowerThreshold)
    (hupperThreshold := hannulusZ) (domain := domainInternal) (hY₁ := hY₁)
    (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower)
    (hY₁le := hY₁le) (hY₂le := hY₂le) (profiles := profiles)
    (hrows := hrowsInternal) (ht := ht) (hlowerWindow := hlowerWindow)
    (hupperWindow := hwindow) (sTail := sTail) (sZero := sZero)
    (totalBound := lengthBound) (coarseBound := columnBound) (frozenBound := columnBound + 7 * (step / 3))
    (radiusBound := 4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step) (Nsave := Nsave) (decay := decay)
    (htotal := htotalInternal) (hcoarseNonneg := hcoarseNonneg) (hcoarse := hcolumn)
    (hloss := hlossOne) (p := source.pieces DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := (rightGeometry DE D).retainedLength + (rightGeometry DE D).enlargement) (hinverse := hrightRadius)
    (s := (stages DE D).right S χ) (hfrozen := hlengths.2.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := ((rightGeometry DE D).canonical_inverse_radius hZ).le) (hcutoff := rfl)
  refine ⟨hmetadata.1, hmetadata.2, ?_⟩
  intro hphysicalFiber
  have hphysical : ((source.pieces DE D).rightData.directSource
      ((source.pieces DE D).rightDivisorCoefficient S χ)).rows.Nonempty :=
    engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
  exact canonicalRightOriginalDualCalibration_amplitude_bounds
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := source.block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := source.radius)
    (firstMask := D.val) (δ := δ₁) (hδ := hδ₁)
    (hδhalf := hδ₁half) (cap := cap) (hcap := hcap)
    (orders := orders) (B := amplitude) (lo := lo)
    (hi := annulus) (loss := loss) (leftExponent := leftExponent)
    (rightExponent := rightExponent) (hB := hamplitude) (hlo := hlo)
    (hloOne := hloOne) (hhi := hannulus) (hlowerThreshold := hlowerThreshold)
    (hupperThreshold := hannulusZ) (domain := domainInternal) (hY₁ := hY₁)
    (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower)
    (hY₁le := hY₁le) (hY₂le := hY₂le) (profiles := profiles)
    (hrows := hrowsInternal) (ht := ht) (hlowerWindow := hlowerWindow)
    (hupperWindow := hwindow) (sTail := sTail) (sZero := sZero)
    (totalBound := lengthBound) (coarseBound := columnBound) (frozenBound := columnBound + 7 * (step / 3))
    (radiusBound := 4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step) (Nsave := Nsave) (decay := decay)
    (htotal := htotalInternal) (hcoarseNonneg := hcoarseNonneg) (hcoarse := hcolumn)
    (hloss := hlossOne) (p := source.pieces DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := (rightGeometry DE D).retainedLength + (rightGeometry DE D).enlargement) (hinverse := hrightRadius)
    (s := (stages DE D).right S χ) (hfrozen := hlengths.2.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := ((rightGeometry DE D).canonical_inverse_radius hZ).le) (hcutoff := rfl) (hphysical := hphysical)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectDualCalibration_left_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveDirectDualCalibration_right_bounds
