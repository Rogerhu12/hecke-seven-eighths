import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStageFibres

/-!
# Closed bounds on the actual pooled terminal family

Every conclusion projects the already constructed whole calibration.
The main and all three original valuation tags retain their precise
multiplicity, full frozen prime power and independent zero-product
exponent. Only nonzero physical fibres require amplitude estimates.
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

namespace AmplifierValuation

/-- The original one, six or seven summand in the same prime pool. -/
def sourceTag {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    {pool : PowerScaleExteriorPool A bad Z ell eps}
    (valuation : AmplifierValuation) (prime : pool.primes) : PoolSourceTag pool :=
  match valuation with
  | .one => .inr (.inl prime)
  | .six => .inr (.inr (.inl prime))
  | .seven => .inr (.inr (.inr prime))

end AmplifierValuation

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
local notation "raw" => (atoms).raw Y₁ Y₂


local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
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


variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)

local notation "columnNorm" => Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
  cap annulus loss leftExponent rightExponent columnBound hannulus hcap hannulusZ
  hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn

local notation "degree" => CanonicalOriginalTerminalPowers.primitiveDegree
  cap lengthBound columnBound step loss cutoffExponent
local notation "cutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z
local notation "hcutoff₂" => CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one
  cap lengthBound columnBound step loss cutoffExponent Nsave decay Z hZ.le hdecay
local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "leftRows" => Q.literalPrimitiveLeftPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "rightRows" => Q.literalPrimitiveRightPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent) (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (reference := reference) (href := href) (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (htotal := htotal) (hN := columnNorm) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half) («cutoff₂» := cutoff₂) («hcutoff₂» := hcutoff₂)

local notation "leftMainGeometry" => OriginalNominalGeometry.canonicalMain
  (a := internal) (step := step)
local notation "rightMainGeometry" => OriginalNominalGeometry.canonicalMain
  (a := internal) (step := step)
local notation "valuationGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := internal) pool

local notation "terminal" => Q.literalPrimitivePooledDualCalibration
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

/-- Exact metadata and amplitudes on the left main source. -/
theorem literalPrimitivePooledDualCalibration_left_main_bounds
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    (((terminal DE D).left S χ).main).windows.multiplicity =
        idealDivisorCount (DE.val.1 ^ 2) ^ (2 * (cap + 2)) ∧
      (((terminal DE D).left S χ).main).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.1) ∧
      ((((stages DE D).left S χ).main).fiber ≠ 0 →
        (((terminal DE D).left S χ).main).tailAmplitude ≤
          ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
            sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1) ∧
        (((terminal DE D).left S χ).main).zeroAmplitude ≤
          (((2 * amplitude ^ (cap + 2)) ^ 2 *
            sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
              2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.1) * δ₁ +
              ((OriginalNominalGeometry.canonicalMain (a := internal) (step := step)
      (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
      (zero_lt_one.trans hZ) (by positivity)).retainedLength + (OriginalNominalGeometry.canonicalMain (a := internal) (step := step)
      (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent)
      (zero_lt_one.trans hZ) (by positivity)).enlargement) + 2 * loss)) := by
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : (internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound columnNorm DE D
  have hDE := actual_common_pair_properties (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) DE
  have hnorm := actual_common_pair_norm (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((firstSource).ideal i).property.1)
    (fun i _ => ((firstSource).ideal i).property.1) columnNorm columnNorm DE
  let «GL» := leftMainGeometry (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  let GR := rightMainGeometry (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D false «GL» rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D true GR rfl
  have hmetadata := canonicalLeftMainOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := «GL».retainedLength + «GL».enlargement) (hinverse := hleftRadius)
    (s := ((stages DE D).left S χ).main) (hfrozen := hlengths.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := («GL».canonical_inverse_radius hZ).le) (hcutoff := rfl)
  refine ⟨hmetadata.1, hmetadata.2, ?_⟩
  intro hphysicalFiber
  have hphysical : (((source).pools DE D).divisorPools.leftData S).mainRows.Nonempty :=
    engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
  exact canonicalLeftMainOriginalDualCalibration_amplitude_bounds
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := «GL».retainedLength + «GL».enlargement) (hinverse := hleftRadius)
    (s := ((stages DE D).left S χ).main) (hfrozen := hlengths.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := («GL».canonical_inverse_radius hZ).le) (hcutoff := rfl) (hphysical := hphysical)

/-- Exact metadata and amplitudes on the right main source. -/
theorem literalPrimitivePooledDualCalibration_right_main_bounds
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) :
    (((terminal DE D).right S χ).main).windows.multiplicity =
        idealDivisorCount (DE.val.2 ^ 2) ^ (2 * (cap + 2)) ∧
      (((terminal DE D).right S χ).main).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.2) ∧
      ((((stages DE D).right S χ).main).fiber ≠ 0 →
        (((terminal DE D).right S χ).main).tailAmplitude ≤
          ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
            sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1) ∧
        (((terminal DE D).right S χ).main).zeroAmplitude ≤
          (((2 * amplitude ^ (cap + 2)) ^ 2 *
            sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
              2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.2) * δ₁ +
              ((OriginalNominalGeometry.canonicalMain (a := internal) (step := step)
      (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
      (zero_lt_one.trans hZ) (by positivity)).retainedLength + (OriginalNominalGeometry.canonicalMain (a := internal) (step := step)
      (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent)
      (zero_lt_one.trans hZ) (by positivity)).enlargement) + 2 * loss)) := by
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : (internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound columnNorm DE D
  have hDE := actual_common_pair_properties (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) DE
  have hnorm := actual_common_pair_norm (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((firstSource).ideal i).property.1)
    (fun i _ => ((firstSource).ideal i).property.1) columnNorm columnNorm DE
  let «GL» := leftMainGeometry (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  let GR := rightMainGeometry (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D false «GL» rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D true GR rfl
  have hmetadata := canonicalRightMainOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := GR.retainedLength + GR.enlargement) (hinverse := hrightRadius)
    (s := ((stages DE D).right S χ).main) (hfrozen := hlengths.2.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := (GR.canonical_inverse_radius hZ).le) (hcutoff := rfl)
  refine ⟨hmetadata.1, hmetadata.2, ?_⟩
  intro hphysicalFiber
  have hphysical : (((source).pools DE D).divisorPools.rightData S).mainRows.Nonempty :=
    engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
  exact canonicalRightMainOriginalDualCalibration_amplitude_bounds
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (S := S)
    (χ := χ) (inverseRadiusExponent := GR.retainedLength + GR.enlargement) (hinverse := hrightRadius)
    (s := ((stages DE D).right S χ).main) (hfrozen := hlengths.2.1.trans (le_add_of_nonneg_right (by positivity))) (hmaskEmpty := rfl)
    (hradius := (GR.canonical_inverse_radius hZ).le) (hcutoff := rfl) (hphysical := hphysical)

/-- All three left valuation tags use their original full frozen power. -/
theorem literalPrimitivePooledDualCalibration_left_valuation_bounds
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes) :
    (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).windows.multiplicity =
        idealDivisorCount (DE.val.1 ^ 2) ^ (2 * (cap + 2)) *
          (valuation.multiplicity + valuation.multiplicity + 1) ^ (2 * (cap + 2)) ∧
      (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss -
          idealLogLength Z (DE.val.1 * (powerIdeal prime.val valuation.multiplicity).val)) ∧
      ((((stages DE D).left S χ).tag (valuation.sourceTag prime)).fiber ≠ 0 →
        (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).tailAmplitude ≤
          ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
            sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1) ∧
        (((terminal DE D).left S χ).tag (valuation.sourceTag prime)).zeroAmplitude ≤
          (((2 * amplitude ^ (cap + 2)) ^ 2 *
            sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
              2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.1) * δ₁ +
              ((OriginalNominalGeometry.canonicalPoolError (a := internal) pool valuation prime
      (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent) (by positivity)).retainedLength + (OriginalNominalGeometry.canonicalPoolError (a := internal) pool valuation prime
      (((source).block DE).literalLeftCoordinates D.val) (2 * loss + cutoffExponent) (by positivity)).enlargement) + 2 * loss)) := by
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : (internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound columnNorm DE D
  have hDE := actual_common_pair_properties (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) DE
  have hnorm := actual_common_pair_norm (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((firstSource).ideal i).property.1)
    (fun i _ => ((firstSource).ideal i).property.1) columnNorm columnNorm DE
  let «GL» := leftMainGeometry (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  let GR := rightMainGeometry (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D false «GL» rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D true GR rfl
  let G := valuationGeometry valuation prime (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (by positivity)
  have hRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D false G rfl
  let valuationStage := (((source).pools DE D).divisorPools.leftData S).literalValuationStage
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (μv := μv) (hDiff := hDiff) (ν := ν)
    (((source).pools DE D).leftDivisorCoefficient S χ) P internal
    (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
    δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
  have hmetadata := canonicalLeftPoolOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (prime := prime.val)
    (n := valuation.multiplicity) (S := S) (χ := χ)
    (inverseRadiusExponent := G.retainedLength + G.enlargement) (hinverse := hRadius) (s := valuationStage)
    (hfrozen := pool.original_frozen_length_le DE.val.1 hDE.1 columnBound hnorm.1 valuation prime) (hmaskEmpty := rfl) (hradius := (G.canonical_inverse_radius hZ).le)
    (hcutoff := rfl)
  refine ⟨?_, ?_, ?_⟩
  · cases valuation <;> exact hmetadata.1
  · cases valuation <;> exact hmetadata.2
  · intro hphysicalFiber
    have hphysical : ((((source).pools DE D).divisorPools.leftData S).errorRows prime.val).Nonempty := by
      cases valuation <;> exact engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
    have hamp := canonicalLeftPoolOriginalDualCalibration_amplitude_bounds
      (μv := μv) (ν := ν) (Q := Q)
      (W := W) (ξ := ξ) (a := internal)
      (Z := Z) (t := t) (Y₁ := Y₁)
      (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
      (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
      (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
      (hloss := hlossOne) (p := (source).pools DE D) (prime := prime.val)
      (n := valuation.multiplicity) (S := S) (χ := χ)
      (inverseRadiusExponent := G.retainedLength + G.enlargement) (hinverse := hRadius) (s := valuationStage)
      (hfrozen := pool.original_frozen_length_le DE.val.1 hDE.1 columnBound hnorm.1 valuation prime) (hmaskEmpty := rfl) (hradius := (G.canonical_inverse_radius hZ).le)
      (hcutoff := rfl) (hphysical := hphysical)
    cases valuation <;> exact hamp

/-- All three right valuation tags use their original full frozen power. -/
theorem literalPrimitivePooledDualCalibration_right_valuation_bounds
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
    (S : divisorPool ((source).pools DE D).rightData.columns
      (fun j => (((source).pools DE D).rightData.ideal j).val))
    (χ : (PUnit × PUnit) →* Circle) (valuation : AmplifierValuation) (prime : pool.primes) :
    (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).windows.multiplicity =
        idealDivisorCount (DE.val.2 ^ 2) ^ (2 * (cap + 2)) *
          (valuation.multiplicity + valuation.multiplicity + 1) ^ (2 * (cap + 2)) ∧
      (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss -
          idealLogLength Z (DE.val.2 * (powerIdeal prime.val valuation.multiplicity).val)) ∧
      ((((stages DE D).right S χ).tag (valuation.sourceTag prime)).fiber ≠ 0 →
        (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).tailAmplitude ≤
          ((2 * amplitude ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
            sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1) ∧
        (((terminal DE D).right S χ).tag (valuation.sourceTag prime)).zeroAmplitude ≤
          (((2 * amplitude ^ (cap + 2)) ^ 2 *
            sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
              (CanonicalRowBall.archTest K A.Sf 1)) / (Ideal.absNorm S.val : ℝ)) *
            Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
              2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.val.2) * δ₁ +
              ((OriginalNominalGeometry.canonicalPoolError (a := internal) pool valuation prime
      (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent) (by positivity)).retainedLength + (OriginalNominalGeometry.canonicalPoolError (a := internal) pool valuation prime
      (((source).block DE).literalRightCoordinates D.val) (2 * loss + cutoffExponent) (by positivity)).enlargement) + 2 * loss)) := by
  have hrowsInternal : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  have domainInternal : PairedEngineDomain centered (data ξ) internal Z Y₁ Y₂ floor padding :=
    domain.withSupportLength (Q.fullSupportLength Z)
  have htotalInternal : (internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength ≤ lengthBound := by
    simpa only [← domain.total_length] using htotal
  have hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss := by
    have hl := (Real.rpow_le_rpow_left_iff hZ).mp hleftPower
    have hr := (Real.rpow_le_rpow_left_iff hZ).mp hrightPower
    have hg : 0 ≤ (data ξ).geometry.totalLength :=
      Finset.sum_nonneg (fun i _ => ((data ξ).geometry.slots i).length_pos.le)
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  have hlengths := Q.literalPrimitiveFirstIdealLengths μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half columnBound columnNorm DE D
  have hDE := actual_common_pair_properties (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) DE
  have hnorm := actual_common_pair_norm (firstSource).columns (firstSource).columns
    (fun i => ((firstSource).ideal i).val) (fun i => ((firstSource).ideal i).val) (Z ^ columnBound)
    (fun i _ => ((firstSource).ideal i).property.1)
    (fun i _ => ((firstSource).ideal i).property.1) columnNorm columnNorm DE
  let «GL» := leftMainGeometry (((source).block DE).literalLeftCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  let GR := rightMainGeometry (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (zero_lt_one.trans hZ) (by positivity)
  have hleftRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D false «GL» rfl
  have hrightRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D true GR rfl
  let G := valuationGeometry valuation prime (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (by positivity)
  have hRadius := Q.literalPrimitiveGeometry_inverse_bound μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    step hstep.le lengthBound columnBound htotal columnNorm DE D true G rfl
  let valuationStage := (((source).pools DE D).divisorPools.rightData S).literalValuationStage
    (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (μv := μv) (hDiff := hDiff) (ν := ν)
    (((source).pools DE D).rightDivisorCoefficient S χ) P internal
    (((source).block DE).literalRightCoordinates D.val)
    (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
    δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ valuation prime
  have hmetadata := canonicalRightPoolOriginalDualCalibration_metadata
    (μv := μv) (ν := ν) (Q := Q)
    (W := W) (ξ := ξ) (a := internal)
    (Z := Z) (t := t) (Y₁ := Y₁)
    (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
    (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
    (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
    (hloss := hlossOne) (p := (source).pools DE D) (prime := prime.val)
    (n := valuation.multiplicity) (S := S) (χ := χ)
    (inverseRadiusExponent := G.retainedLength + G.enlargement) (hinverse := hRadius) (s := valuationStage)
    (hfrozen := pool.original_frozen_length_le DE.val.2 hDE.2.1 columnBound hnorm.2 valuation prime) (hmaskEmpty := rfl) (hradius := (G.canonical_inverse_radius hZ).le)
    (hcutoff := rfl)
  refine ⟨?_, ?_, ?_⟩
  · cases valuation <;> exact hmetadata.1
  · cases valuation <;> exact hmetadata.2
  · intro hphysicalFiber
    have hphysical : ((((source).pools DE D).divisorPools.rightData S).errorRows prime.val).Nonempty := by
      cases valuation <;> exact engineOrbitMultiplicity_rows_nonempty _ hphysicalFiber
    have hamp := canonicalRightPoolOriginalDualCalibration_amplitude_bounds
      (μv := μv) (ν := ν) (Q := Q)
      (W := W) (ξ := ξ) (a := internal)
      (Z := Z) (t := t) (Y₁ := Y₁)
      (Y₂ := Y₂) (centered := centered) (b := (source).block DE)
      (C := C) (φ := CanonicalRowBall.archTest K A.Sf 1) (firstFiniteTest := rowBallFiniteFamily K A.Sf 1)
      (hlc := rowBallFiniteFamily_locallyConstant K A.Sf 1) (hcs := rowBallFiniteFamily_compactSupport K A.Sf 1) (firstRadius := (source).radius)
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
      (hloss := hlossOne) (p := (source).pools DE D) (prime := prime.val)
      (n := valuation.multiplicity) (S := S) (χ := χ)
      (inverseRadiusExponent := G.retainedLength + G.enlargement) (hinverse := hRadius) (s := valuationStage)
      (hfrozen := pool.original_frozen_length_le DE.val.2 hDE.2.1 columnBound hnorm.2 valuation prime) (hmaskEmpty := rfl) (hradius := (G.canonical_inverse_radius hZ).le)
      (hcutoff := rfl) (hphysical := hphysical)
    cases valuation <;> exact hamp

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualCalibration_left_main_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualCalibration_right_main_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualCalibration_left_valuation_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledDualCalibration_right_valuation_bounds
