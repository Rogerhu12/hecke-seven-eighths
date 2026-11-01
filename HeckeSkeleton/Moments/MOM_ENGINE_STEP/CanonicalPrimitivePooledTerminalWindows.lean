import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledTerminalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralStageFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalLedgers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedPoolSourceTerminal

/-!
# Original pooled zero and tail windows for the same actual family

The actual main and 1/6/7 sources share their original first label,
physical divisor and independent second divisor. The physical fibre
bound is derived from the signed original representatives. The one
pool density is paid explicitly in the final exponent ledger.
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



namespace CanonicalPrimitivePooledTerminalWindows

/-- The numerical pool loss, including its one density exponent. -/
def zeroLoss (padding step loss cutoffExponent lengthBound columnBound δ ε eps : ℝ) : ℝ :=
  padding + 5 * step / 3 + (2 * loss + cutoffExponent) + 2 * loss +
    (4 * max lengthBound columnBound + 2) * δ +
      2 * (max lengthBound columnBound + 1) * ε + eps

/-- The original amplified fibre bound, fixed before the prime pool. -/
def fiberCap (M step : ℝ) : ℕ := max 1 ⌈(M + 6 * (step / 3)) / ((step / 3) / 2)⌉₊

end CanonicalPrimitivePooledTerminalWindows

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
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

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


local notation "leftAtoms" => Q.literalPrimitivePooledTerminal_left_atoms
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

local notation "rightAtoms" => Q.literalPrimitivePooledTerminal_right_atoms
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)

local notation "tupleDegree" => 2 * (cap + 2)
local notation "tailProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "zeroProfile" => (2 * amplitude ^ (cap + 2)) ^ 2 *
  sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (CanonicalRowBall.archTest K A.Sf 1)
local notation "geometry" => fun DE : source.CommonLabel =>
  fun D : ((source.block DE).mask source.mask).powerset =>
  (source.block DE).pooledTerminalGeometry internal pool D.val
    (2 * loss + cutoffExponent) (by positivity)
local notation "rowExponent" => literalPrimitivePoolRowExponent
  (lengthBound := lengthBound) (columnBound := columnBound)
  (loss := loss) (cutoffExponent := cutoffExponent)
local notation "fiberCap" => CanonicalPrimitivePooledTerminalWindows.fiberCap rowExponent step
local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstShift" => fun DE D =>
  Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D (firstTotal DE D)

variable (hlarge : 2 * (rowExponent / ((step / 3) / 2) +
  columnBound / ((step / 3) / 2)) ≤ Z ^ (step / 3 - eps))

/-- Every field is derived on the actual original pooled source. -/
def literalPrimitivePooledZeroAmplitudeWindows (εzero : ℝ) (hεzero : 0 ≤ εzero) :
    stages.CombinedZeroAmplitudeWindows terminal εzero
      (CanonicalPrimitivePooledTerminalWindows.zeroLoss
        padding step loss cutoffExponent lengthBound columnBound δ₁ εzero eps)
      zeroProfile rowExponent fiberCap firstTotal firstShift := by
  refine
    { exponentL := fun DE D _ _ tag => (geometry DE D false tag).sharpZeroExponent loss δ₁
      exponentR := fun DE D _ _ tag => (geometry DE D true tag).sharpZeroExponent loss δ₁
      row_left := fun _ _ _ => le_rfl
      row_right := fun _ _ _ => le_rfl
      large_left := ?_
      large_right := ?_
      fiber_left := ?_
      fiber_right := ?_
      tuples_left := fun DE D S χ tag => (leftAtoms DE D S χ tag).1
      tuples_right := fun DE D S χ tag => (rightAtoms DE D S χ tag).1
      amplitude_left := fun DE D S χ tag hf => ((leftAtoms DE D S χ tag).2.2 hf).2
      amplitude_right := fun DE D S χ tag hf => ((rightAtoms DE D S χ tag).2.2 hf).2
      exponent_left := ?_
      exponent_right := ?_ }
  · intro DE D S
    change 2 * (rowExponent / ((step / 3) / 2) +
      (0 + columnBound) / ((step / 3) / 2)) ≤ _
    simpa only [zero_add] using hlarge
  · intro DE D S
    change 2 * (rowExponent / ((step / 3) / 2) +
      (0 + columnBound) / ((step / 3) / 2)) ≤ _
    simpa only [zero_add] using hlarge
  · intro DE D S χ tag
    have horiginal : ((source.pools DE D).divisorPools.leftData S).rows ⊆
        ((firstSource.source DE).divisorRows D.val).image
          (fun q => q.out.val * (1 : A.R)) := by
      simpa only [mul_one] using
        (Finset.Subset.refl (((firstSource.source DE).divisorRows D.val).image
          (fun q => q.out.val)))
    exact ((source.pools DE D).divisorPools.leftData S).literalCanonicalStages_fiber_le
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      ((source.pools DE D).leftDivisorCoefficient S χ) P internal
      ((source.block DE).literalLeftCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ rowExponent le_rfl
      ((firstSource.source DE).divisorRows D.val) 1 one_ne_zero horiginal tag
  · intro DE D S χ tag
    have horiginal : ((source.pools DE D).divisorPools.rightData S).rows ⊆
        ((firstSource.source DE).divisorRows D.val).image
          (fun q => q.out.val * ((-1) : A.R)) := by
      simpa only [mul_neg_one] using
        (Finset.Subset.refl (((firstSource.source DE).divisorRows D.val).image
          (fun q => -q.out.val)))
    exact ((source.pools DE D).divisorPools.rightData S).literalCanonicalStages_fiber_le
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      ((source.pools DE D).rightDivisorCoefficient S χ) P internal
      ((source.block DE).literalRightCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ rowExponent le_rfl
      ((firstSource.source DE).divisorRows D.val) (-1) (neg_ne_zero.mpr one_ne_zero) horiginal tag
  · intro DE D S χ tag _
    have hcoordinates := (source.block DE).pooledTerminalGeometry_ideals internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) false tag
    have h := Q.literalPrimitiveGeometry_zero_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D false (geometry DE D false tag) hcoordinates
      hstep.le lengthBound columnBound htotal columnNorm domain loss εzero
      (((terminal DE D).left S χ).tag tag).zeroProductExponent (firstTotal DE D)
      hlossOne hεzero (leftAtoms DE D S χ tag).2.1
    have hfirst : (geometry DE D false tag).ideals.first.val = DE.val.1 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalLeftCoordinates_first]
    have hopposite : (geometry DE D false tag).ideals.opposite.val = DE.val.2 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalLeftCoordinates_opposite]
    have herr := (source.block DE).pooledTerminalGeometry_supportError internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) false tag
    simp only [OriginalNominalGeometry.boundary, hfirst, hopposite, herr] at h
    dsimp only [CanonicalPrimitivePooledTerminalWindows.zeroLoss]
    convert h using 1 <;> ring
  · intro DE D S χ tag _
    have hcoordinates := (source.block DE).pooledTerminalGeometry_ideals internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) true tag
    have h := Q.literalPrimitiveGeometry_zero_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D true (geometry DE D true tag) hcoordinates
      hstep.le lengthBound columnBound htotal columnNorm domain loss εzero
      (((terminal DE D).right S χ).tag tag).zeroProductExponent (firstTotal DE D)
      hlossOne hεzero (rightAtoms DE D S χ tag).2.1
    have hfirst : (geometry DE D true tag).ideals.first.val = DE.val.2 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalRightCoordinates_first]
    have hopposite : (geometry DE D true tag).ideals.opposite.val = DE.val.1 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalRightCoordinates_opposite]
    have herr := (source.block DE).pooledTerminalGeometry_supportError internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) true tag
    simp only [OriginalNominalGeometry.boundary, hfirst, hopposite, herr,
      firstActiveRadical_swap_of_support DE.val.1 DE.val.2 (source.block DE).common_support_eq] at h
    dsimp only [CanonicalPrimitivePooledTerminalWindows.zeroLoss]
    convert h using 1 <;> ring

local notation "zeroWindows" => Q.literalPrimitivePooledZeroAmplitudeWindows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ) (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂)
  (hZ := hZ) (hbudget := hbudget) (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff) (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain) (orders := orders) (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow) (hcutoffPower := hcutoffPower) (step := step)
  (hstep := hstep) (hloss := hloss) (hcutoffExponent := hcutoffExponent) (lo := lo) (hlo := hlo) (hloOne := hloOne) (hlowerThreshold := hlowerThreshold) (hlowerWindow := hlowerWindow) (hamplitude := hamplitude) (leftExponent := leftExponent) (rightExponent := rightExponent) (lengthBound := lengthBound)
  (columnBound := columnBound) (hY₁ := hY₁) (hY₂ := hY₂) (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le) (htotal := htotal) (hcolumn := hcolumn) (hlossOne := hlossOne) (hDiff := hDiff) (δ₂ := δ₂)
  (hδ₂ := hδ₂) (hδ₂half := hδ₂half) (sTail := sTail) (sZero := sZero) (Nsave := Nsave) (decay := decay) (hdecay := hdecay) (reference := reference) (href := href)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound) (pool := pool) (hdensity := hdensity)
  (hlarge := hlarge)

/-- The fixed physical saving is applied before the original pooled
classes are summed. The pool density is paid by the displayed loss. -/
def literalPrimitivePooledTailAmplitudeWindows (hsaving : 2 * columnBound ≤ Nsave) :
    stages.CombinedTailAmplitudeWindows terminal eps tailProfile
      rowExponent fiberCap firstTotal firstShift := by
  let U := zeroWindows 0 (le_refl _)
  refine
    { exponentL := fun _ _ _ _ _ => 0
      exponentR := fun _ _ _ _ _ => 0
      row_left := U.row_left
      row_right := U.row_right
      large_left := U.large_left
      large_right := U.large_right
      fiber_left := U.fiber_left
      fiber_right := U.fiber_right
      tuples_left := U.tuples_left
      tuples_right := U.tuples_right
      amplitude_left := ?_
      amplitude_right := ?_
      exponent_left := ?_
      exponent_right := ?_ }
  · intro DE D S χ tag hf
    simpa only [Real.rpow_zero, mul_one] using ((leftAtoms DE D S χ tag).2.2 hf).1
  · intro DE D S χ tag hf
    simpa only [Real.rpow_zero, mul_one] using ((rightAtoms DE D S χ tag).2.2 hf).1
  · intro DE D S χ tag _
    have hcoordinates := (source.block DE).pooledTerminalGeometry_ideals internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) false tag
    have h := Q.literalPrimitiveGeometry_tail_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D false (geometry DE D false tag) hcoordinates columnBound columnNorm
      0 Nsave (firstTotal DE D) (le_refl _) hsaving
    have hfirst : (geometry DE D false tag).ideals.first.val = DE.val.1 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalLeftCoordinates_first]
    have hopposite : (geometry DE D false tag).ideals.opposite.val = DE.val.2 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalLeftCoordinates_opposite]
    simp only [add_zero, OriginalNominalGeometry.boundary, hfirst, hopposite] at h
    convert h using 1 <;> ring
  · intro DE D S χ tag _
    have hcoordinates := (source.block DE).pooledTerminalGeometry_ideals internal pool D.val
      (2 * loss + cutoffExponent) (by positivity) true tag
    have h := Q.literalPrimitiveGeometry_tail_ledger μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      step DE D true (geometry DE D true tag) hcoordinates columnBound columnNorm
      0 Nsave (firstTotal DE D) (le_refl _) hsaving
    have hfirst : (geometry DE D true tag).ideals.first.val = DE.val.2 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalRightCoordinates_first]
    have hopposite : (geometry DE D true tag).ideals.opposite.val = DE.val.1 := by
      simp only [hcoordinates, Bool.false_eq_true, if_false, if_true,
        FirstCommonCharacterBlock.literalRightCoordinates_opposite]
    simp only [add_zero, OriginalNominalGeometry.boundary, hfirst, hopposite,
      firstActiveRadical_swap_of_support DE.val.1 DE.val.2 (source.block DE).common_support_eq] at h
    convert h using 1 <;> ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledZeroAmplitudeWindows
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooledTailAmplitudeWindows
