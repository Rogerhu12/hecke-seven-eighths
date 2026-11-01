import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledMassWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalTaggedLocalIndex

/-!
# The actual pooled outer scalar and its arithmetic index

The second physical fibre is bounded from the same signed original
rows. Supporting the source can only decrease that fibre. The original
pool scalar and its moving power are then identified with the same
amplified arithmetic index, keeping the original prime and valuation.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
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

namespace CanonicalLiteralPrimitivePooledScalar

/-- Fixed before the source, prime and both continuous parameters. -/
def fiberCap (rowExponent step : ℝ) : ℕ :=
  max 1 ⌈(rowExponent + 6 * (step / 3)) / ((step / 3) / 2)⌉₊

end CanonicalLiteralPrimitivePooledScalar

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

variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (cap : ℕ) (loss cutoffExponent : ℝ)
variable (hloss : 0 ≤ loss) (hcutoffExponent : 0 ≤ cutoffExponent)
variable (step error mesh : ℝ) (hstep : 0 < step) (herror : 0 ≤ error) (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable (hsmall : 2 * (2 * loss + cutoffExponent) ≤ step)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (hcutoffPower₂ : cutoff₂ ≤ Z ^ cutoffExponent)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
variable (orders : Finset (ℕ × ℕ)) (originalBound : ℝ) (horiginalBound : 0 ≤ originalBound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : hi ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)

variable (lengthBound columnBound : ℝ)
variable (hlengthBound : 0 ≤ lengthBound) (hcolumnBound : 0 ≤ columnBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hN : ∀ i ∈ (firstSource).columns,
  (Ideal.absNorm ((firstSource).ideal i).val : ℝ) ≤ Z ^ columnBound)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "stages" => Q.literalPrimitivePooledStages
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "exceptional" => Q.literalPrimitivePooledPredicates
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "normalization" => Q.literalPrimitivePooledNormalization
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "leftRows" => Q.literalPrimitiveLeftPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "rightRows" => Q.literalPrimitiveRightPooledRows
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := originalWindow) (hrows := hrows) (ht := htime) (hwindow := fun _ h => h.2)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

local notation "rowExponent" => literalPrimitivePoolRowExponent
  (lengthBound := lengthBound) (columnBound := columnBound)
  (loss := loss) (cutoffExponent := cutoffExponent)
local notation "fiberCap" => CanonicalLiteralPrimitivePooledScalar.fiberCap rowExponent step

/-- These are the windows already stored in the original divisor pool. -/
theorem literalPrimitivePooled_originalWindowExponents
    (j : (stages).supported.gated.CoveredLeafKey (raw).originalAtlas) :
    (stages).supported.gated.originalRowExponentAt (raw).originalAtlas j = rowExponent ∧
      (stages).supported.gated.originalFrozenExponentAt (raw).originalAtlas j = columnBound := by
  rcases j with ⟨DE, D, S, χ, leaf | leaf⟩
  all_goals
    change rowExponent = rowExponent ∧ 0 + columnBound = columnBound
    exact ⟨rfl, zero_add _⟩

/-- The main and all three valuation tags use the original signed
physical rows. The supported source has no larger fibre. -/
theorem literalPrimitivePooled_originalSecondFiber_le
    (j : (stages).supported.gated.CoveredLeafKey (raw).originalAtlas) :
    (stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j ≤ fiberCap := by
  rcases j with ⟨DE, D, S, χ, leaf | leaf⟩
  · let tag := (((stages).supported.gated DE D).left S χ).leafTag
        (((source).pools DE D).leftSourceCovers (raw).originalAtlas S χ) leaf
    have horiginal : (((source).pools DE D).divisorPools.leftData S).rows ⊆
        (((firstSource).source DE).divisorRows D.val).image
          (fun q => q.out.val * (1 : A.R)) := by
      simpa only [mul_one] using
        (Finset.Subset.refl ((((firstSource).source DE).divisorRows D.val).image
          (fun q => q.out.val)))
    have hraw := (((source).pools DE D).divisorPools.leftData S).literalCanonicalStages_fiber_le
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).leftDivisorCoefficient S χ) P internal
      (((source).block DE).literalLeftCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (leftRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ rowExponent le_rfl
      (((firstSource).source DE).divisorRows D.val) 1 one_ne_zero horiginal tag
    have hprepared :
        (((stages DE D).left S χ).supported.gated.tag tag).fiber ≤
          (((stages DE D).left S χ).tag tag).fiber := by
      rcases tag with u | p | p | p
      all_goals
        change (if _ then 0 else _) ≤ _
        split_ifs
        · exact Nat.zero_le _
        · exact le_rfl
    exact hprepared.trans hraw
  · let tag := (((stages).supported.gated DE D).right S χ).leafTag
        (((source).pools DE D).rightSourceCovers (raw).originalAtlas S χ) leaf
    have horiginal : (((source).pools DE D).divisorPools.rightData S).rows ⊆
        (((firstSource).source DE).divisorRows D.val).image
          (fun q => q.out.val * ((-1) : A.R)) := by
      simpa only [mul_neg_one] using
        (Finset.Subset.refl ((((firstSource).source DE).divisorRows D.val).image
          (fun q => -q.out.val)))
    have hraw := (((source).pools DE D).divisorPools.rightData S).literalCanonicalStages_fiber_le
      (hΓ := actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (μv := μv) (hDiff := hDiff) (ν := ν)
      (((source).pools DE D).rightDivisorCoefficient S χ) P internal
      (((source).block DE).literalRightCoordinates D.val)
      (2 * loss + cutoffExponent) (by positivity) hstep (rightRows DE D S)
      δ₂ hδ₂ hδ₂half cutoff₂ hcutoff₂ rowExponent le_rfl
      (((firstSource).source DE).divisorRows D.val) (-1) (neg_ne_zero.mpr one_ne_zero) horiginal tag
    have hprepared :
        (((stages DE D).right S χ).supported.gated.tag tag).fiber ≤
          (((stages DE D).right S χ).tag tag).fiber := by
      rcases tag with u | p | p | p
      all_goals
        change (if _ then 0 else _) ≤ _
        split_ifs
        · exact Nat.zero_le _
        · exact le_rfl
    exact hprepared.trans hraw

local notation "windowExponents" => literalPrimitivePooled_originalWindowExponents
  (Q := Q)
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (hi := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hhi := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lo := lo) (orders := orders) (originalBound := originalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (step := step) (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)
local notation "secondFiberBound" => literalPrimitivePooled_originalSecondFiber_le
  (Q := Q)
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (hi := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hhi := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lo := lo) (orders := orders) (originalBound := originalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (step := step) (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

local notation "labels" => (stages).supported.gated.arithmeticLabels
  (raw).originalAtlas hcap exceptional normalization
local notation "tags" => (stages).supported.gated.arithmeticTag
  (raw).originalAtlas exceptional normalization
local notation "tagMem" => (stages).supported.gated.arithmeticTag_mem
  (raw).originalAtlas exceptional normalization
local notation "indices" => (stages).supported.gated.arithmeticIndex
  (raw).originalAtlas hcap exceptional normalization
local notation "movingAt" => fun j =>
  ((stages).supported.gated.originalNominalTagAt (raw).originalAtlas j.val).movingLength Z +
    ((stages).supported.gated.originalNominalTagAt (raw).originalAtlas j.val).poolLength step
local notation "localWeight" => fun j =>
  ((labels).localBranch tags j).indexWeight ((labels).localIndex tags j)
local notation "amplifiedWeight" => fun j =>
  amplifiedIndexWeight pool rowExponent columnBound
    ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j)

private theorem localWeight_eq_harmonic
    (j : (stages).supported.gated.liveLeaves (raw).originalAtlas exceptional normalization) :
    AmplifiedCommonIndex.harmonicWeight pool
        ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j) = localWeight j := by
  change AmplifiedCommonIndex.harmonicWeight pool
    ((labels).mainCarrier tags) ((labels).errorCarrier tags)
    ((labels).amplifiedIndex tags pool tagMem j) = _
  cases h : tags j with
  | none => simp only [OriginalArithmeticLabels.amplifiedIndex, h,
      AmplifiedCommonIndex.harmonicWeight, OriginalArithmeticLabels.localBranch,
      OriginalArithmeticLabels.localIndex]
  | some q => simp only [OriginalArithmeticLabels.amplifiedIndex, h,
      AmplifiedCommonIndex.harmonicWeight, OriginalArithmeticLabels.localBranch,
      OriginalArithmeticLabels.localIndex]

local notation "harmonic_eq" => localWeight_eq_harmonic
  (Q := Q)
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (hi := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hhi := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lo := lo) (orders := orders) (originalBound := originalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (step := step) (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

/-- The original pool scalar contains precisely one tag weight.
Its actual moving length turns that weight into the original amplified
index, with the same common labels and occurrence allocation. -/
theorem literalPrimitivePooled_originalScalar_moving_index
    (j : (stages).supported.gated.liveLeaves (raw).originalAtlas exceptional normalization) :
    (stages).supported.gated.originalScalarAt (raw).originalAtlas j.val *
        Z ^ movingAt j * localWeight j =
      (((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ) / 2) *
        amplifiedWeight j := by
  have hs := (stages).supported.gated.originalScalarAt_eq_originalTagWeight
    (raw).originalAtlas hcap exceptional normalization j
  have hw := windowExponents j.val
  rw [hw.1, hw.2] at hs
  have hm := (stages).supported.gated.originalNominalTagAt_movingLength
    (raw).originalAtlas hcap exceptional normalization j
  rw [show 3 * (step / 3) = step by ring] at hm
  have ht := AmplifiedCommonIndex.originalTagWeight_mul_rpow pool rowExponent columnBound
    ((labels).mainCarrier tags) ((labels).errorCarrier tags) hZ (indices j)
  rw [harmonic_eq j] at ht
  rw [hs, hm]
  change ((1 * ((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ)) / 2 *
      AmplifiedCommonIndex.originalTagWeight pool rowExponent columnBound
        ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j)) *
      Z ^ AmplifiedCommonIndex.movingLength pool
        ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j) * localWeight j = _
  calc
    _ = (((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ) / 2) *
        (AmplifiedCommonIndex.originalTagWeight pool rowExponent columnBound
          ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j) *
          Z ^ AmplifiedCommonIndex.movingLength pool
            ((labels).mainCarrier tags) ((labels).errorCarrier tags) (indices j) * localWeight j) := by ring
    _ = _ := congrArg
      (fun x : ℝ =>
        (((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ) / 2) * x) ht

local notation "scalarIdentity" => literalPrimitivePooled_originalScalar_moving_index
  (Q := Q)
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (hi := hi) (loss := loss) (cutoffExponent := cutoffExponent)
  (hhi := hhi) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (lo := lo) (orders := orders) (originalBound := originalBound)
  (originalWindow := originalWindow) (hrows := hrows) (htime := htime)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)
  (step := step) (hstep := hstep) (hDiff := hDiff) (δ₂ := δ₂) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
  (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂)

/-- The finite physical-fibre cap is the only factor left outside the
same amplified arithmetic index. No new density or prime sum occurs. -/
theorem literalPrimitivePooled_originalScalar_moving_index_le
    (j : (stages).supported.gated.liveLeaves (raw).originalAtlas exceptional normalization) :
    (stages).supported.gated.originalScalarAt (raw).originalAtlas j.val *
        Z ^ movingAt j * localWeight j ≤ (fiberCap : ℝ) * amplifiedWeight j := by
  rw [scalarIdentity j]
  have hf : ((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ) ≤
      (fiberCap : ℝ) := by
    exact_mod_cast secondFiberBound j.val
  have hfhalf :
      ((stages).supported.gated.originalSecondFiberAt (raw).originalAtlas j.val : ℝ) / 2 ≤
        (fiberCap : ℝ) :=
    (div_le_self (Nat.cast_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans hf
  have hM : 0 ≤ rowExponent := by
    dsimp only [literalPrimitivePoolRowExponent]
    positivity
  exact mul_le_mul_of_nonneg_right hfhalf
    (amplifiedIndexWeight_nonneg pool rowExponent columnBound
      ((labels).mainCarrier tags) ((labels).errorCarrier tags) (zero_lt_one.trans hZ).le
      pool.exponent_pos hM hdensity.le (indices j))

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_originalWindowExponents
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_originalSecondFiber_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_originalScalar_moving_index
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitivePooled_originalScalar_moving_index_le
