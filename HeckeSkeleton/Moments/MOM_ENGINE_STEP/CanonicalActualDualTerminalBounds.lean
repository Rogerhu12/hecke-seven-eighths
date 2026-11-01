import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualDualTerminal

/-!
# Closed amplitudes of the six original dual calibrations

These are projections of the actual constructors, with the same source,
column carrier and divisor. Tuple and zero-product metadata hold even
when every original coefficient vanishes. The amplitude bounds require
only a genuine physical row, supplied by a nonzero supported fibre.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical MeasureTheory
open HeckePort.Moments HeckePort.Moments.MobiusRegroup

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
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem actualDualDivisor_ne_zero {ι : Type*}
    (columns : Finset ι) (ideal : ι → A.Exterior)
    (S : divisorPool columns (fun j => (ideal j).val)) : S.val ≠ 0 := by
  obtain ⟨j, _, hSj⟩ := Finset.mem_biUnion.mp S.property
  have hd := (mem_idealDivisors (ideal j).property.1).mp hSj
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (ideal j).property.1 hd

namespace CompleteMovingRowRecipe

variable {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {J : Type*} {data : J → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable (W : NormProfileRecipe data) (ξ : J)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).columnExterior
  ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (firstFiniteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (firstFiniteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (firstFiniteTest v))
variable (firstRadius : {r : ℝ // 0 < r}) (firstMask : Finset (HeightOneSpectrum A.R))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

variable (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (orders : Finset (ℕ × ℕ))
variable (B lo hi loss leftExponent rightExponent : ℝ)
variable (hB : 1 ≤ B) (hlo : 0 < lo) (hloOne : lo ≤ 1) (hhi : 1 ≤ hi)
variable (hlowerThreshold : (lo ^ (cap + 2))⁻¹ ≤ Z ^ loss)
variable (hupperThreshold : hi ^ (cap + 2) ≤ Z ^ loss)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
variable (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
variable (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) (data ξ) B)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain)
variable (hlowerWindow : window ⊆ Set.Ici lo) (hupperWindow : window ⊆ Set.Iic hi)
variable (sTail sZero : Finset (ℕ × ℕ))
variable (totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent : ℝ)
variable (htotal : a.n₁ + a.n₂ + (data ξ).geometry.totalLength ≤ totalBound)
variable (hcoarseNonneg : 0 ≤ leftExponent + rightExponent + (data ξ).geometry.totalLength + loss)
variable (hcoarse : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ coarseBound)
variable (hloss : loss ≤ 1) (hinverse : inverseRadiusExponent ≤ radiusBound)

local notation "original" => Q.originalTerminalAtoms W ξ a Z t
local notation "raw" => (Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂
local notation "values" => (Q.originalTerminalAtoms W ξ a Z t).values Y₁ Y₂
local notation "hUnits" => actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))

section Direct

variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν b C
    ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).exteriorColumns
    ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).exteriorColumns φ
    (((Q.originalTerminalAtoms W ξ a Z t).values Y₁ Y₂).coefficient centered)
    (((Q.originalTerminalAtoms W ξ a Z t).values Y₁ Y₂).coefficient centered)
    firstFiniteTest hlc hcs firstRadius firstMask δ hδ hδhalf) M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

section LeftDirectBounds

variable (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      (p.leftData.directSource (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.1 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalLeftOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (s := s) (hfrozen := hfrozen)
  (hmaskEmpty := hmaskEmpty) (hradius := hradius) (hcutoff := hcutoff)

theorem canonicalLeftOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.1) := by
  unfold canonicalLeftOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalLeftOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalLeftOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalLeftTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalLeftOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalLeftOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalLeftTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalLeftOriginalDualCalibration_amplitude_bounds
    (hphysical : (p.leftData.directSource (p.leftDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.1) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalLeftOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let post := p.canonicalLeftOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let tuples := p.originalLeftTuples raw S χ cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalLeftOriginalDualCalibration, b.common_left] using h

end LeftDirectBounds

section RightDirectBounds

variable (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      (p.rightData.directSource (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.2 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalRightOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (s := s) (hfrozen := hfrozen)
  (hmaskEmpty := hmaskEmpty) (hradius := hradius) (hcutoff := hcutoff)

theorem canonicalRightOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.2) := by
  unfold canonicalRightOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalRightOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalRightOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalRightTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalRightOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalRightOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalRightTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalRightOriginalDualCalibration_amplitude_bounds
    (hphysical : (p.rightData.directSource (p.rightDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.2) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalRightOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let post := p.canonicalRightOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let tuples := p.originalRightTuples raw S χ cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalRightOriginalDualCalibration, b.common_right] using h

end RightDirectBounds

end Direct

section Pool

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad base ell eps}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv ν b C
    ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).exteriorColumns
    ((Q.originalTerminalAtoms W ξ a Z t).raw Y₁ Y₂).exteriorColumns φ
    (((Q.originalTerminalAtoms W ξ a Z t).values Y₁ Y₂).coefficient centered)
    (((Q.originalTerminalAtoms W ξ a Z t).values Y₁ Y₂).coefficient centered)
    firstFiniteTest hlc hcs firstRadius firstMask δ hδ hδhalf) pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

section LeftMainBounds

variable (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.1 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalLeftMainOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (s := s) (hfrozen := hfrozen)
  (hmaskEmpty := hmaskEmpty) (hradius := hradius) (hcutoff := hcutoff)

theorem canonicalLeftMainOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.1) := by
  unfold canonicalLeftMainOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalLeftMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalLeftMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalLeftMainTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalLeftMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalLeftMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalLeftMainTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalLeftMainOriginalDualCalibration_amplitude_bounds
    (hphysical : ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.1) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalLeftMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let post := p.canonicalLeftMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let tuples := p.originalLeftMainTuples raw S χ cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalLeftMainOriginalDualCalibration, b.common_left] using h

end LeftMainBounds

section RightMainBounds

variable (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.2 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalRightMainOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (s := s) (hfrozen := hfrozen)
  (hmaskEmpty := hmaskEmpty) (hradius := hradius) (hcutoff := hcutoff)

theorem canonicalRightMainOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.2) := by
  unfold canonicalRightMainOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalRightMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalRightMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalRightMainTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalRightMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let post := p.canonicalRightMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ
      let tuples := p.originalRightMainTuples raw S χ cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalRightMainOriginalDualCalibration_amplitude_bounds
    (hphysical : ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.2) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalRightMainOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let post := p.canonicalRightMainOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ
    let tuples := p.originalRightMainTuples raw S χ cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalRightMainOriginalDualCalibration, b.common_right] using h

end RightMainBounds

section LeftPoolBounds

variable (prime : ExteriorPrime A) (n : ℕ)
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.leftData S).residualSource prime n (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z (DE.1 * (powerIdeal prime n).val) ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalLeftPoolOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (prime := prime) (n := n)
  (s := s) (hfrozen := hfrozen) (hmaskEmpty := hmaskEmpty) (hradius := hradius)
  (hcutoff := hcutoff)

theorem canonicalLeftPoolOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.1 ^ 2) ^ (2 * (cap + 2)) * (n + n + 1) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z (DE.1 * (powerIdeal prime n).val)) := by
  unfold canonicalLeftPoolOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalLeftPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let post := p.canonicalLeftPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let tuples := p.originalLeftPoolTuples raw S χ prime n cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalLeftPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let post := p.canonicalLeftPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let tuples := p.originalLeftPoolTuples raw S χ prime n cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalLeftPoolOriginalDualCalibration_amplitude_bounds
    (hphysical : ((p.divisorPools.leftData S).residualSource prime n (p.leftDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.1) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalLeftPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
    let post := p.canonicalLeftPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
    let tuples := p.originalLeftPoolTuples raw S χ prime n cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalLeftPoolOriginalDualCalibration, b.common_left] using h

end LeftPoolBounds

section RightPoolBounds

variable (prime : ExteriorPrime A) (n : ℕ)
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.rightData S).residualSource prime n (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z (DE.2 * (powerIdeal prime n).val) ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay)

local notation "terminal" => canonicalRightPoolOriginalDualCalibration
  (μv := μv) (ν := ν) (Q := Q) (W := W)
  (ξ := ξ) (a := a) (Z := Z) (t := t)
  (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered) (b := b)
  (C := C) (φ := φ) (firstFiniteTest := firstFiniteTest) (hlc := hlc)
  (hcs := hcs) (firstRadius := firstRadius) (firstMask := firstMask) (δ := δ)
  (hδ := hδ) (hδhalf := hδhalf) (cap := cap) (hcap := hcap)
  (orders := orders) (B := B) (lo := lo) (hi := hi)
  (loss := loss) (leftExponent := leftExponent) (rightExponent := rightExponent) (hB := hB)
  (hlo := hlo) (hloOne := hloOne) (hhi := hhi) (hlowerThreshold := hlowerThreshold)
  (hupperThreshold := hupperThreshold) (domain := domain) (hY₁ := hY₁) (hY₂ := hY₂)
  (hleftPower := hleftPower) (hrightPower := hrightPower) (hY₁le := hY₁le) (hY₂le := hY₂le)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hlowerWindow := hlowerWindow)
  (hupperWindow := hupperWindow) (sTail := sTail) (sZero := sZero) (totalBound := totalBound)
  (coarseBound := coarseBound) (frozenBound := frozenBound) (radiusBound := radiusBound) (Nsave := Nsave)
  (decay := decay) (inverseRadiusExponent := inverseRadiusExponent) (htotal := htotal) (hcoarseNonneg := hcoarseNonneg)
  (hcoarse := hcoarse) (hloss := hloss) (hinverse := hinverse) (p := p)
  (S := S) (χ := χ) (prime := prime) (n := n)
  (s := s) (hfrozen := hfrozen) (hmaskEmpty := hmaskEmpty) (hradius := hradius)
  (hcutoff := hcutoff)

theorem canonicalRightPoolOriginalDualCalibration_metadata :
    (terminal).windows.multiplicity = idealDivisorCount (DE.2 ^ 2) ^ (2 * (cap + 2)) * (n + n + 1) ^ (2 * (cap + 2)) ∧
      (terminal).zeroProductExponent = 2 * max 0
        (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z (DE.2 * (powerIdeal prime n).val)) := by
  unfold canonicalRightPoolOriginalDualCalibration
  constructor
  · exact
      let numerator := p.canonicalRightPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let post := p.canonicalRightPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let tuples := p.originalRightPoolTuples raw S χ prime n cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_multiplicity original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff
  · exact
      let numerator := p.canonicalRightPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let post := p.canonicalRightPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
        φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
        hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
      let tuples := p.originalRightPoolTuples raw S χ prime n cap hcap
      s.canonicalOriginalDualCalibrationOfTuples_zeroProductExponent original numerator post tuples
        (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
        (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
        (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
          orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
          hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
          profiles hrows ht hlowerWindow hupperWindow sTail sZero
          totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
          htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

theorem canonicalRightPoolOriginalDualCalibration_amplitude_bounds
    (hphysical : ((p.divisorPools.rightData S).residualSource prime n (p.rightDivisorCoefficient S χ)).rows.Nonempty) :
    (terminal).tailAmplitude ≤ ((2 * B ^ (cap + 2)) ^ 2 / (Ideal.absNorm S.val : ℝ)) *
        sTail.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile ∧
      (terminal).zeroAmplitude ≤
        (((2 * B ^ (cap + 2)) ^ 2 *
          sZero.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) s.profile) /
            (Ideal.absNorm S.val : ℝ)) *
          Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
            2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + loss - idealLogLength Z DE.2) * δ +
              inverseRadiusExponent + 2 * loss) := by
  have h :=
    let numerator := p.canonicalRightPoolOriginalNumerator hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
    let post := p.canonicalRightPoolOriginalPostIdeal hUnits μv ν b C (raw).exteriorColumns (raw).exteriorColumns
      φ ((values).coefficient centered) ((values).coefficient centered) firstFiniteTest
      hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
    let tuples := p.originalRightPoolTuples raw S χ prime n cap hcap
    s.canonicalOriginalDualCalibrationOfTuples_amplitude_bounds original numerator post tuples
      (actualDualDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
      (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
      (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
        orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
        hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
        profiles hrows ht hlowerWindow hupperWindow sTail sZero
        totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
        htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff hphysical
  simpa only [canonicalRightPoolOriginalDualCalibration, b.common_right] using h

end RightPoolBounds

end Pool

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftMainOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftMainOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightMainOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightMainOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftPoolOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftPoolOriginalDualCalibration_amplitude_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightPoolOriginalDualCalibration_metadata
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightPoolOriginalDualCalibration_amplitude_bounds
