import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalDualFactory

/-!
# Six actual dual terminal calibrations from the original moving recipe

The direct, main and valuation sources below are the literal sources of
one original first common block. Each constructor builds its numerator,
post-ideal reconstruction and complete occurrence tuple internally. The
actual moving arithmetic recipe proves the three arithmetic atom bounds.
Only original single-profile, scale, length and physical stage windows
remain as inputs. No transformed profile or completed terminal estimate
is supplied by the caller.
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

private theorem originalTerminalDivisor_ne_zero {ι : Type*}
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

/-- A transparent name for the original atoms; this makes no new choice. -/
abbrev originalTerminalAtoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t

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

/-- The actual left direct terminal, with its original coefficients and carrier. -/
def canonicalLeftOriginalDualCalibration
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      (p.leftData.directSource (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.1 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalLeftOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let post := p.canonicalLeftOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let tuples := p.originalLeftTuples raw S χ cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

/-- The actual right direct terminal, with its original coefficients and carrier. -/
def canonicalRightOriginalDualCalibration
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      (p.rightData.directSource (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.2 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalRightOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let post := p.canonicalRightOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let tuples := p.originalRightTuples raw S χ cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

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

/-- The actual left main terminal, with its original coefficients and carrier. -/
def canonicalLeftMainOriginalDualCalibration
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.1 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalLeftMainOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let post := p.canonicalLeftMainOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let tuples := p.originalLeftMainTuples raw S χ cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

/-- The actual right main terminal, with its original coefficients and carrier. -/
def canonicalRightMainOriginalDualCalibration
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z DE.2 ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalRightMainOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let post := p.canonicalRightMainOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ
  let tuples := p.originalRightMainTuples raw S χ cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

/-- The actual left pool terminal, with its original coefficients and carrier. -/
def canonicalLeftPoolOriginalDualCalibration
    (prime : ExteriorPrime A) (n : ℕ)
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.leftData S).residualSource prime n (p.leftDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z (DE.1 * (powerIdeal prime n).val) ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalLeftPoolOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
  let post := p.canonicalLeftPoolOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
  let tuples := p.originalLeftPoolTuples raw S χ prime n cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

/-- The actual right pool terminal, with its original coefficients and carrier. -/
def canonicalRightPoolOriginalDualCalibration
    (prime : ExteriorPrime A) (n : ℕ)
    (s : ActualGaussStage (E := E)
      (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
      ((p.divisorPools.rightData S).residualSource prime n (p.rightDivisorCoefficient S χ)) finiteTest)
    (hfrozen : idealLogLength Z (DE.2 * (powerIdeal prime n).val) ≤ frozenBound)
    (hmaskEmpty : s.mask = ∅)
    (hradius : s.radius.val⁻¹ ≤ Z ^ inverseRadiusExponent)
    (hcutoff : s.cutoff = Z ^ firstTailCutoffExponent
      (CanonicalOriginalTerminalPowers.tailDegree (2 * (cap + 2))
        totalBound coarseBound frozenBound radiusBound) Nsave decay) :=
  let numerator := p.canonicalRightPoolOriginalNumerator hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
  let post := p.canonicalRightPoolOriginalPostIdeal hUnits μv ν b C raw.exteriorColumns raw.exteriorColumns
    φ (values.coefficient centered) (values.coefficient centered) firstFiniteTest
    hlc hcs firstRadius firstMask δ hδ hδhalf S χ prime n
  let tuples := p.originalRightPoolTuples raw S χ prime n cap hcap
  s.canonicalOriginalDualCalibrationOfTuples original numerator post tuples
    (originalTerminalDivisor_ne_zero p.rightData.columns p.rightData.ideal S) hδ.le hδhalf
    (Q.arithmeticAtoms_left_norm_le_one ξ) (Q.arithmeticAtoms_right_norm_le_one ξ)
    (Q.arithmeticAtoms_prime_norm_le_one ξ) cap hcap
      orders B lo hi loss leftExponent rightExponent hB hlo hloOne hhi
      hlowerThreshold hupperThreshold domain hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
      profiles hrows ht hlowerWindow hupperWindow sTail sZero
      totalBound coarseBound frozenBound radiusBound Nsave decay inverseRadiusExponent
      htotal hcoarseNonneg hcoarse hfrozen hloss hinverse hmaskEmpty hradius hcutoff

end Pool

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftOriginalDualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightOriginalDualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftMainOriginalDualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightMainOriginalDualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalLeftPoolOriginalDualCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.canonicalRightPoolOriginalDualCalibration
