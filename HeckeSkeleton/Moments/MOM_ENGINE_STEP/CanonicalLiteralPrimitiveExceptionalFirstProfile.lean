import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectCombinedProfile
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPoolCombinedProfile
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalGeometry

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# The actual primitive first profile in all six branches

Each estimate concerns the weight and the two original scalars of the
same first source. The scalars include the real factors removed by the
actual redistribution of the two Mellin powers. The original common
label proves nonnegativity of the internal row length; original column
norms bound the physical divisor and active radical. Thus the small
Mellin cost is uniform before any second-stage label or Fourier mode.

The original normalization retains both exact ideal lengths. Only the
remaining tilt is bounded by the fixed original length box. The fixed
coefficient is independent of the moving profile amplitude, which
appears explicitly to degree twice the original occurrence cap.
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

namespace CanonicalLiteralPrimitiveExceptionalFirstProfile

variable (K : Type) [Field K] [NumberField K]

/-- Chosen using the field, original occurrence cap and support window. -/
def firstConstant (cap : ℕ) (annulus : ℝ) : ℝ :=
  orbitalFieldFactor K * annulus ^ cap

theorem firstConstant_nonneg (cap : ℕ) {annulus : ℝ} (hannulus : 0 ≤ annulus) :
    0 ≤ firstConstant K cap annulus := by
  sorry

/-- The raw profile amplitude is paid explicitly, without entering the
fixed first-source constant. -/
theorem atom_coefficient_eq (cap : ℕ) {annulus amplitude : ℝ}
    (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude) :
    orbitalFieldFactor K *
        CanonicalLiteralFirstScalarCost.atomBudget annulus amplitude ^ cap =
      firstConstant K cap annulus * amplitude ^ (2 * cap) := by
  sorry

end CanonicalLiteralPrimitiveExceptionalFirstProfile

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

local notation "hΓ₀" => actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => (atoms).raw Y₁ Y₂
local notation "firstSource" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (lengthBound columnBound : ℝ) (hlengthBound : 0 ≤ lengthBound)
variable (htotal : a.n₁ + a.n₂ + a.z ≤ lengthBound)
variable (hN : ∀ i ∈ (firstSource).columns,
  (Ideal.absNorm ((firstSource).ideal i).val : ℝ) ≤ Z ^ columnBound)
variable (δ₂ : ℝ) (hδ₂ : 0 ≤ δ₂)

include domain hlengthBound htotal hN hδ₂ in
/-- The numeric windows used by the first-profile tilt come from the
same original common label and full columns. -/
theorem literalPrimitiveExceptionalFirstTilt_le
    (DE : (firstSource).CommonLabel)
    (D : (((firstSource).block DE).mask (firstSource).mask).powerset) :
    CanonicalFirstResidualProfileCost.tiltError (internal).m
        ((internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength)
        (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val)
        (idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2)) δ₁ δ₂ ≤
      4 * max lengthBound columnBound * (δ₁ + δ₂) := by
  sorry

variable (cap : ℕ) (annulus amplitude : ℝ)
variable (hannulus : 1 ≤ annulus) (hamplitude : 1 ≤ amplitude)

local notation "fixedFirst" =>
  CanonicalLiteralPrimitiveExceptionalFirstProfile.firstConstant K cap annulus
local notation "tilt" => 4 * max lengthBound columnBound * (δ₁ + δ₂)

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude in
/-- Only the small remainder of the exact first-profile exponent is
enlarged. The original normalization still contains its actual ideals. -/
theorem literalPrimitiveExceptionalFirstCoefficient_le
    (DE : (firstSource).CommonLabel)
    (D : (((firstSource).block DE).mask (firstSource).mask).powerset) :
    (orbitalFieldFactor K *
        CanonicalLiteralFirstScalarCost.atomBudget annulus amplitude ^ cap) *
      Z ^ (((internal).m + (internal).q) -
        ((internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength + (internal).q +
          idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val +
          idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2)) +
        CanonicalFirstResidualProfileCost.tiltError (internal).m
          ((internal).n₁ + (internal).n₂ + (data ξ).geometry.totalLength)
          (idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val)
          (idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2)) δ₁ δ₂) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude)
variable (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (hwindow : window ⊆ Set.Iic annulus)
variable (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)

section Direct

local notation "source" => firstSource
variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
local notation "p" => (source).pieces DE D
variable (S : divisorPool (p).rightData.columns (fun j => ((p).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

section LeftDirect

local notation "cover" => (p).leftSourceCover (raw).originalAtlas S χ
local notation "firstFixed" => ((source).block DE).literalLeftFixed D.val
local notation "hfirst" => ((source).block DE).literalLeftFixed_generates C D.val
local notation "firstScalar" => literalLeftDirectScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ
local notation "firstAtoms" => literalLeftDirectAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual left direct source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveLeftDirectExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end LeftDirect

section RightDirect

local notation "cover" => (p).rightSourceCover (raw).originalAtlas S χ
local notation "firstFixed" => ((source).block DE).literalRightFixed D.val
local notation "hfirst" => ((source).block DE).literalRightFixed_generates C D.val
local notation "firstScalar" => literalRightDirectScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ
local notation "firstAtoms" => literalRightDirectAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual right direct source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveRightDirectExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end RightDirect

end Direct

section Pooled

variable (loss cutoffExponent : ℝ) (hloss : 0 ≤ loss)
variable (hcutoffExponent : 0 ≤ cutoffExponent) (hcolumnBound : 0 ≤ columnBound)
variable (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (hcutoffPower : cutoff ≤ Z ^ cutoffExponent)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {step eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
variable (hdensity : 0 < pool.rowDensity
  (literalPrimitivePoolRowExponent (lengthBound := lengthBound) (columnBound := columnBound)
    (loss := loss) (cutoffExponent := cutoffExponent)) columnBound)

local notation "source" => Q.literalPrimitivePooledSource
  (μv := μv) (ν := ν) (C := C) (hroot := hroot) (hemb := hemb) (W := W) (ξ := ξ)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (hZ := hZ) (hbudget := hbudget)
  (centered := centered) (cutoff := cutoff) (hcutoff := hcutoff)
  (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half)
  (cap := cap) (annulus := annulus) (loss := loss) (cutoffExponent := cutoffExponent)
  (hannulus := hannulus) (hcap := hcap) (hannulusZ := hannulusZ) (domain := domain)
  (profiles := profiles) (hrows := hrows) (ht := ht) (hwindow := hwindow)
  (hcutoffPower := hcutoffPower) (reference := reference) (href := href)
  (lengthBound := lengthBound) (columnBound := columnBound)
  (hlengthBound := hlengthBound) (hcolumnBound := hcolumnBound)
  (htotal := htotal) (hN := hN) (hloss := hloss) (hcutoffExponent := hcutoffExponent)
  (pool := pool) (hdensity := hdensity)

variable (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset)
local notation "p" => (source).pools DE D
variable (S : divisorPool (p).rightData.columns (fun j => ((p).rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)

section LeftMain

local notation "cover" => ((p).leftSourceCovers (raw).originalAtlas S χ).main
local notation "firstFixed" => ((source).block DE).literalLeftFixed D.val
local notation "hfirst" => ((source).block DE).literalLeftFixed_generates C D.val
local notation "firstScalar" => literalLeftMainScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ
local notation "firstAtoms" => literalLeftMainAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual left main source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveLeftMainExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end LeftMain

section RightMain

local notation "cover" => ((p).rightSourceCovers (raw).originalAtlas S χ).main
local notation "firstFixed" => ((source).block DE).literalRightFixed D.val
local notation "hfirst" => ((source).block DE).literalRightFixed_generates C D.val
local notation "firstScalar" => literalRightMainScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ
local notation "firstAtoms" => literalRightMainAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual right main source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveRightMainExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end RightMain

section LeftPool

variable (prime : pool.primes) (n : ℕ)
local notation "cover" => ((p).leftSourceCovers (raw).originalAtlas S χ).residual prime n
local notation "firstFixed" => ((source).block DE).literalLeftFixed D.val
local notation "hfirst" => ((source).block DE).literalLeftFixed_generates C D.val
local notation "firstScalar" => literalLeftPoolScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ prime n
local notation "firstAtoms" => literalLeftPoolAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂ prime n

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual left pool source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveLeftPoolExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end LeftPool

section RightPool

variable (prime : pool.primes) (n : ℕ)
local notation "cover" => ((p).rightSourceCovers (raw).originalAtlas S χ).residual prime n
local notation "firstFixed" => ((source).block DE).literalRightFixed D.val
local notation "hfirst" => ((source).block DE).literalRightFixed_generates C D.val
local notation "firstScalar" => literalRightPoolScalar
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ prime n
local notation "firstAtoms" => literalRightPoolAtoms
    hΓ₀ μv ν Q ξ (W.at ξ) internal Z t Y₁ Y₂ centered hZ hY₁ hY₂
    ((source).block DE) C (CanonicalRowBall.archTest K A.Sf 1)
    (rowBallFiniteFamily K A.Sf 1) (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) (source).radius D.val δ₁ hδ₁ hδ₁half
    p S χ firstFixed hfirst δ₂ prime n

include domain hlengthBound htotal hN hδ₂ hannulus hamplitude profiles hzero ht hprime
  hwindow hcap hδsum in
/-- The actual right pool source pays its two original
redistributed scalars, at the original normalization and uniform tilt. -/
theorem literalPrimitiveRightPoolExceptional_firstProfile_le
    (labelL labelR : (cover).labels) :
    (p).weightBound *
        (‖firstScalar labelL * ((firstAtoms labelL).normProfileFactor δ₁ δ₂ : ℂ)‖ *
          ‖firstScalar labelR * ((firstAtoms labelR).normProfileFactor δ₁ δ₂ : ℂ)‖) ≤
      (fixedFirst * amplitude ^ (2 * cap)) *
        Z ^ ((a.m + a.q) - firstTotal DE D + tilt) := by
  sorry

end RightPool

end Pooled
end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveExceptionalFirstProfile.atom_coefficient_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveExceptionalFirstTilt_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftDirectExceptional_firstProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightDirectExceptional_firstProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftMainExceptional_firstProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightMainExceptional_firstProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveLeftPoolExceptional_firstProfile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveRightPoolExceptional_firstProfile_le

