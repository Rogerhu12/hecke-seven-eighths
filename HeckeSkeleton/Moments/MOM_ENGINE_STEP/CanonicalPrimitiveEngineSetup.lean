import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveFirstTerminalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveSecondTerminalUniform
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineMassChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineProfileOrders
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEnginePool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalUnifiedChoice
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPhysicalBox
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeAnalyticProvider

/-!
# Original choices for the uniform primitive engine

Only the fixed arithmetic, character catalogue, original one-character
volume input and original analytic provider enter these choices. The
finite profile orders and analytic height constant are chosen before
the scale, original source, allocation or child family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineSetup

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open CanonicalOriginalParentFactory CanonicalPrimitiveEngineChoices
open HeckeGeneral.Bridge HeckePort.Moments

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
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

variable {ω ψ : HeckeCharacter K}
variable (b : Box) (theta : Finset (HeckeCharacter K))
variable (outputOrders : Finset (ℕ × ℕ))
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  ψ theta (Set.Icc b.lo b.hi))

/-- The original first deletion retains the passive sixth-power prime
factors. Its exceptional volume box therefore also covers the actual
column bound and the two pool-prime lengths. The choice precedes the
source and does not alter its mask or arithmetic data. -/
def volumeWidth (b : Box) : ℝ :=
  max b.widthMax (b.columnBound + 2 * b.step / 3)

theorem volumeWidth_nonneg (b : Box) : 0 ≤ volumeWidth b :=
  b.width_nonneg.trans (le_max_left _ _)

theorem widthMax_le_volumeWidth (b : Box) : b.widthMax ≤ volumeWidth b :=
  le_max_left _ _

theorem firstSupport_le_volumeWidth (b : Box) :
    b.columnBound + 2 * b.step / 3 ≤ volumeWidth b :=
  le_max_right _ _

/-- The complete mask pays both original column contributions, with
the same physical loss and cutoff exponent used by the actual source. -/
def volumeMaskExponent (b : Box) : ℝ :=
  2 * volumeWidth b + 2 * b.loss + b.loss + 1

theorem volumeMaskExponent_nonneg (b : Box) : 0 ≤ volumeMaskExponent b := by
  have hwidth := volumeWidth_nonneg b
  have hloss := b.loss_pos.le
  unfold volumeMaskExponent
  positivity

/-- One finite order set for the two centered sides and the ordinary side. -/
def volumeOrders : Finset (ℕ × ℕ) :=
  CanonicalLiteralExceptionalUnifiedChoice.orders
    (A := A) (σ := σ) (η := η) (hS := hS) primitive
    (b.ε / 64) (volumeMaskExponent b)
    (div_pos b.ε_pos (by norm_num)) (volumeMaskExponent_nonneg b)

def orders : Finset (ℕ × ℕ) :=
  CanonicalPrimitiveEngineProfileOrders.orders outputOrders
    (volumeOrders (A := A) (σ := σ) (η := η) (hS := hS) b theta primitive)

/-- The single original finite window supplies all later restrictions. -/
def originalOrders : Finset (ℕ × ℕ) :=
  CanonicalPrimitiveEngineProfileOrders.originalOrders outputOrders
    (volumeOrders (A := A) (σ := σ) (η := η) (hS := hS) b theta primitive)

local notation "allOrders" => orders (A := A) (σ := σ) (η := η) (hS := hS)
  b theta outputOrders primitive

theorem outputOrders_subset : outputOrders ⊆ allOrders :=
  CanonicalPrimitiveEngineProfileOrders.output_subset _ _

theorem volumeOrders_subset :
    volumeOrders (A := A) (σ := σ) (η := η) (hS := hS) b theta primitive ⊆ allOrders :=
  CanonicalPrimitiveEngineProfileOrders.volume_subset _ _

theorem primeOrders_subset : CanonicalFullKappaPrime.orders ⊆ allOrders :=
  CanonicalPrimitiveEngineProfileOrders.prime_subset _ _

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (provider : CanonicalOriginalPrimeAnalyticProvider.Provider
  (A := A) (P := P) (R := R) theta)

/-- Its defining analytic provider is uniform in the original full mask. -/
def heightConstant : ℝ := Classical.choose (provider b.rawNormBound b.rawNormBound_nonneg)

theorem heightConstant_pos :
    0 < heightConstant (A := A) (P := P) (R := R) b theta provider :=
  (Classical.choose_spec (provider b.rawNormBound b.rawNormBound_nonneg)).1

/-- This is the raw single-character window itself, before any source. -/
theorem primeWindow : CanonicalOriginalPrimeAnalyticProvider.Window
    (A := A) (P := P) (R := R) theta b.rawNormBound
    (heightConstant (A := A) (P := P) (R := R) b theta provider) :=
  (Classical.choose_spec (provider b.rawNormBound b.rawNormBound_nonneg)).2

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)

/-- The original first zero and tail share one pre-source choice. -/
def first : CanonicalPrimitiveFirstTerminalConstants.Fixed μv ν C hDiff b allOrders :=
  CanonicalPrimitiveFirstTerminalConstants.choose (μv := μv) (ν := ν) (μ := μ)
    (C := C) (hDiff := hDiff) (b := b) (orders := allOrders)

/-- The direct and pooled second terminals share the same pre-source choice. -/
def second : CanonicalPrimitiveSecondTerminalConstants.Fixed
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    μv hDiff C (rowBallFiniteFamily K A.Sf 1) b :=
  CanonicalPrimitiveSecondTerminalConstants.choose (ν := ν) (μ := μ)
    (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) μv hDiff
    C Drecipe hD (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1) b

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineSetup

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineSetup.primeWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineSetup.first
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineSetup.second
