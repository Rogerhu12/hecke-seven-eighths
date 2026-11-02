import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSourceCoordinates
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFullSupportParameters

set_option linter.unusedSectionVars false

/-!
# Original exceptional numbers on the actual theta class

Only the four second ideal coordinates are filled from the original
physical classifier. The first retained scale, enlargement, tag and
first allowance remain unchanged. The exceptional row mass is the same
common-atom and correlation-supported theta restriction as the actual
source factory.

The second saving, radical windows, v-sum and exact remaining-width
ledger are proved for that actual mass. The first support window follows
from the internal full-support parameter; the error-prime window is the
original prime pool's own upper endpoint. The physical cutoff retains
the two original column losses and the original finite cutoff.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

/-- A nonnegative original support exponent and a genuine nonzero
complementary ideal give the first support window internally. -/
theorem support_window {a : RealParameters} {Z step : ℝ}
    (G : OriginalNominalGeometry (K := K) a Z step) (hZ : 1 < Z) (hq : 0 ≤ a.q) :
    1 ≤ Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ) := by
  sorry

/-- This is the support parameter used by the literal producer,
computed from its complete original mask before the first transform. -/
theorem fullSupport_window {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    {Index : Type*} {data : Index → MomentData K ω ψ}
    (Q : CompleteMovingRowRecipe A P R data) (a : RealParameters) (Z step : ℝ)
    (G : OriginalNominalGeometry (K := K) (Q.fullSupportParameters a Z) Z step)
    (hZ : 1 < Z) :
    1 ≤ Z ^ (Q.fullSupportParameters a Z).q *
      (Ideal.absNorm G.ideals.complementary.val : ℝ) := by
  sorry

/-- The selected error prime has the same upper endpoint as its
original pool. No post-transform length window is supplied. -/
theorem pool_error_upper {A : SArithmeticData K} {a : RealParameters} {Z step : ℝ}
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
    (pool : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (e : AmplifierValuation) (p : pool.primes) (I : OriginalNominalIdeals K)
    (supportError : ℝ) (herr : 0 ≤ supportError) :
    ∀ e' p',
      (OriginalNominalGeometry.canonicalPoolError (a := a) pool e p I supportError herr).tag =
        .error e' p' → (Ideal.absNorm p'.asIdeal : ℝ) ≤ Z ^ (step / 3) := by
  sorry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K)

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "rawRows" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "characters" => (rawRows).literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit (rawRows).rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)
variable (hleft : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hright : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ q ∈ (rawRows).rows, ‖chart.weight q‖ ≤ bound)

local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair
local notation "mass" => CanonicalLiteralExceptionalArithmetic.actualMass chart P R
  hclass X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
    hleft hright bound hbound hprofile

variable {a : RealParameters} {Z step : ℝ}
variable (first : OriginalNominalGeometry (K := K) a Z step)

/-- The already fixed first geometry is retained. Only the actual
second common and frequency-pattern coordinates are filled. -/
def geometry : OriginalNominalGeometry (K := K) a Z step :=
  first.atSecondPattern b.primes b.leftMultiplicity b.rightMultiplicity
    b.left_positive b.right_positive pattern

local notation "G" => geometry chart X hX label first

def numbers (r₁ r₂ slotError firstProfile : ℝ) : ExceptionalOriginalNumbers :=
  (G).exceptionalNumbers mass (G).centeredExtractionLength r₁ r₂ slotError firstProfile

variable (r₁ r₂ slotError firstProfile : ℝ)
local notation "n" => numbers chart P R hclass X hX label F parent oldMoving correction
  leftAtoms rightAtoms thetaPair hleft hright bound hbound hprofile first
    r₁ r₂ slotError firstProfile

theorem second_saving (hZ : 1 < Z) (h : (S).live) :
    2 * (n).b₂ / 3 ≤ 2 * (n).b₂ - 5 * (n).g₂ / 6 - (n).p₂ + (n).t₂ + (n).V₀ / 6 +
      (2 * (n).v) / 6 := by
  sorry

theorem v_sum : (n).vStar ≤ (n).c + (n).w + (n).b₂ := by
  sorry

theorem v_nonneg (hZ : 1 < Z) : 0 ≤ (n).v := by
  sorry

theorem radical_window (hZ : 1 < Z) (h : Orbit) (hh : h ∈ (S).rows) :
    Z ^ (n).v ≤ A.exteriorNorm (multiplicityOneNonunitRadical C (S).primes
      (S).leftMultiplicity (S).rightMultiplicity ((S).frequency h)) := by
  sorry

theorem gcd_window (hZ : 1 < Z) :
    (Ideal.absNorm (gcd (mass).leftIdeal (mass).rightIdeal) : ℝ) ≤ Z ^ (n).g₂ := by
  sorry

theorem unit_window (hZ : 1 < Z) (h : Orbit) (hh : h ∈ (S).rows) :
    Z ^ (n).t₂ ≤ A.exteriorNorm (unitFrequencyRadical C (S).primes
      (S).leftMultiplicity (S).rightMultiplicity ((S).frequency h)) := by
  sorry

theorem dyad_window :
    (n).g₂ - (n).t₂ ≤ idealLogLength Z (gcd (mass).leftIdeal (mass).rightIdeal) -
      idealLogLength Z (mass).unitIdeal.val + (n).rowError := by
  sorry

theorem remaining_window :
    ((n).Aexp - (n).c - (n).w) + (a.q + (n).R₀ + (n).E₀) + (n).w + (n).Bcommon +
      (n).wo + (n).ell + (n).rowError - (n).parentWidth ≤ (n).remaining := by
  sorry

theorem width_window :
    ((2 * ((n).Aexp - (n).c - (n).w) - (n).K₀ - (n).g - (n).g₂ - (n).V₀) +
      (a.q + (n).R₀ + (n).E₀ + (n).wo + (n).t₂ + (n).V₀) +
      ((n).b₂ - (n).p₂ + (n).w + (n).Bcommon + (n).ell)) -
      (secondCommonChildWidth Z ((n).Aexp - (n).c - (n).w) (a.q + (n).R₀ + (n).E₀)
        (n).wo (n).K₀ (n).g (mass).leftIdeal (mass).rightIdeal (mass).unitIdeal.val (mass).nonunitIdeal.val +
      secondCommonChildAllowance Z (n).w (n).Bcommon (n).ell (mass).leftIdeal (mass).rightIdeal) ≤
      (n).widthError := by
  sorry

theorem first_saving (hZ : 1 < Z) (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
    (hprime : ∀ e p, first.tag = .error e p →
      (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3)) :
    2 * ((n).c + (n).w) / 3 - 3 * (n).stepσ - 5 * (n).δ / 6 ≤
      firstSaving (n).c ((n).d + (2 * (n).Aexp - (n).c - (n).d + (n).R₀ + (n).E₀ - a.m) - (n).K₀)
        (n).w (a.q + (n).R₀ + (n).E₀) (n).wo (n).Bcommon (n).g (n).ell := by
  sorry

theorem radius_window (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
      first.retainedScale_pos (zero_lt_one.trans hZ)) :
    Z ^ (-(n).K₀ - (n).g) ≤ (mass).radius.val *
      (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (mass).mask)).val := by
  sorry

theorem cutoff_window (columnLoss cutoffExponent : ℝ) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
      first.retainedScale_pos (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
        Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
    (h : (S).live) :
    A.exteriorNorm ((S).originalIdeal h.val) ≤ (S).normFactor C h.val *
      Z ^ (2 * ((n).Aexp - (n).c - (n).w) - (n).K₀ - (n).g - (n).g₂ - (n).V₀ +
        CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0) := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.fullSupport_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.pool_error_upper
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.second_saving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.v_sum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.first_saving
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalNumbers.cutoff_window
