import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalRowLocalization
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput

/-!
# Actual complete sources with the producer's full allowed-row budget

The source arithmetic calibration controls the actual paired rows of a
parent. Localizing to exactly those rows supplies the full allowed-row
budget used by the canonical primitive engine. The moving factors,
remaining ideal, common mask and all profile representatives stay fixed.

The final transport returns a canonical engine conclusion to the original
parent. It preserves the actual children, Fourier kernels, four terminal
terms and every numerical constant; the parent energy identity was proved
before any estimate or recursive call was introduced.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The two original row-independent plain functions survive the exact
finite-row restriction, with the same values at every time and norm. -/
def localizedNormProfileRecipe {Index : Type*}
    {data : Index → MomentData K ω ψ} (W : EngineStep.NormProfileRecipe data)
    (a : RealParameters) (U : ℝ) :
    EngineStep.NormProfileRecipe (fun ξ => localizeOriginalParent (data ξ) a U) where
  left := W.left
  right := W.right
  left_eq ξ u hu := W.left_eq ξ u hu.1
  right_eq ξ u hu := W.right_eq ξ u hu.1

/-- All four literal Schwartz representatives are reused. No new
profile bound is requested after localizing the allowed rows. -/
def localizedRawProfileWindow
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {amplitude : ℝ}
    (profiles : EngineStep.RawProfileWindow rowDomain heightDomain window orders d amplitude)
    (a : RealParameters) (U : ℝ) :
    EngineStep.RawProfileWindow rowDomain heightDomain window orders
      (localizeOriginalParent d a U) amplitude where
  inverseRep := profiles.inverseRep
  leftRep := profiles.leftRep
  rightRep := profiles.rightRep
  primeRep := profiles.primeRep
  inverse_eq := profiles.inverse_eq
  left_eq := profiles.left_eq
  right_eq := profiles.right_eq
  prime_eq := profiles.prime_eq
  inverse_support := profiles.inverse_support
  left_support := profiles.left_support
  right_support := profiles.right_support
  prime_support := profiles.prime_support
  inverse_bound := profiles.inverse_bound
  left_bound := profiles.left_bound
  right_bound := profiles.right_bound
  prime_bound := profiles.prime_bound

namespace CompleteSourceData

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)}
variable {d : MomentData K c.family.omega (targetCharacter K c)}

/-- The canonical factors and fixed remaining ideal are retained by
the existing literal dictionary transport. -/
def localized (D : CompleteSourceData c theta d) (a : RealParameters) (U : ℝ) :
    CompleteSourceData c theta (localizeOriginalParent d a U) :=
  D.transport _ (fun _ hu => hu.1) rfl rfl rfl D.slot_characters
    { inverse := D.timeIndependent.inverse
      plain₁ := D.timeIndependent.plain₁
      plain₂ := D.timeIndependent.plain₂
      prime := D.timeIndependent.prime }

/-- A budget on the original finite moment becomes the exact full
allowed-row premise of the owner's complete moving-row engine. -/
theorem localized_fullJointBudget (D : CompleteSourceData c theta d)
    (a : RealParameters) (U : ℝ)
    (hbudget : ∀ u ∈ pairedRows d a U,
      idealNorm K u * idealNorm K (D.recipe.moving.fullMaskSupport D.recipe.remaining) ≤
        U ^ (a.m + a.q)) :
    (D.localized a U).recipe.FullJointBudget U (a.m + a.q) := by
  intro ξ u hu
  exact hbudget u hu.2

/-- The displayed moving support and its q-budget are literally
unchanged. Localizing rows neither adds nor removes a moving factor. -/
theorem localized_supportBudget (D : CompleteSourceData c theta d)
    (a : RealParameters) (U : ℝ) (hbudget : D.recipe.SupportBudget U a.q) :
    (D.localized a U).recipe.SupportBudget U a.q := hbudget

end CompleteSourceData

/-- All hypotheses of the strict domain depend only on the actual
parameters and slot geometry, which this localization preserves. -/
def localizeOriginalParent_domain
    {d : MomentData K ω ψ} {a : RealParameters} {centered : Bool}
    {U Y₁ Y₂ floor padding : ℝ}
    (domain : EngineStep.PairedEngineDomain centered d a U Y₁ Y₂ floor padding) :
    EngineStep.PairedEngineDomain centered (localizeOriginalParent d a U)
      a U Y₁ Y₂ floor padding :=
  { domain with total_length := domain.total_length }

/-- Apply the canonical single-step conclusion to the original parent
using the previously proved complete-energy equality. This is a genuine
transport of one output, retaining its actual children and measure. -/
def engineOutput_of_localizedOriginalParent {Ω : Type*} [MeasurableSpace Ω]
    {d : MomentData K ω ψ} {a : RealParameters} {centered : Bool}
    {U t Y₁ Y₂ sigma delta beta C control : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (out : EngineStep.PairedEngineConclusion (Ω := Ω) centered
      (localizeOriginalParent d a U) a U t Y₁ Y₂ sigma delta beta C control admissible) :
    EngineStep.PairedEngineConclusion (Ω := Ω) centered
      d a U t Y₁ Y₂ sigma delta beta C control admissible :=
  { out with
    parent := by
      simpa only [localizeOriginalParent_pairedStageEnergy] using out.parent }

end HeckeSkeleton.Moments.EngineInduction
