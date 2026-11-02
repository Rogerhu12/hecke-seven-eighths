import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChoiceBox
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualAnnularVolume
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalNormReduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidOrdinaryTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalRightTerminal

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual finite exceptional-volume choices

The catalogue contains all three original plain backgrounds and the
unchanged finite detector characters. Its error seminorms come from
the already proved supported ideal-volume theorem. The two centered
and the ordinary terminal order sets are then selected by the merged
terminal theorems, before a moving node or a Fourier frequency exists.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.VolumeChoices

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineStep
open HeckeSkeleton.Moments.MOM_PRIME
open CanonicalPrimitiveEngineChoices
open scoped Classical BigOperators SchwartzMap

variable {K : Type} [Field K] [NumberField K]

abbrev Catalogue (c : TargetContext K) :=
  Option Bool × (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))

local instance catalogueFintype (c : TargetContext K) : Fintype (Catalogue c) := by
  unfold Catalogue
  infer_instance

def background (ψ : HeckeCharacter K) : Option Bool → HeckeCharacter K
  | none => 1
  | some false => ψ
  | some true => ψ⁻¹

def character (c : TargetContext K) (i : Catalogue c) : HeckeCharacter K :=
  background (targetCharacter K c) i.1 * i.2.val

theorem character_normReduced (c : TargetContext K) (i : Catalogue c) :
    ExceptionalNormReduced K (character c i) := by
  apply exceptionalNormReduced_of_radial_zero K (normNormalizationPlace K)
  apply radial_zero_mul_finiteOrder K (normNormalizationPlace K)
  · rcases i with ⟨side, θ⟩
    cases side with
    | none => simp [background]
    | some side =>
      cases side with
      | false => exact targetCharacter_radial_zero K c
      | true =>
        simpa only [background, heckeRadialParameter_inv, neg_zero] using
          congrArg Neg.neg (targetCharacter_radial_zero K c)
  · exact Expansion.Project.canonicalDetectorTheta_finiteOrder
      K (targetCharacter K c) i.2.val i.2.property

variable (c : TargetContext K) (b : Box)

private def annularExistence (i : Catalogue c) :=
  exists_actualAnnularVolumeSeminorm (isComplex_of_family K c)
    (character c i) (character_normReduced c i)
    b.lo b.hi b.lo_pos (b.lo_le_one.trans b.hi_ge_one)

def density (i : Catalogue c) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  actualAnnularDensity (character c i) φ

def remainder (i : Catalogue c) : Seminorm ℂ (𝓢(ℝ, ℂ)) :=
  (annularExistence c b i).choose

theorem remainder_continuous (i : Catalogue c) : Continuous (remainder c b i) :=
  (annularExistence c b i).choose_spec.1

theorem volume (i : Catalogue c) (φ : 𝓢(ℝ, ℂ)) (X : ℝ)
    (hX : 0 < X) (hsupport : tsupport φ ⊆ Icc b.lo b.hi) :
    ‖(∑' I : Ideal (𝓞 K), CanonicalExceptionalVolume.coefficient (character c i) I *
        φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density c i φ‖ ≤
      remainder c b i φ :=
  (annularExistence c b i).choose_spec.2 φ hsupport X hX

theorem positive : Icc b.lo b.hi ⊆ Ioi 0 :=
  fun _ hx => b.lo_pos.trans_le hx.1

private def leftExistence :=
  CanonicalExceptionalTerminal.exists_original_magnitude_terminal_with_cutoff.{0, 0, 0, 0, 0}
    (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
    (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS) (V := EngineParameter)
    (character c) (density c) (remainder c b) (remainder_continuous c b)
    (Icc b.lo b.hi) (volume c b) isCompact_Icc (positive b)
    b.volumeLoss b.maskExponent b.volumeLoss_pos b.maskExponent_nonneg

private def rightExistence :=
  CanonicalExceptionalTerminal.exists_original_magnitude_terminal_with_right_cutoff.{0, 0, 0, 0, 0}
    (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
    (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS) (V := EngineParameter)
    (character c) (density c) (remainder c b) (remainder_continuous c b)
    (Icc b.lo b.hi) (volume c b) isCompact_Icc (positive b)
    b.volumeLoss b.maskExponent b.volumeLoss_pos b.maskExponent_nonneg

private def ordinaryExistence :=
  CanonicalExceptionalTerminal.exists_original_ordinary_magnitude_terminal_with_cutoff.{0, 0, 0, 0, 0}
    (A := (axiomChoice K c).A) (σ := complexEmbedding K c)
    (η := (axiomChoice K c).η) (hS := (axiomChoice K c).hS) (V := EngineParameter)
    (character c) (density c) (remainder c b) (remainder_continuous c b)
    (Icc b.lo b.hi) (volume c b) isCompact_Icc (positive b)

def leftOrders : Finset (ℕ × ℕ) := (leftExistence c b).choose
def rightOrders : Finset (ℕ × ℕ) := (rightExistence c b).choose
def ordinaryOrders : Finset (ℕ × ℕ) := (ordinaryExistence c b).choose
def leftOrder : ℕ := (leftExistence c b).choose_spec.2.choose
def rightOrder : ℕ := (rightExistence c b).choose_spec.2.choose
def leftConstant : ℝ := (leftExistence c b).choose_spec.2.choose_spec.choose
def rightConstant : ℝ := (rightExistence c b).choose_spec.2.choose_spec.choose
def ordinaryConstant : ℝ := (ordinaryExistence c b).choose_spec.2.choose

def orders : Finset (ℕ × ℕ) := (leftOrders c b ∪ rightOrders c b) ∪ ordinaryOrders c b
def heightOrder : ℕ := max (leftOrder c b) (rightOrder c b)
def constant : ℝ := leftConstant c b + rightConstant c b + ordinaryConstant c b

theorem leftConstant_pos : 0 < leftConstant c b :=
  (leftExistence c b).choose_spec.2.choose_spec.choose_spec.1
theorem rightConstant_pos : 0 < rightConstant c b :=
  (rightExistence c b).choose_spec.2.choose_spec.choose_spec.1
theorem ordinaryConstant_pos : 0 < ordinaryConstant c b :=
  (ordinaryExistence c b).choose_spec.2.choose_spec.1
theorem constant_pos : 0 < constant c b :=
  add_pos (add_pos (leftConstant_pos c b) (rightConstant_pos c b))
    (ordinaryConstant_pos c b)

theorem orders_zero : (0, 0) ∈ orders c b :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (leftExistence c b).choose_spec.1)

/-- These are the actual proved terminal estimates underlying the
three numerical choices, retained without changing their hypotheses. -/
def leftEstimate := (leftExistence c b).choose_spec.2.choose_spec.choose_spec.2
def rightEstimate := (rightExistence c b).choose_spec.2.choose_spec.choose_spec.2
def ordinaryEstimate := (ordinaryExistence c b).choose_spec.2.choose_spec.2

end HeckeSkeleton.Moments.EngineStepV2.VolumeChoices
