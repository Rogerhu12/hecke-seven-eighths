import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

set_option linter.unusedSectionVars false

/-!
# The original parent radius pays its complete fixed deletion support

The original joint budget bounds the varying row times the radical of
all displayed factors and the fixed remaining mask.  A bound for the
displayed factors alone does not bound that remaining ideal.  We use
the actual norm of this complete support to choose the first row ball.

Writing its logarithmic norm as r, the internal coordinates are M-r
and r.  Their sum is the original width M.  The original row set,
characters, masks, profiles, slot count, centered coefficient and parent
energy are identical.  This is an allocation of the norm budget; the
moving list and the fixed remaining ideal are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}

namespace CompleteMovingRowRecipe

variable (Q : CompleteMovingRowRecipe A P R data)

def fullMaskSupportLength (Z : ℝ) : ℝ :=
  idealLogLength Z (Q.moving.fullMaskSupport Q.remaining).val

theorem fullMaskSupportLength_nonneg (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Q.fullMaskSupportLength Z := by
  sorry

theorem rpow_fullMaskSupportLength (Z : ℝ) (hZ : 1 < Z) :
    Z ^ Q.fullMaskSupportLength Z = idealNorm K (Q.moving.fullMaskSupport Q.remaining) := by
  sorry

def fullMaskParameters (a : RealParameters) (Z : ℝ) : RealParameters :=
  { a with m := a.m + a.q - Q.fullMaskSupportLength Z, q := Q.fullMaskSupportLength Z }

@[simp] theorem fullMaskParameters_width (a : RealParameters) (Z : ℝ) :
    (Q.fullMaskParameters a Z).m + (Q.fullMaskParameters a Z).q = a.m + a.q := by
  sorry

@[simp] theorem fullMaskParameters_pairedRows (ξ : X) (a : RealParameters) (Z : ℝ) :
    pairedRows (data ξ) (Q.fullMaskParameters a Z) Z = pairedRows (data ξ) a Z := by
  sorry

@[simp] theorem fullMaskParameters_pairedEnergy
    (ξ : X) (a : RealParameters) (Z t : ℝ) :
    pairedEnergy (data ξ) (Q.fullMaskParameters a Z) Z t =
      pairedEnergy (data ξ) a Z t := by
  sorry

@[simp] theorem fullMaskParameters_pairedStageEnergy
    (centered : Bool) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered (data ξ) (Q.fullMaskParameters a Z) Z t Y₁ Y₂ =
      pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ := by
  sorry

theorem fullMaskParameters_domain
    (centered : Bool) (ξ : X) (a : RealParameters) (Z Y₁ Y₂ floor padding : ℝ)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered (data ξ) (Q.fullMaskParameters a Z)
      Z Y₁ Y₂ floor padding := by
  sorry

/-- Every actual displayed prime is still budgeted. No character is
added to the moving list and no remaining phase is discarded. -/
theorem fullMaskParameters_supportBudget (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    Q.SupportBudget Z (Q.fullMaskParameters a Z).q := by
  sorry

theorem fullMaskParameters_fullJointBudget (a : RealParameters) (Z : ℝ)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    Q.FullJointBudget Z
      ((Q.fullMaskParameters a Z).m + (Q.fullMaskParameters a Z).q) := by
  sorry

/-- One actual allowed row proves that the fixed full support fits in
the parent width. Empty parents require no such assertion. -/
theorem fullMaskSupportLength_le_width_of_allowed
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    Q.fullMaskSupportLength Z ≤ a.m + a.q := by
  sorry

theorem fullMaskParameters_nonneg_of_allowed
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    0 ≤ (Q.fullMaskParameters a Z).m ∧ 0 ≤ (Q.fullMaskParameters a Z).q := by
  sorry

theorem fullMaskParameters_bounds_of_pairedRow
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (a : RealParameters) (Z : ℝ)
    (hu : u ∈ pairedRows (data ξ) a Z) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    0 ≤ (Q.fullMaskParameters a Z).m ∧
      (Q.fullMaskParameters a Z).m ≤ a.m + a.q ∧
      0 ≤ (Q.fullMaskParameters a Z).q ∧
      (Q.fullMaskParameters a Z).q ≤ a.m + a.q := by
  sorry

/-- If the original full deletion support exceeds the available width,
the actual parent has no rows. This branch needs no row-ball estimate. -/
theorem pairedRows_eq_empty_of_fullSupportLength_gt
    (ξ : X) (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hlarge : a.m + a.q < Q.fullMaskSupportLength Z) :
    pairedRows (data ξ) a Z = ∅ := by
  sorry

theorem pairedStageEnergy_eq_zero_of_fullSupportLength_gt
    (centered : Bool) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hlarge : a.m + a.q < Q.fullMaskSupportLength Z) :
    pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ = 0 := by
  sorry

def fullMaskRadius (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) : {r : ℝ // 0 < r} :=
  ⟨idealNorm K (Q.moving.fullMaskSupport Q.remaining) / Z ^ (a.m + a.q),
    div_pos (idealNorm_pos K _) (Real.rpow_pos_of_pos hZ _)⟩

theorem fullMaskRadius_eq_inverse (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    (Q.fullMaskRadius a Z (zero_lt_one.trans hZ)).val =
      (Z ^ (Q.fullMaskParameters a Z).m)⁻¹ := by
  sorry

/-- The full-mask budget proves the actual row-ball inequality. This
is stronger than the bare row enumeration's norm window. -/
theorem fullMaskRadius_row_norm
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 0 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    (Q.fullMaskRadius a Z hZ).val * idealNorm K u ≤ 1 := by
  sorry

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskParameters_domain
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskParameters_pairedStageEnergy
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskRadius_row_norm
