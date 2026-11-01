import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

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
    0 ≤ Q.fullMaskSupportLength Z :=
  idealLogLength_nonneg Z hZ _
    (nonZeroDivisors.ne_zero (Q.moving.fullMaskSupport Q.remaining).property)

theorem rpow_fullMaskSupportLength (Z : ℝ) (hZ : 1 < Z) :
    Z ^ Q.fullMaskSupportLength Z = idealNorm K (Q.moving.fullMaskSupport Q.remaining) :=
  rpow_idealLogLength Z hZ _
    (nonZeroDivisors.ne_zero (Q.moving.fullMaskSupport Q.remaining).property)

def fullMaskParameters (a : RealParameters) (Z : ℝ) : RealParameters :=
  { a with m := a.m + a.q - Q.fullMaskSupportLength Z, q := Q.fullMaskSupportLength Z }

@[simp] theorem fullMaskParameters_width (a : RealParameters) (Z : ℝ) :
    (Q.fullMaskParameters a Z).m + (Q.fullMaskParameters a Z).q = a.m + a.q :=
  sub_add_cancel _ _

@[simp] theorem fullMaskParameters_pairedRows (ξ : X) (a : RealParameters) (Z : ℝ) :
    pairedRows (data ξ) (Q.fullMaskParameters a Z) Z = pairedRows (data ξ) a Z := by
  simp only [pairedRows, fullMaskParameters, sub_add_cancel]

@[simp] theorem fullMaskParameters_pairedEnergy
    (ξ : X) (a : RealParameters) (Z t : ℝ) :
    pairedEnergy (data ξ) (Q.fullMaskParameters a Z) Z t =
      pairedEnergy (data ξ) a Z t := by
  simp only [pairedEnergy, pairedRows, fullMaskParameters, sub_add_cancel]

@[simp] theorem fullMaskParameters_pairedStageEnergy
    (centered : Bool) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered (data ξ) (Q.fullMaskParameters a Z) Z t Y₁ Y₂ =
      pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ := by
  simp only [pairedStageEnergy, pairedRows, fullMaskParameters, sub_add_cancel]

theorem fullMaskParameters_domain
    (centered : Bool) (ξ : X) (a : RealParameters) (Z Y₁ Y₂ floor padding : ℝ)
    (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered (data ξ) (Q.fullMaskParameters a Z)
      Z Y₁ Y₂ floor padding where
  scale := domain.scale
  width_floor := by simpa only [Q.fullMaskParameters_width] using domain.width_floor
  width_nonneg := by simpa only [Q.fullMaskParameters_width] using domain.width_nonneg
  plain_left_nonneg := domain.plain_left_nonneg
  plain_right_nonneg := domain.plain_right_nonneg
  total_length := domain.total_length
  kappa_lower := domain.kappa_lower
  kappa_upper := domain.kappa_upper
  capacity := by simpa only [fullMaskParameters, sub_add_cancel] using domain.capacity
  padded_core := by simpa only [fullMaskParameters, sub_add_cancel] using domain.padded_core
  ordinary hc := by
    simpa only [fullMaskParameters, sub_add_cancel] using domain.ordinary hc
  centered_left hc := by
    simpa only [fullMaskParameters, sub_add_cancel] using domain.centered_left hc
  centered_right hc := by
    simpa only [fullMaskParameters, sub_add_cancel] using domain.centered_right hc
  comparison_left hc := by
    simpa only [fullMaskParameters, sub_add_cancel] using domain.comparison_left hc
  comparison_right hc := by
    simpa only [fullMaskParameters, sub_add_cancel] using domain.comparison_right hc

/-- Every actual displayed prime is still budgeted. No character is
added to the moving list and no remaining phase is discarded. -/
theorem fullMaskParameters_supportBudget (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    Q.SupportBudget Z (Q.fullMaskParameters a Z).q := by
  change A.exteriorNorm Q.moving.support ≤ Z ^ Q.fullMaskSupportLength Z
  rw [Q.rpow_fullMaskSupportLength Z hZ]
  exact Q.moving.support_norm_le_fullMaskSupport Q.remaining

theorem fullMaskParameters_fullJointBudget (a : RealParameters) (Z : ℝ)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    Q.FullJointBudget Z
      ((Q.fullMaskParameters a Z).m + (Q.fullMaskParameters a Z).q) := by
  simpa only [Q.fullMaskParameters_width] using hfull

/-- One actual allowed row proves that the fixed full support fits in
the parent width. Empty parents require no such assertion. -/
theorem fullMaskSupportLength_le_width_of_allowed
    (ξ : X) (u : NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    Q.fullMaskSupportLength Z ≤ a.m + a.q := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Q.rpow_fullMaskSupportLength Z hZ]
  calc
    idealNorm K (Q.moving.fullMaskSupport Q.remaining) =
        1 * idealNorm K (Q.moving.fullMaskSupport Q.remaining) := (one_mul _).symm
    _ ≤ idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining) :=
      mul_le_mul_of_nonneg_right (one_le_idealNorm K u) (idealNorm_pos K _).le
    _ ≤ _ := hfull ξ u hu

theorem fullMaskParameters_nonneg_of_allowed
    (ξ : X) (u : NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    0 ≤ (Q.fullMaskParameters a Z).m ∧ 0 ≤ (Q.fullMaskParameters a Z).q :=
  ⟨sub_nonneg.mpr (Q.fullMaskSupportLength_le_width_of_allowed ξ u hu a Z hZ hfull),
    Q.fullMaskSupportLength_nonneg Z hZ⟩

theorem fullMaskParameters_bounds_of_pairedRow
    (ξ : X) (u : NonzeroIdeal K) (a : RealParameters) (Z : ℝ)
    (hu : u ∈ pairedRows (data ξ) a Z) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    0 ≤ (Q.fullMaskParameters a Z).m ∧
      (Q.fullMaskParameters a Z).m ≤ a.m + a.q ∧
      0 ≤ (Q.fullMaskParameters a Z).q ∧
      (Q.fullMaskParameters a Z).q ≤ a.m + a.q := by
  have hallowed := (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hr := Q.fullMaskSupportLength_nonneg Z hZ
  have hwidth := Q.fullMaskSupportLength_le_width_of_allowed ξ u hallowed a Z hZ hfull
  change 0 ≤ a.m + a.q - Q.fullMaskSupportLength Z ∧
    a.m + a.q - Q.fullMaskSupportLength Z ≤ a.m + a.q ∧
    0 ≤ Q.fullMaskSupportLength Z ∧ Q.fullMaskSupportLength Z ≤ a.m + a.q
  exact ⟨sub_nonneg.mpr hwidth, sub_le_self _ hr, hr, hwidth⟩

/-- If the original full deletion support exceeds the available width,
the actual parent has no rows. This branch needs no row-ball estimate. -/
theorem pairedRows_eq_empty_of_fullSupportLength_gt
    (ξ : X) (a : RealParameters) (Z : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hlarge : a.m + a.q < Q.fullMaskSupportLength Z) :
    pairedRows (data ξ) a Z = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro u hu
  have hallowed := (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  exact (not_le_of_gt hlarge)
    (Q.fullMaskSupportLength_le_width_of_allowed ξ u hallowed a Z hZ hfull)

theorem pairedStageEnergy_eq_zero_of_fullSupportLength_gt
    (centered : Bool) (ξ : X) (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q))
    (hlarge : a.m + a.q < Q.fullMaskSupportLength Z) :
    pairedStageEnergy centered (data ξ) a Z t Y₁ Y₂ = 0 := by
  simp only [pairedStageEnergy,
    Q.pairedRows_eq_empty_of_fullSupportLength_gt ξ a Z hZ hfull hlarge, Finset.sum_empty]

def fullMaskRadius (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) : {r : ℝ // 0 < r} :=
  ⟨idealNorm K (Q.moving.fullMaskSupport Q.remaining) / Z ^ (a.m + a.q),
    div_pos (idealNorm_pos K _) (Real.rpow_pos_of_pos hZ _)⟩

theorem fullMaskRadius_eq_inverse (a : RealParameters) (Z : ℝ) (hZ : 1 < Z) :
    (Q.fullMaskRadius a Z (zero_lt_one.trans hZ)).val =
      (Z ^ (Q.fullMaskParameters a Z).m)⁻¹ := by
  change idealNorm K (Q.moving.fullMaskSupport Q.remaining) / Z ^ (a.m + a.q) =
    (Z ^ (a.m + a.q - Q.fullMaskSupportLength Z))⁻¹
  rw [Real.rpow_sub (zero_lt_one.trans hZ), Q.rpow_fullMaskSupportLength Z hZ, inv_div]

/-- The full-mask budget proves the actual row-ball inequality. This
is stronger than the bare row enumeration's norm window. -/
theorem fullMaskRadius_row_norm
    (ξ : X) (u : NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (a : RealParameters) (Z : ℝ) (hZ : 0 < Z)
    (hfull : Q.FullJointBudget Z (a.m + a.q)) :
    (Q.fullMaskRadius a Z hZ).val * idealNorm K u ≤ 1 := by
  change idealNorm K (Q.moving.fullMaskSupport Q.remaining) / Z ^ (a.m + a.q) *
    idealNorm K u ≤ 1
  rw [div_mul_eq_mul_div, mul_comm (idealNorm K (Q.moving.fullMaskSupport Q.remaining))]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr
  simpa only [one_mul] using hfull ξ u hu

end CompleteMovingRowRecipe

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskParameters_domain
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskParameters_pairedStageEnergy
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.fullMaskRadius_row_norm
