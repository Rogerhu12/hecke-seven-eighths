import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthRootSupportBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DerivedCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry

/-!
# The complete sixth-root deletion in the original length ledger

The support mask contains the complete second sixth-root ideal.  Its
literal logarithmic length is added to the child width and subtracted
from the second allowance.  Their sum, and therefore the original
second scalar cancellation, is unchanged.

The actual ideal divisibilities from `SixthRootSupportBudget` prove
that this larger width retains the prescribed descent and that the
smaller allowance still pays `w + ell`.  The capacity defect can only
decrease when this nonnegative support length is added.

The old `ScaleWindows` record is retained literally.  Separate theorems
derive the enlarged support scale and its width errors from that
record; no enlarged support parameter is asserted to satisfy the old
record's unmodified scale identity.  Cutoff and dyadic errors remain
explicit.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

/-- The original width with the full sixth-root support added. -/
def secondSixthDeletionChildWidth (Z a₀ q wo krow g : ℝ)
    (D E T V root : Ideal (𝓞 K)) : ℝ :=
  secondCommonChildWidth Z a₀ q wo krow g D E T V + idealLogLength Z root

/-- The same full root is paid from the original second allowance. -/
def secondSixthDeletionChildAllowance (Z w B ell : ℝ)
    (D E root : Ideal (𝓞 K)) : ℝ :=
  secondCommonChildAllowance Z w B ell D E - idealLogLength Z root

theorem secondSixthDeletion_total (Z a₀ q wo w B krow g ell : ℝ)
    (D E T V root : Ideal (𝓞 K)) :
    secondSixthDeletionChildWidth Z a₀ q wo krow g D E T V root +
        secondSixthDeletionChildAllowance Z w B ell D E root =
      secondCommonChildWidth Z a₀ q wo krow g D E T V +
        secondCommonChildAllowance Z w B ell D E := by
  unfold secondSixthDeletionChildWidth secondSixthDeletionChildAllowance
  ring

/-- The pool density, original Poisson factor, original correlation
norm and both central factors are identical to the original scalar
identity.  Only the allocation between width and allowance changes. -/
theorem second_sixthDeletion_actual_scalar_budget_identity
    (Z : ℝ) (hZ : 1 < Z) (F a₀ q wo w B krow g ell : ℝ)
    (D E T V root : Ideal (𝓞 K)) (hD : D ≠ 0) (hE : E ≠ 0) (hT : T ≠ 0) :
    Z ^ (-ell) * (F * Z ^ (krow + g - a₀)) *
        ((Ideal.absNorm (gcd D E) : ℝ) / (Ideal.absNorm T : ℝ)) /
        (Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ)) *
        Z ^ (secondSixthDeletionChildWidth Z a₀ q wo krow g D E T V root +
          secondSixthDeletionChildAllowance Z w B ell D E root) =
      F * Z ^ (a₀ + q + wo + w + B) /
        (Ideal.absNorm (commonRadical D E) : ℝ) := by
  rw [secondSixthDeletion_total]
  exact second_actual_scalar_budget_identity Z hZ F a₀ q wo w B krow g ell
    D E T V hD hE hT

namespace NominalChildGeometry

/-- Bookkeeping for the additional support factor.  The original
geometry, including its actual unit-radical coordinate, is not changed. -/
def sixthDeletionWidth (s : NominalChildGeometry) (rootLength : ℝ) : ℝ :=
  s.nominalWidth + rootLength

theorem sixthDeletionWidth_identity (s : NominalChildGeometry) (rootLength : ℝ) :
    s.sixthDeletionWidth rootLength =
      s.parentWidth + s.enlargementJ - s.g - s.g₂ + s.t₂ + rootLength := by
  rw [sixthDeletionWidth, s.width_identity]

theorem sixthDeletion_width_drop (s : NominalChildGeometry) (rootLength step : ℝ)
    (henlarge : s.enlargementJ + step ≤ s.g)
    (hunit : s.t₂ + rootLength ≤ s.g₂) :
    s.sixthDeletionWidth rootLength ≤ s.parentWidth - step := by
  have hid := s.sixthDeletionWidth_identity rootLength
  linarith

theorem sixthDeletion_width_drop_with_errors (s : NominalChildGeometry)
    (rootLength step cutoff error actualWidth : ℝ)
    (henlarge : s.enlargementJ + step ≤ s.g)
    (hunit : s.t₂ + rootLength ≤ s.g₂)
    (hactual : actualWidth ≤ s.sixthDeletionWidth rootLength + cutoff + error) :
    actualWidth ≤ s.parentWidth - step + cutoff + error := by
  have hnom := s.sixthDeletion_width_drop rootLength step henlarge hunit
  linarith

theorem sixthDeletion_width_drop_half (s : NominalChildGeometry)
    (rootLength step cutoff error actualWidth : ℝ)
    (henlarge : s.enlargementJ + step ≤ s.g)
    (hunit : s.t₂ + rootLength ≤ s.g₂)
    (hactual : actualWidth ≤ s.sixthDeletionWidth rootLength + cutoff + error)
    (herror : cutoff + error ≤ step / 2) :
    actualWidth ≤ s.parentWidth - step / 2 := by
  have hdrop := s.sixthDeletion_width_drop_with_errors rootLength step cutoff error
    actualWidth henlarge hunit hactual
  linarith

/-- A nonempty clipped row uses its original cutoff error.  The new
root cost is confined to the support component. -/
theorem sixthDeletion_clipped_width_drop (s : NominalChildGeometry)
    (rootLength step cutoff : ℝ)
    (henlarge : s.enlargementJ + step ≤ s.g)
    (hunit : s.t₂ + rootLength ≤ s.g₂)
    (hnonempty : 0 ≤ s.nominalRow + cutoff) :
    max 0 (s.nominalRow + cutoff) + (s.nominalSupport + rootLength) ≤
      s.parentWidth - step + cutoff := by
  rw [max_eq_right hnonempty]
  have hdrop := s.sixthDeletion_width_drop rootLength step henlarge hunit
  dsimp only [sixthDeletionWidth, nominalWidth] at hdrop
  linarith

theorem sixthDeletion_raw_shift_le (s : NominalChildGeometry)
    (rootLength ell supportError : ℝ) (hroot : 0 ≤ rootLength)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : s.paidShift ≤ 6 * (s.w + ell) + supportError) :
    s.rawDegree - s.sixthDeletionWidth rootLength ≤
      s.A - s.parentWidth + 6 * (s.w + ell) + supportError := by
  have hshift := s.raw_shift_le ell supportError hcommon hpaid
  dsimp only [sixthDeletionWidth]
  linarith

end NominalChildGeometry

/-- Derived from the original parent, extraction and clipping ledger.
Adding the full nonnegative root support cannot increase the defect;
no prior capacity-defect bound is an input. -/
theorem sixthDeletion_capacity_from_allocation
    (s : NominalChildGeometry) (a : RealParameters)
    (rootLength zBefore reduction ell supportError clipError widthError : ℝ)
    (hroot : 0 ≤ rootLength) (hκ : 0 ≤ a.κ) (hlive : a.z ≤ zBefore)
    (hred : zBefore - a.z ≤ reduction)
    (hparent : s.A + (6 * a.κ - 1) * zBefore ≤ s.parentWidth)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : s.paidShift ≤ 6 * (s.w + ell) + supportError)
    (hclip : a.n₁ + a.n₂ + a.z ≤ s.rawDegree - reduction + clipError)
    (hwidth : s.nominalWidth - (a.m + a.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (s.w + ell) + supportError + clipError + widthError) :
    max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + (a.q + rootLength))) 0 ≤
      6 * (s.w + ell) + supportError + clipError + widthError := by
  have hold := child_capacity_from_allocation s a zBefore reduction ell supportError
    clipError widthError hκ hlive hred hparent hcommon hpaid hclip hwidth hbudget
  apply le_trans (max_le_max ?_ le_rfl) hold
  linarith

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reduced allowance is paid by the actual common radical and
sixth-root divisibility, with the original nonnegative boundary cost. -/
theorem secondSixthDeletionChildAllowance_lower
    (Z : ℝ) (hZ : 1 < Z) (w B ell : ℝ) (hB : 0 ≤ B)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    w + ell ≤ secondSixthDeletionChildAllowance Z w B ell
      (primePowerProduct p m).val (primePowerProduct p n).val
      (secondSixthRootIdeal p m n).val := by
  have hroot := secondSixthRoot_common_log_slack_mean Z hZ p hp m n hm hn
  unfold secondSixthDeletionChildAllowance secondCommonChildAllowance
  linarith

namespace ActualSecondCorrelationRows

variable {H : Type*} (R : ActualSecondCorrelationRows A σ H ι)

/-- The actual row record supplies the reduced allowance with its
original prime list and both original positive multiplicities. -/
theorem sixthDeletion_allowance_lower (Z : ℝ) (hZ : 1 < Z)
    (w B ell : ℝ) (hB : 0 ≤ B)
    (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i) :
    w + ell ≤ secondSixthDeletionChildAllowance Z w B ell
      (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val :=
  secondSixthDeletionChildAllowance_lower Z hZ w B ell hB R.primes
    R.primes_injective R.leftMultiplicity R.rightMultiplicity hm hn

end ActualSecondCorrelationRows

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- The enlarged second width is exactly the original nominal ledger
plus the same root.  The old support coordinate is kept literally. -/
theorem sixthDeletionWidth_eq (root : Ideal (𝓞 K)) :
    G.skeleton.sixthDeletionWidth (idealLogLength Z root) =
      secondSixthDeletionChildWidth Z
        (G.skeleton.A - G.skeleton.c - G.skeleton.w)
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo
        G.skeleton.Krow G.skeleton.g G.ideals.second.val G.ideals.secondOpposite.val
        G.ideals.unitPart.val G.ideals.nonunitPart.val root := by
  sorry

namespace ScaleWindows

variable {G} {m q : ℝ} (W : G.ScaleWindows m q)

/-- This is the new scale identity derived from the old record.  It
does not construct an old `ScaleWindows` record at the enlarged q. -/
theorem sixthDeletion_support_parameter (hZ : 1 < Z)
    (root : Ideal (𝓞 K)) (hroot : root ≠ 0) :
    Z ^ (q + idealLogLength Z root) = W.supportScale *
      ((Ideal.absNorm G.ideals.unitPart.val : ℝ) *
        (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) * (Ideal.absNorm root : ℝ)) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ), W.support_parameter,
    rpow_idealLogLength Z hZ root hroot]
  ring

/-- The same two original errors control the enlarged width on both
sides; the same root is added to the actual and nominal supports. -/
theorem sixthDeletion_width_bounds (hZ : 1 < Z) (rootLength : ℝ) :
    m + (q + rootLength) ≤ G.skeleton.sixthDeletionWidth rootLength + W.error ∧
      G.skeleton.sixthDeletionWidth rootLength - (m + (q + rootLength)) ≤ W.error := by
  have hwidth := W.width_bounds hZ
  dsimp only [NominalChildGeometry.sixthDeletionWidth]
  constructor <;> linarith [hwidth.1, hwidth.2]

include W in
theorem sixthDeletion_width_drop (hZ : 1 < Z) (hstep : 0 ≤ step)
    (rootLength : ℝ) (hunit : G.skeleton.t₂ + rootLength ≤ G.skeleton.g₂) :
    m + (q + rootLength) ≤ a.m + a.q - step / 2 := by
  sorry

/-- A further Fourier cutoff consumes its own explicit part of the
step.  It is never absorbed by changing the old scale-window record. -/
theorem sixthDeletion_width_drop_with_cutoff (hZ : 1 < Z) (hstep : 0 ≤ step)
    (rootLength cutoff : ℝ)
    (hunit : G.skeleton.t₂ + rootLength ≤ G.skeleton.g₂)
    (herror : W.error + cutoff ≤ step / 2) :
    m + (q + rootLength) + cutoff ≤ a.m + a.q - step / 2 := by
  have hwidth := (W.sixthDeletion_width_bounds hZ rootLength).1
  have hdrop := G.skeleton.sixthDeletion_width_drop rootLength step
    (G.enlargement_bound hstep) hunit
  rw [G.parentWidth] at hdrop
  linarith

end ScaleWindows

section ActualRows

variable [IsPrincipalIdealRing A.R]
variable {H : Type*} {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- Only literal original ideal identities bind the nominal geometry
to the actual row class.  Both root slacks are then conclusions of the
original prime multiplicities, not new geometric input bounds. -/
theorem sixthDeletion_slack_of_rowMass
    (hZ : 1 < Z) (hn : ∀ i, 0 < R.rightMultiplicity i) (h : R.rows)
    (hsecond : G.ideals.second.val = W.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val) :
    let r₆ := idealLogLength Z
      (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
    0 ≤ r₆ ∧ G.skeleton.t₂ + r₆ ≤ G.skeleton.g₂ ∧
      G.secondRadical + r₆ ≤ G.halfSecond := by
  have hbudget := R.sixthRoot_log_budget C Z hZ W.left_positive hn h.val
  dsimp only at hbudget ⊢
  simpa only [skeleton, halfSecond, secondRadical, hsecond, hopposite, hunit,
    ActualSecondRowMass.leftIdeal, ActualSecondRowMass.rightIdeal,
    W.unit_ideal h.val h.property] using hbudget

/-- The actual original geometry chooses the enlargement and boundary
itself.  Its full-root width still drops by the chosen step, and its
reduced allowance still pays the same removal and pool lengths. -/
theorem sixthDeletion_bounds_of_rowMass
    (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hn : ∀ i, 0 < R.rightMultiplicity i) (h : R.rows)
    (hsecond : G.ideals.second.val = W.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val) :
    let root := (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
    G.skeleton.sixthDeletionWidth (idealLogLength Z root) ≤ a.m + a.q - step ∧
      G.skeleton.w + G.tag.poolLength step ≤
        secondSixthDeletionChildAllowance Z G.skeleton.w G.boundary
          (G.tag.poolLength step) G.ideals.second.val G.ideals.secondOpposite.val root := by
  dsimp only
  have hslack := G.sixthDeletion_slack_of_rowMass W hZ hn h hsecond hopposite hunit
  dsimp only at hslack
  constructor
  · simpa only [G.parentWidth] using
      G.skeleton.sixthDeletion_width_drop
        (idealLogLength Z
          (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val)
        step (G.enlargement_bound hstep) hslack.2.1
  · have hB := G.boundary_nonneg
    change G.skeleton.w + G.tag.poolLength step ≤
      G.halfSecond - G.secondRadical + G.skeleton.w + G.boundary +
        G.tag.poolLength step - idealLogLength Z
          (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val
    linarith [hslack.2.2]

end ActualRows

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_sixthDeletion_actual_scalar_budget_identity
#print axioms HeckeSkeleton.Moments.EngineStep.sixthDeletion_capacity_from_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.ScaleWindows.sixthDeletion_support_parameter
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.sixthDeletion_bounds_of_rowMass
