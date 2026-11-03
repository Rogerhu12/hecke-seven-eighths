import HeckeSkeleton.Moments.MOM_INV_STEP.CenteredChildGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition

/-!
# Descent margins after the actual fixed smooth test partition

The fixed smooth partition changes a column scale by (3/2)^j,
j = -18,...,5. These shifts are retained in every child length.
The public margin and physical energy losses still follow from the
same fine mesh. A negative piece length is clipped only numerically
here; its actual unit-column estimate is a separate source theorem,
not an invocation of the canonical child hypothesis.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.PartitionedChildGeometry

open HeckePort.Moments
open HeckeSkeleton.Moments.MOM_INV_STEP
open scoped Classical

def pieceLength (Z N : ℝ) (i : SchwartzTestPartition.Index) : ℝ :=
  max 0 N + Real.logb Z (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i))

/-- Exact logarithmic length of the real scale in the fixed smooth
partition, after the original complete-pool clipping. -/
theorem pieceLength_eq_logb (Z U : ℝ) (hZ : 1 < Z) (hU : 0 < U)
    (i : SchwartzTestPartition.Index) :
    pieceLength Z (Real.logb Z U) i =
      Real.logb Z
        (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * max 1 U) := by
  have hs := SchwartzTestPartition.scale_pos (SchwartzTestPartition.exponent i)
  rcases le_total 1 U with h | h
  · have hl : 0 ≤ Real.logb Z U := Real.logb_nonneg hZ h
    rw [pieceLength, max_eq_right hl, max_eq_right h,
      Real.logb_mul hs.ne' hU.ne']
    ring
  · have hl : Real.logb Z U ≤ 0 :=
      (Real.logb_le_iff_le_rpow hZ hU).mpr (by simpa only [Real.rpow_zero] using h)
    rw [pieceLength, max_eq_left hl, max_eq_left h, mul_one, zero_add]

theorem piece_shift_bounds (Z h : ℝ) (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h)
    (i : SchwartzTestPartition.Index) :
    -18 * h ≤
        Real.logb Z (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)) ∧
      Real.logb Z (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)) ≤
        5 * h := by
  have hl0 : 0 ≤ Real.logb Z (3 / 2 : ℝ) := Real.logb_nonneg hZ (by norm_num)
  have hlh : Real.logb Z (3 / 2 : ℝ) ≤ h :=
    (Real.logb_le_iff_le_rpow hZ (by norm_num : (0 : ℝ) < 3 / 2)).mpr
      ((by norm_num : (3 / 2 : ℝ) ≤ 2).trans hwidth)
  have he := SchwartzTestPartition.exponent_bounds i
  have hlo : (-18 : ℝ) ≤ (SchwartzTestPartition.exponent i : ℝ) := by
    exact_mod_cast he.1
  have hhi : (SchwartzTestPartition.exponent i : ℝ) ≤ (5 : ℝ) := by
    exact_mod_cast he.2
  have hp :
      Real.logb Z (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)) =
        (SchwartzTestPartition.exponent i : ℝ) * Real.logb Z (3 / 2 : ℝ) := by
    simp only [SchwartzTestPartition.scale, Real.logb, Real.log_zpow, mul_div_assoc]
  rw [hp]
  constructor
  · have hm := mul_le_mul_of_nonneg_right hlo hl0
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hhi hl0
    nlinarith

/-- The numerical clipping of a negative piece can only improve its
lower margin. Its upper shift stays within the same positive endpoint. -/
theorem piece_clipped_shift (Z Nformal Nactual h : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hlo : Nformal - 5 * h ≤ Nactual) (hhi : Nactual ≤ Nformal + 8 * h)
    (hlive : -2 * h ≤ Nactual) (i : SchwartzTestPartition.Index) :
    -19 * h ≤ max 0 (pieceLength Z Nactual i) - Nformal + 4 * h ∧
      max 0 (pieceLength Z Nactual i) - Nformal + 4 * h ≤ 19 * h := by
  obtain ⟨hslo,hshi⟩ := CenteredChildGeometry.clipped_shift Nformal Nactual h hh hlo hhi hlive
  obtain ⟨hdlo,hdhi⟩ := piece_shift_bounds Z h hZ hwidth i
  have hn0 : 0 ≤ max 0 Nactual := le_max_left _ _
  have hlo' := le_max_right (0 : ℝ) (pieceLength Z Nactual i)
  have hhi' : max 0 (pieceLength Z Nactual i) ≤ max 0 Nactual + 5 * h := by
    apply max_le
    · linarith
    · dsimp only [pieceLength]
      linarith
  dsimp only [pieceLength] at hlo' hhi' ⊢
  constructor <;> linarith

/-- Actual smooth pieces preserve all public single-step margins.
When a piece length is negative, the effective length zero is used only
for the separate actual unit-column bound. -/
theorem partitioned_step
    (Z M r ell V Q Qnew z c d A B t g theta v j h eta Nactual Mactual : ℝ)
    (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h)
    (hparent : CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hell : 0 ≤ ell) (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hcommon : -2 * h ≤ g - theta)
    (hlabel : j ≤ 2 * ell + 3 * h)
    (hpuncture : Qnew ≤ Q + decrease ell A t g theta V + 4 * h)
    (hnonterminal : d ≤ ell + V)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual)
    (hrow : Mactual ≤ childM M ell A t g theta V j (5 * h))
    (i : SchwartzTestPartition.Index) :
    let Fc := max 0 (pieceLength Z Nactual i) + secondFormalLabel B theta v j + 4 * h
    c - 5 * eta ≤ Fc - Mactual - Qnew - z ∧
      c - 7 * eta ≤ 4 * Fc - 3 * Mactual - 6 * z ∧
      3 * d / 2 ≤ M - Mactual ∧ Fc ≤ r + 3 * ell + V + 11 * eta := by
  obtain ⟨hslo,hshi⟩ := piece_clipped_shift Z (secondFormalColumn r A B t g v)
    Nactual h hZ hh hwidth hlo hhi hlive i
  obtain ⟨hp₁,hp₂⟩ := hparent
  dsimp only
  unfold secondFormalColumn at hslo hshi
  unfold secondFormalLabel childM decrease at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Both powers of the actual piece's combined length fit in the
original public loss. No partition scale is discarded from the exponent. -/
theorem physical_exponent_budget
    (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual : ℝ)
    (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) (i : SchwartzTestPartition.Index) :
    firstKappa M r ell V delta A B R +
      secondLambda M r ell V delta A B j t g theta +
      secondCount ell R j t g theta +
      2 * (max 0 (pieceLength Z Nactual i) + secondFormalLabel B theta v j + 4 * h) +
      (9 / 2 + 18 + 11 / 2) * h + tau + pi + eps ≤
      r + 3 * ell + V + 40 * eta + tau + pi + eps := by
  have hs := (piece_clipped_shift Z (secondFormalColumn r A B t g v) Nactual h
    hZ hh hwidth hlo hhi hlive i).2
  have hi := physical_prefactor_identity M r ell V delta A B R j t g theta v
  linarith

theorem physical_power_budget
    (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual : ℝ)
    (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) (i : SchwartzTestPartition.Index) :
    Z ^ (firstKappa M r ell V delta A B R + (9 / 2 : ℝ) * h) *
      Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * h + tau) *
      Z ^ (secondCount ell R j t g theta + (11 / 2 : ℝ) * h + pi) *
      Z ^ (2 * (max 0 (pieceLength Z Nactual i) + secondFormalLabel B theta v j + 4 * h) + eps) ≤
      Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hb := physical_exponent_budget Z M r ell V delta A B R j t g theta v h eta
    tau pi eps Nactual hZ hwidth hh hmesh hlo hhi hlive i
  linarith

/-- The exact first capacity loss is useful for an actual unit column.
It does not require the public margin c-5*eta to remain positive. -/
theorem first_capacity_loss
    (Z M r ell V Q Qnew z c A B t g theta v j h Nactual Mactual : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hparent : c ≤ r + 3 * ell + V - M - Q - z)
    (hpuncture : Qnew ≤ Q + decrease ell A t g theta V + 4 * h)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual)
    (hrow : Mactual ≤ childM M ell A t g theta V j (5 * h))
    (i : SchwartzTestPartition.Index) :
    c - 28 * h ≤ max 0 (pieceLength Z Nactual i) +
      secondFormalLabel B theta v j + 4 * h - Mactual - Qnew - z := by
  have hs := (piece_clipped_shift Z (secondFormalColumn r A B t g v) Nactual h
    hZ hh hwidth hlo hhi hlive i).1
  unfold secondFormalColumn at hs
  unfold secondFormalLabel childM decrease at *
  linarith

/-- If the real piece has scale below one, its effective column length
is zero. The actual first capacity then controls the remaining row mass
by the label mass, with an explicit 28h allowance. -/
theorem small_piece_row_bound
    (Z M r ell V Q Qnew z c A B t g theta v j h Nactual Mactual : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hparent : c ≤ r + 3 * ell + V - M - Q - z)
    (hc : 0 ≤ c) (hQ : 0 ≤ Qnew) (hz : 0 ≤ z)
    (hpuncture : Qnew ≤ Q + decrease ell A t g theta V + 4 * h)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual)
    (hrow : Mactual ≤ childM M ell A t g theta V j (5 * h))
    (i : SchwartzTestPartition.Index) (hsmall : pieceLength Z Nactual i ≤ 0) :
    Mactual ≤ secondFormalLabel B theta v j + 4 * h + 28 * h := by
  have hb := first_capacity_loss Z M r ell V Q Qnew z c A B t g theta v j h
    Nactual Mactual hZ hh hwidth hparent hpuncture hlo hhi hlive hrow i
  rw [max_eq_left hsmall] at hb
  linarith

/-- Counting the actual unit column by row mass times label mass still
fits the same public physical loss. This is the numerical companion to
the exact source unit-collapse theorem, not a smaller-child hypothesis. -/
theorem small_piece_physical_exponent_budget
    (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual Mactual : ℝ)
    (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) (i : SchwartzTestPartition.Index)
    (hsmall : pieceLength Z Nactual i ≤ 0)
    (hrow : Mactual ≤ secondFormalLabel B theta v j + 4 * h + 28 * h) :
    firstKappa M r ell V delta A B R +
      secondLambda M r ell V delta A B j t g theta +
      secondCount ell R j t g theta +
      Mactual + (secondFormalLabel B theta v j + 4 * h) +
      (9 / 2 + 18 + 11 / 2) * h + tau + pi + eps ≤
      r + 3 * ell + V + 40 * eta + tau + pi + eps := by
  have hs := (piece_clipped_shift Z (secondFormalColumn r A B t g v) Nactual h
    hZ hh hwidth hlo hhi hlive i).2
  rw [max_eq_left hsmall] at hs
  have hi := physical_prefactor_identity M r ell V delta A B R j t g theta v
  linarith

end HeckeSkeleton.Moments.MOMInvStep.PartitionedChildGeometry

end
