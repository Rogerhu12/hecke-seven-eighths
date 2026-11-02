import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionOperator
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RowIntegralKernel
import HeckeSkeleton.Moments.MOM_BASE.PairedPolynomials

/-!
# The actual reflected column inside the original moment energy

The operator uses the inverse of the entire actual plain character.
Conjugating its power window reverses the common frequency and restores
the original character.  This is an equality of the absolute square,
with the other original plain factor, every prime slot, and the complete
common mask unchanged.  No alternate arithmetic row is constructed.

The finite column has a genuine frequency-independent pointwise bound.
It is used only to establish L2 in any finite positive frequency kernel,
not as a contribution to the final moment estimate or kernel mass.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators ComplexConjugate

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The real fixed cutoff makes conjugation exactly frequency reversal,
including the total definition at nonpositive norm ratios. -/
theorem ordinaryPowerWindow_conjugate (sigma frequency y : ℝ) :
    conj (ordinaryPowerWindow sigma frequency y) =
      ordinaryPowerWindow sigma (-frequency) y := by
  have hpoint : conj (idealVerticalPoint sigma frequency - 1) =
      idealVerticalPoint sigma (-frequency) - 1 := by
    simp [idealVerticalPoint] <;> ring
  simp only [ordinaryPowerWindow, profilePower, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, hpoint]

/-- Conjugation retains the exact fixed finite support of the column. -/
theorem ordinaryPowerColumn_conjugate (a : NonzeroIdeal K → ℂ)
    (sigma N frequency : ℝ) :
    ordinaryPowerColumn K (fun I => conj (a I)) sigma N frequency =
      conj (ordinaryPowerColumn K a sigma N (-frequency)) := by
  simp only [ordinaryPowerColumn, map_mul, map_sum, map_inv₀,
    Complex.conj_ofReal, ordinaryPowerWindow_conjugate, neg_neg]

/-- The literal dual column, before the norm-square identification. -/
def ordinaryDualPowerColumn (d : MomentData K omegaCharacter psiCharacter)
    (u : NonzeroIdeal K) (sigma N frequency : ℝ) : ℂ :=
  ordinaryPowerColumn K
    (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I *
      maskValue d u I.val) sigma N frequency

/-- The same original row, full common mask and plain character suffice;
only the actual test frequency changes sign. -/
theorem ordinaryDualPowerColumn_norm (d : MomentData K omegaCharacter psiCharacter)
    (u : NonzeroIdeal K) (sigma N frequency : ℝ) :
    ‖ordinaryDualPowerColumn d u sigma N frequency‖ =
      ‖plainPolynomial d (ordinaryPowerWindowIdealTest K sigma) u N (-frequency)‖ := by
  have hcoefficient :
      (fun I : NonzeroIdeal K =>
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I *
          maskValue d u I.val) =
      (fun I : NonzeroIdeal K => conj
        (heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          maskValue d u I.val)) := by
    funext I
    simp only [heckeIdealCoefficient_inv, map_mul,
      MOM_BASE.Paired.maskValue_conjugate]
  rw [ordinaryDualPowerColumn, hcoefficient, ordinaryPowerColumn_conjugate,
    Complex.norm_conj, ordinaryPowerColumn_eq_plainPolynomial]

/-- The replaced first test is frozen at the operator frequency; the
unreplaced test retains its original evaluation time. -/
theorem ordinaryPowerChild_plain_left (d : MomentData K omegaCharacter psiCharacter)
    (first : Bool) (sigma frequency : ℝ) (u : NonzeroIdeal K) (N time : ℝ) :
    plainPolynomial (ordinaryPowerChild K d first sigma frequency)
      (ordinaryPowerChild K d first sigma frequency).plainTest₁ u N time =
      if first then plainPolynomial d (ordinaryPowerWindowIdealTest K sigma) u N frequency
      else plainPolynomial d d.plainTest₁ u N time := by
  cases first <;>
    simp [ordinaryPowerChild, plainPolynomial, IdealTest.freezeTwist, profilePower_zero,
      maskValue]

theorem ordinaryPowerChild_plain_right (d : MomentData K omegaCharacter psiCharacter)
    (first : Bool) (sigma frequency : ℝ) (u : NonzeroIdeal K) (N time : ℝ) :
    plainPolynomial (ordinaryPowerChild K d first sigma frequency)
      (ordinaryPowerChild K d first sigma frequency).plainTest₂ u N time =
      if first then plainPolynomial d d.plainTest₂ u N time
      else plainPolynomial d (ordinaryPowerWindowIdealTest K sigma) u N frequency := by
  cases first <;>
    simp [ordinaryPowerChild, plainPolynomial, IdealTest.freezeTwist, profilePower_zero,
      maskValue]

theorem ordinaryPowerChild_slotProduct (d : MomentData K omegaCharacter psiCharacter)
    (first : Bool) (sigma frequency : ℝ) (u : NonzeroIdeal K) (U time : ℝ) :
    slotProduct (ordinaryPowerChild K d first sigma frequency) u U time =
      slotProduct d u U time := rfl

/-- Only the selected plain exponent changes. The width, kappa and
whole slot length retain their original numerical values. -/
def ordinaryPowerParameters (a : RealParameters) (first : Bool) (length : ℝ) :
    RealParameters :=
  { a with n₁ := if first then length else a.n₁
           n₂ := if first then a.n₂ else length }

theorem ordinaryPowerChild_rows (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma frequency length U : ℝ) :
    pairedRows (ordinaryPowerChild K d first sigma frequency)
      (ordinaryPowerParameters a first length) U = pairedRows d a U := rfl

/-- One literal dual column times all the other original factors. -/
def ordinaryDualRow (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (u : NonzeroIdeal K) (frequency : ℝ) : ℂ :=
  (if first then
    ordinaryDualPowerColumn d u sigma (U ^ length) frequency *
      plainPolynomial d d.plainTest₂ u (U ^ a.n₂) time
   else
    plainPolynomial d d.plainTest₁ u (U ^ a.n₁) time *
      ordinaryDualPowerColumn d u sigma (U ^ length) frequency) *
        slotProduct d u U time

/-- Exact summand calibration to an actual child of the original model. -/
theorem ordinaryDualRow_norm_sq (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (u : NonzeroIdeal K) (frequency : ℝ) :
    ‖ordinaryDualRow d a first sigma length U time u frequency‖ ^ 2 =
      ‖plainPolynomial (ordinaryPowerChild K d first sigma (-frequency))
          (ordinaryPowerChild K d first sigma (-frequency)).plainTest₁ u
          (U ^ (ordinaryPowerParameters a first length).n₁) time *
        plainPolynomial (ordinaryPowerChild K d first sigma (-frequency))
          (ordinaryPowerChild K d first sigma (-frequency)).plainTest₂ u
          (U ^ (ordinaryPowerParameters a first length).n₂) time *
        slotProduct (ordinaryPowerChild K d first sigma (-frequency)) u U time‖ ^ 2 := by
  rw [ordinaryPowerChild_plain_left, ordinaryPowerChild_plain_right,
    ordinaryPowerChild_slotProduct]
  cases first <;> simp [ordinaryDualRow, ordinaryPowerParameters, norm_mul,
    ordinaryDualPowerColumn_norm]

/-- The entire original finite row sum equals the actual child energy.
No row filter or number of rows is discarded during conjugation. -/
theorem ordinaryDualRow_energy (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time frequency : ℝ) :
    (∑ u ∈ pairedRows d a U,
      ‖ordinaryDualRow d a first sigma length U time u frequency‖ ^ 2) =
      pairedEnergy (ordinaryPowerChild K d first sigma (-frequency))
        (ordinaryPowerParameters a first length) U time := by
  rw [pairedEnergy, ordinaryPowerChild_rows]
  apply Finset.sum_congr rfl
  intro u hu
  exact ordinaryDualRow_norm_sq d a first sigma length U time u frequency

theorem continuous_ordinaryDualRow (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (u : NonzeroIdeal K) :
    Continuous (ordinaryDualRow d a first sigma length U time u) := by
  have hc : Continuous (ordinaryDualPowerColumn d u sigma (U ^ length)) :=
    continuous_ordinaryPowerColumn K _ sigma (U ^ length)
  cases first
  · exact (continuous_const.mul hc).mul continuous_const
  · exact (hc.mul continuous_const).mul continuous_const

/-- An explicit finite column bound supplies integrability only. Its
possibly large arithmetic constant is not used in the kernel mass. -/
theorem ordinaryDualRow_bounded (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (hU : 0 < U) (u : NonzeroIdeal K) :
    ∃ B : ℝ, ∀ frequency : ℝ,
      ‖ordinaryDualRow d a first sigma length U time u frequency‖ ≤ B := by
  let b : NonzeroIdeal K → ℂ := fun I =>
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I *
      maskValue d u I.val
  let C := ordinaryPowerColumnMajorant K b sigma (U ^ length)
  have hc (frequency : ℝ) : ‖ordinaryDualPowerColumn d u sigma (U ^ length) frequency‖ ≤ C :=
    ordinaryPowerColumn_norm_le K b sigma frequency (Real.rpow_pos_of_pos hU length)
  cases first
  · refine ⟨‖plainPolynomial d d.plainTest₁ u (U ^ a.n₁) time‖ * C *
        ‖slotProduct d u U time‖, ?_⟩
    intro frequency
    simp only [ordinaryDualRow, Bool.false_eq_true, if_false, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc frequency) (norm_nonneg _)) (norm_nonneg _)
  · refine ⟨C * ‖plainPolynomial d d.plainTest₂ u (U ^ a.n₂) time‖ *
        ‖slotProduct d u U time‖, ?_⟩
    intro frequency
    simp only [ordinaryDualRow, if_true, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hc frequency) (norm_nonneg _)) (norm_nonneg _)

/-- Every actual column is L2 in the common finite positive measure. -/
theorem ordinaryDualRow_memLp (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (hU : 0 < U) (u : NonzeroIdeal K) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    MemLp (ordinaryDualRow d a first sigma length U time u) 2 mu := by
  obtain ⟨B, hB⟩ := ordinaryDualRow_bounded d a first sigma length U time hU u
  exact MemLp.of_bound
    (continuous_ordinaryDualRow d a first sigma length U time u).aestronglyMeasurable B
      (Filter.Eventually.of_forall hB)

/-- Integrability of the numerical child energy follows from the actual
finite polynomial columns, without a measurable space on MomentData. -/
theorem ordinaryPowerChild_energy_integrable (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time : ℝ)
    (hU : 0 < U) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Integrable (fun frequency : ℝ =>
      pairedEnergy (ordinaryPowerChild K d first sigma (-frequency))
        (ordinaryPowerParameters a first length) U time) mu := by
  simp_rw [← ordinaryDualRow_energy]
  exact integrable_finset_sum _ (fun u _ =>
    (ordinaryDualRow_memLp d a first sigma length U time hU u mu).norm.integrable_sq)

end HeckeSkeleton.Moments.EngineInduction
