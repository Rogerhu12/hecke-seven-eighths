import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceActualScale
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionMellin

/-!
# The common prefix energy is a sum of actual canonical annular energies

The fixed enlarged ideal pool contains every supported annular piece.
All extra terms vanish for the same original test.  The normalization
contributes the precise square root of each fixed partition scale; their
squares are at most eight.  Cauchy is applied to the actual 24 pieces and
then to the actual finite set of dyadic scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourcePrefixEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOM_INV_STEP
open CommonKernel SourceAnnularRows SourceActualScale
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def pool (L : ℕ) : Finset (NonzeroIdeal K) := dyadicIdealSupport K (8 * (2 : ℝ) ^ L)

def scale (j : ℕ) (i : SchwartzTestPartition.Index) : ℝ :=
  SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * (2 : ℝ) ^ j

theorem scale_pos (j : ℕ) (i : SchwartzTestPartition.Index) : 0 < scale j i :=
  mul_pos (SchwartzTestPartition.scale_pos _) (by positivity)

theorem scale_le_pool {j L : ℕ} (hj : j ≤ L) (i : SchwartzTestPartition.Index) :
    scale j i ≤ 8 * (2 : ℝ) ^ L := by
  exact mul_le_mul (CubeCompletionMellin.annular_scale_le_eight i)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    (by positivity) (by norm_num)

theorem supported_sum_eq (a : NonzeroIdeal K → ℂ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (U R : ℝ) (hU : 0 < U) (hUR : U ≤ R) :
    (∑ I ∈ dyadicIdealSupport K R, a I * W (idealNorm K I / U)) =
      ∑ I ∈ dyadicIdealSupport K U, a I * W (idealNorm K I / U) := by
  symm
  apply Finset.sum_subset
  · intro I hI
    apply (mem_dyadicIdealSupport_iff K (hU.le.trans hUR) I).mpr
    have hnorm := (mem_dyadicIdealSupport_iff K hU.le I).mp hI
    linarith
  · intro I hI hnot
    have hz : W (idealNorm K I / U) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hnot ((mem_dyadicIdealSupport_iff K hU.le I).mpr ((div_le_iff₀ hU).mp (hW hs).2))
    rw [hz, mul_zero]

/-- Each term on the right is the literal complete norm-envelope
polynomial with its original coefficient and complete row mask. -/
theorem annular_eq_pieces (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (L j : ℕ) (hj : j ≤ L) (t : ℝ) :
    SourceScaleSup.annularColumn (pool K L) (normWeightedCoefficient d u)
        (idealNorm K) j t =
      columnPhase t (Real.log ((2 : ℝ) ^ j)) *
        ∑ i : SchwartzTestPartition.Index,
          (Real.sqrt (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)) : ℂ) *
            polynomial K d u (scale j i) (SourceAnnularTests.piece t i) := by
  unfold normWeightedCoefficient
  rw [SourceAnnularTests.finite_annular_eq (pool K L) (inverseRowCoefficient d u)
    (idealNorm K) (fun I hI => idealNorm_pos K I) j t,
    SourceAnnularTests.finite_test_eq_pieces]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (Real.sqrt ((2 : ℝ) ^ j) : ℂ)⁻¹ *
    (∑ I ∈ dyadicIdealSupport K (8 * (2 : ℝ) ^ L),
      inverseRowCoefficient d u I *
        SourceAnnularTests.piece t i (idealNorm K I / scale j i)) = _
  rw [supported_sum_eq K (inverseRowCoefficient d u) (SourceAnnularTests.piece t i)
    (SourceAnnularTests.piece_support t i) (scale j i) (8 * (2 : ℝ) ^ L)
    (scale_pos j i) (scale_le_pool hj i)]
  unfold polynomial scale
  rw [Real.sqrt_mul (SchwartzTestPartition.scale_pos _).le, Complex.ofReal_mul, mul_inv_rev]
  have hs : (Real.sqrt (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (SchwartzTestPartition.scale_pos _)).ne'
  field_simp

theorem annular_sq_le (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (L j : ℕ) (hj : j ≤ L) (t : ℝ) :
    ‖SourceScaleSup.annularColumn (pool K L) (normWeightedCoefficient d u)
        (idealNorm K) j t‖ ^ 2 ≤
      192 * ∑ i : SchwartzTestPartition.Index,
        ‖polynomial K d u (scale j i) (SourceAnnularTests.piece t i)‖ ^ 2 := by
  rw [annular_eq_pieces K d u L j hj t, norm_mul, norm_columnPhase, one_mul]
  let p := fun i : SchwartzTestPartition.Index =>
    polynomial K d u (scale j i) (SourceAnnularTests.piece t i)
  let s := fun i : SchwartzTestPartition.Index =>
    SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)
  have hc : (Finset.univ : Finset SchwartzTestPartition.Index).card = 24 := by
    simp only [Finset.card_univ, SchwartzTestPartition.Index, Fintype.card_fin]
  calc
    _ ≤ (∑ i : SchwartzTestPartition.Index, ‖(Real.sqrt (s i) : ℂ) * p i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.univ : Finset SchwartzTestPartition.Index).card : ℝ) *
        ∑ i : SchwartzTestPartition.Index, ‖(Real.sqrt (s i) : ℂ) * p i‖ ^ 2 :=
      _root_.sq_sum_le_card_mul_sum_sq
    _ ≤ 24 * ∑ i : SchwartzTestPartition.Index, 8 * ‖p i‖ ^ 2 := by
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (SchwartzTestPartition.scale_pos _).le]
      exact mul_le_mul_of_nonneg_right (CubeCompletionMellin.annular_scale_le_eight i) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; dsimp only [p]; ring

/-- Positive complete-row energies are summed before the common
frequency integral.  The cost is exactly the finite dyadic count and the
fixed 24-piece normalization constant. -/
theorem prefix_energy_le (d : MomentData K ω ψ) (R : Finset (NonzeroIdeal K))
    (L : ℕ) (t : ℝ) :
    (∑ u ∈ R, ‖SourceScaleSup.prefixColumn (pool K L) (normWeightedCoefficient d u)
        (idealNorm K) L t‖ ^ 2) ≤
      192 * (L + 1 : ℕ) *
        ∑ j ∈ Finset.range (L + 1), ∑ i : SchwartzTestPartition.Index,
          ∑ u ∈ R, ‖polynomial K d u (scale j i) (SourceAnnularTests.piece t i)‖ ^ 2 := by
  have hAnn (j : ℕ) (hj : j ∈ Finset.range (L + 1)) :
      (∑ u ∈ R, ‖SourceScaleSup.annularColumn (pool K L) (normWeightedCoefficient d u)
        (idealNorm K) j t‖ ^ 2) ≤
      192 * ∑ i : SchwartzTestPartition.Index, ∑ u ∈ R,
        ‖polynomial K d u (scale j i) (SourceAnnularTests.piece t i)‖ ^ 2 := by
    calc
      _ ≤ ∑ u ∈ R, 192 * ∑ i : SchwartzTestPartition.Index,
          ‖polynomial K d u (scale j i) (SourceAnnularTests.piece t i)‖ ^ 2 :=
        Finset.sum_le_sum (fun u hu => annular_sq_le K d u L j
          (by have := Finset.mem_range.mp hj; omega) t)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    _ ≤ ∑ u ∈ R, (L + 1 : ℕ) * ∑ j ∈ Finset.range (L + 1),
        ‖SourceScaleSup.annularColumn (pool K L) (normWeightedCoefficient d u)
          (idealNorm K) j t‖ ^ 2 :=
      Finset.sum_le_sum (fun u hu => SourceScaleSup.prefixColumn_sq_le
        (pool K L) (normWeightedCoefficient d u) (idealNorm K)
        (fun I hI => one_le_idealNorm K I) L t)
    _ = (L + 1 : ℕ) * ∑ j ∈ Finset.range (L + 1), ∑ u ∈ R,
        ‖SourceScaleSup.annularColumn (pool K L) (normWeightedCoefficient d u)
          (idealNorm K) j t‖ ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (L + 1 : ℕ) * ∑ j ∈ Finset.range (L + 1),
        192 * ∑ i : SchwartzTestPartition.Index, ∑ u ∈ R,
          ‖polynomial K d u (scale j i) (SourceAnnularTests.piece t i)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hAnn) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourcePrefixEnergy

end
