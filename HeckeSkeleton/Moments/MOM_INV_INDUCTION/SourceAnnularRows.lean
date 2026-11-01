import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularTests
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceOrientation
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceReductionPoisson
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerEnergy

/-!
# Complete ideal rows for the actual fixed-test inverse polynomial

The norm envelope in the polynomial is explicit.  Replacing the inherited
profile by one supported Schwartz test changes no coefficient, character,
direction, puncture or complete row.  This is the polynomial occurring
inside the common scale-sup prefix after its finite annular partition.

The bounded column range is estimated directly from the original ideal
sum and the linear ideal count.  It does not require the row scale to be
bounded, and hence supplies the small annular scales of the strict seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularRows

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def supportedTest (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    IdealTest K where
  profile _ _ y := W y
  support _ _ X := if 0 < X then
    (dyadicIdealSupport K X).filter (fun I => W (idealNorm K I / X) ≠ 0) else ∅
  support_spec _ _ X I := by
    by_cases hX : 0 < X
    · rw [if_pos hX, Finset.mem_filter, mem_dyadicIdealSupport_iff K hX.le]
      constructor
      · exact And.right
      · intro h
        exact ⟨(div_le_iff₀ hX).mp (hW (subset_closure (Function.mem_support.mpr h))).2, h⟩
    · have hz : W (idealNorm K I / X) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        have hy := (hW hm).1
        have hn := div_nonpos_of_nonneg_of_nonpos (idealNorm_pos K I).le (le_of_not_gt hX)
        linarith
      simp only [if_neg hX, Finset.notMem_empty, hz, ne_eq, not_true_eq_false]

def testData (d : MomentData K ω ψ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : MomentData K ω ψ :=
  { d with inverseTest := supportedTest K W hW }

def polynomial (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (X : ℝ) (W : SchwartzMap ℝ ℂ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑ I ∈ dyadicIdealSupport K X,
    inverseRowCoefficient d u I * W (idealNorm K I / X)

/-- The original exact-support polynomial and the full norm-envelope
polynomial agree.  Added summands are the same arithmetic zeros. -/
theorem polynomial_eq (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (X : ℝ) (hX : 0 < X) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    inversePolynomial (testData K d W hW) u X 0 = polynomial K d u X W := by
  rw [inversePolynomial_sum_coeff]
  change (Real.sqrt X : ℂ)⁻¹ *
    ∑ I ∈ (supportedTest K W hW).support u 0 X,
      inverseRowCoefficient d u I * W (idealNorm K I / X) = _
  simp only [supportedTest, if_pos hX, Finset.sum_filter, polynomial]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : W (idealNorm K I / X) = 0 <;> simp only [hz, ne_eq, not_true_eq_false,
    if_false, mul_zero, not_false_eq_true, if_true]

theorem polynomial_eq_zero_small (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (X : ℝ) (hX : 0 < X) (hsmall : X < 1 / 2) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : polynomial K d u X W = 0 := by
  unfold polynomial
  have he : (∑ I ∈ dyadicIdealSupport K X,
      inverseRowCoefficient d u I * W (idealNorm K I / X)) = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    have hz : W (idealNorm K I / X) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hn := (div_le_iff₀ hX).mp (hW hs).2
      linarith [one_le_idealNorm K I]
    rw [hz, mul_zero]
  rw [he, mul_zero]

/-- The low column scales cost only a constant times the complete row
count.  This bound is simultaneous in the original MomentData and test. -/
theorem exists_small_scale_row_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K}
      (d : MomentData K ω ψ) (H X : ℝ) (W : SchwartzMap ℝ ℂ),
      1 ≤ H → 0 < X → X ≤ 1 → tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      (∑ u ∈ d.rows H, ‖polynomial K d u X W‖ ^ 2) ≤
        C * H * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := exists_nonzero_ideal_count_bound (K := K)
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  refine ⟨16 * A ^ 3, by positivity, ?_⟩
  intro ω ψ d H X W hH hX hX1 hW
  by_cases hsmall : X < 1 / 2
  · have hz : (∑ u ∈ d.rows H, ‖polynomial K d u X W‖ ^ 2) = (0 : ℝ) := by
      apply Finset.sum_eq_zero
      intro u hu
      simp only [polynomial_eq_zero_small K d u X hX hsmall W hW, norm_zero,
        pow_two, mul_zero]
    rw [hz]
    positivity
  · have hXlower : 1 / 2 ≤ X := le_of_not_gt hsmall
    have hinv : (Real.sqrt X)⁻¹ ≤ 2 := by
      have hroot : 1 / 2 ≤ Real.sqrt X := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      have hi := (inv_le_inv₀ (Real.sqrt_pos.2 hX)
        (by norm_num : (0 : ℝ) < 1 / 2)).mpr hroot
      norm_num at hi
      exact hi
    let Q := SchwartzMap.seminorm ℝ 0 0 W
    have hQ : 0 ≤ Q := apply_nonneg _ _
    have hcols : ((dyadicIdealSupport K X).card : ℝ) ≤ A * 2 := by
      apply hcount _ 2 (by norm_num)
      intro I hI
      have hn := (mem_dyadicIdealSupport_iff K hX.le I).mp hI
      linarith
    have hpoly (u : NonzeroIdeal K) : ‖polynomial K d u X W‖ ≤ 4 * A * Q := by
      have hs : ‖∑ I ∈ dyadicIdealSupport K X,
          inverseRowCoefficient d u I * W (idealNorm K I / X)‖ ≤ A * 2 * Q := by
        apply (norm_sum_le _ _).trans
        have hp : (∑ I ∈ dyadicIdealSupport K X,
            ‖inverseRowCoefficient d u I * W (idealNorm K I / X)‖) ≤
              ((dyadicIdealSupport K X).card : ℝ) * Q := by
          calc
            _ ≤ ∑ _I ∈ dyadicIdealSupport K X, Q := by
              apply Finset.sum_le_sum
              intro I hI
              rw [norm_mul]
              exact (mul_le_mul (norm_inverseRowCoefficient_le_one d u I)
                (SchwartzMap.norm_le_seminorm ℝ W _) (norm_nonneg _) zero_le_one).trans_eq
                (one_mul Q)
            _ = _ := by simp
        exact hp.trans (mul_le_mul_of_nonneg_right hcols hQ)
      rw [polynomial, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul hinv hs (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hrows : ((d.rows H).card : ℝ) ≤ A * H :=
      hcount _ H hH (fun u hu => ((d.rows_spec H u).mp hu).2)
    calc
      _ ≤ ∑ _u ∈ d.rows H, (4 * A * Q) ^ 2 :=
        Finset.sum_le_sum (fun u hu => pow_le_pow_left₀ (norm_nonneg _) (hpoly u) 2)
      _ = ((d.rows H).card : ℝ) * (4 * A * Q) ^ 2 := by simp
      _ ≤ A * H * (4 * A * Q) ^ 2 := mul_le_mul_of_nonneg_right hrows (sq_nonneg _)
      _ = _ := by dsimp only [Q]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceAnnularRows

end
