module

public import HeckeSkeleton.ActualProbeThetaAbsolute
public import ThetaGlobal.ReflectedAbsoluteProject
public import ThetaGlobal.RegularizedTestProject
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Uniform quadratic tails and regularizer limits for the literal direct series

The source's finite-cardinality Gauss bound proves that the completed arithmetic
coefficient has norm at most one. The ordinary ideal norm-square series then
gives a two-ideal summable majorant. This file retains the actual squarefree,
whole-index coprimality, and mark masks in completedTerm.

No global theta reflection or calibration identity is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.PrimalLimitProject

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ReflectedAbsolute
open scoped Classical BigOperators Topology nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (θ : HeckeCharacter K)
variable (m : S.integer K) (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))

abbrev DirectIndex := ExteriorIdeal K S × ExteriorIdeal K S

def majorant (B X : ℝ) (cn : DirectIndex K S) : ℝ :=
  (B * X ^ 2) * inverseSquare (exteriorNorm K S cn.1) *
    inverseSquare (exteriorNorm K S cn.2)

theorem summable_majorant (B X : ℝ) :
    Summable (majorant K S B X) := by
  have hN := ReflectedAbsoluteProject.summable_exterior_inverseSquare K S
  have hprod := hN.mul_of_nonneg hN
    (fun c => inverseSquare_nonneg (exteriorNorm K S c))
    (fun n => inverseSquare_nonneg (exteriorNorm K S n))
  simpa only [majorant, mul_assoc] using hprod.mul_left (B * X ^ 2)

theorem completed_argument_pos {X : ℝ} (hX : 0 < X) (cn : DirectIndex K S) :
    0 < exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X :=
  div_pos (ReflectedArithmetic.exteriorNorm_pos K S _) hX

theorem completed_argument_inverseSquare_le {X : ℝ} (hX : 0 < X)
    (cn : DirectIndex K S) :
    inverseSquare (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X) ≤
      X ^ 2 * inverseSquare (exteriorNorm K S cn.1) *
        inverseSquare (exteriorNorm K S cn.2) := by
  have h := cubic_scale_inverse_square_le 1 (exteriorNorm K S cn.1)
    (exteriorNorm K S cn.2) X⁻¹ (by norm_num)
    (ReflectedArithmetic.exteriorNorm_pos K S cn.1)
    (ReflectedArithmetic.exteriorNorm_ge_one K S cn.2) (inv_pos.mpr hX)
  have he : exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X =
      X⁻¹ * 1 * exteriorNorm K S cn.1 * exteriorNorm K S cn.2 ^ 3 := by
    rw [HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft.exteriorNorm_completedIdeal]
    ring
  rw [he]
  simpa only [inv_inv, inverseSquare, one_pow, inv_one, mul_one] using h

/-- The scalar test may be noncompactly supported; only its quadratic tail
on the positive axis is used. The actual finite coefficient bound is proved
in ActualProbeThetaAbsolute by triangle inequality on its Gauss sum. -/
theorem norm_completedTerm_le_majorant (V : ℝ → ℂ) {B X : ℝ}
    (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ y, 0 < y → ‖V y‖ ≤ B * inverseSquare y)
    (cn : DirectIndex K S) :
    ‖completedTerm K S D θ m r Q V X cn‖ ≤ majorant K S B X cn := by
  unfold completedTerm
  dsimp only
  split_ifs
  · rw [norm_mul]
    have hcoeff :=
      HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft.norm_completedCoefficient_le_one
        K S D θ m cn.1 cn.2
    calc
      _ ≤ 1 * (B * inverseSquare
          (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X)) :=
        mul_le_mul hcoeff (htail _ (completed_argument_pos K S hX cn))
          (norm_nonneg _) zero_le_one
      _ = B * inverseSquare
          (exteriorNorm K S (completedIdeal K S cn.1 cn.2) / X) := one_mul _
      _ ≤ B * (X ^ 2 * inverseSquare (exteriorNorm K S cn.1) *
          inverseSquare (exteriorNorm K S cn.2)) :=
        mul_le_mul_of_nonneg_left (completed_argument_inverseSquare_le K S hX cn) hB
      _ = _ := by unfold majorant; ring
  · rw [norm_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hB (sq_nonneg X)) (inverseSquare_nonneg _))
      (inverseSquare_nonneg _)

theorem summable_completedTerm_of_quadratic_tail (V : ℝ → ℂ) {B X : ℝ}
    (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ y, 0 < y → ‖V y‖ ≤ B * inverseSquare y) :
    Summable (completedTerm K S D θ m r Q V X) :=
  (summable_majorant K S B X).of_norm_bounded
    (norm_completedTerm_le_majorant K S D θ m r Q V hB hX htail)

/-- Dominated convergence for the actual direct series with all masks intact.
The limit series is proved summable and is never a convergence premise. -/
theorem tendsto_completedThetaSum {T : Type*} {l : Filter T} [l.NeBot]
    (V : T → ℝ → ℂ) (V₀ : ℝ → ℂ) {B X : ℝ}
    (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ y, 0 < y → ‖V n y‖ ≤ B * inverseSquare y)
    (hlim : ∀ y, 0 < y → Tendsto (fun n => V n y) l (𝓝 (V₀ y))) :
    Summable (completedTerm K S D θ m r Q V₀ X) ∧
      Tendsto (fun n => completedThetaSum K S D θ m r Q (V n) X)
        l (𝓝 (completedThetaSum K S D θ m r Q V₀ X)) := by
  have hmajor := summable_majorant K S B X
  have hpoint (cn : DirectIndex K S) :
      Tendsto (fun n => completedTerm K S D θ m r Q (V n) X cn)
        l (𝓝 (completedTerm K S D θ m r Q V₀ X cn)) := by
    unfold completedTerm
    dsimp only
    split_ifs
    · exact tendsto_const_nhds.mul (hlim _ (completed_argument_pos K S hX cn))
    · exact tendsto_const_nhds
  have hbound : ∀ᶠ n in l, ∀ cn,
      ‖completedTerm K S D θ m r Q (V n) X cn‖ ≤ majorant K S B X cn :=
    htail.mono (fun n hn cn =>
      norm_completedTerm_le_majorant K S D θ m r Q (V n) hB hX hn cn)
  exact ⟨hmajor.of_norm_bounded (fun cn =>
    le_of_tendsto (hpoint cn).norm (hbound.mono (fun n hn => hn cn))),
    tendsto_tsum_of_dominated_convergence hmajor hpoint hbound⟩

/-- The actual Gaussian-smoothed annular test gives the literal completed
theta sum in the pointwise regularizer limit. No annular support theorem is
applied to the noncompact regularized test. -/
theorem regularized_completed_sum_tendsto (V : SmoothAnnularTest) (ε : ℕ → ℝ)
    (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) {X : ℝ} (hX : 0 < X) :
    Summable (completedTerm K S D θ m r Q V.toFun X) ∧
      Tendsto (fun n => completedThetaSum K S D θ m r Q
        (RegularizedTestProject.regularizedTest V (ε n) 0) X)
        atTop (𝓝 (completedThetaSum K S D θ m r Q V.toFun X)) := by
  obtain ⟨B, hB, htail⟩ := RegularizedTestProject.uniform_quadratic_tail V
  apply tendsto_completedThetaSum K S D θ m r Q
    (fun n => RegularizedTestProject.regularizedTest V (ε n) 0) V.toFun hB hX
  · exact Eventually.of_forall (fun n y hy => by
      have ht := htail (ε n) (hε₀ n) (hε₁ n) y hy
      simpa only [Real.rpow_neg hy.le 2, Real.rpow_two, inverseSquare] using ht)
  · intro y hy
    exact RegularizedTestProject.pointwise_tendsto V ε hε₀ hε₁ hε hy

end ThetaGlobal.PrimalLimitProject

