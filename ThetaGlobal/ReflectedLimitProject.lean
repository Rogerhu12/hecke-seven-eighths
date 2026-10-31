import ThetaGlobal.ReflectedAbsoluteProject
import ThetaGlobal.RegularizedKernelProject
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Regularizer removal for the project's literal reflected ideal series

This project adapter keeps the actual ReflectionIndex and actual arithmetic
prefactor. Its convergence majorant is proved from the finite Weyl sums and
the actual ideal-counting result. The final theorem applies the actual
regularized Mellin kernel and concludes convergence to the literal
reflectedTerm sum, with no theta reflection or fixed-profile seed premise.

This file requires the original project's vendored dependencies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedLimitProject

open NumberField IsDedekindDomain MeasureTheory Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedArithmetic
open ThetaGlobal.ReflectedAbsoluteProject
open scoped Classical BigOperators Topology nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S) (θ : HeckeCharacter K)

def argument (X : ℝ) (i : ReflectionIndex K S d) : ℝ :=
  X * exteriorNorm K S i.numeratorFrozen * exteriorNorm K S i.c *
    exteriorNorm K S i.n ^ 3 /
    (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
      exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2

theorem argument_pos {X : ℝ} (hX : 0 < X) (i : ReflectionIndex K S d) :
    0 < argument K S d X i := by
  exact div_pos
    (mul_pos (mul_pos (mul_pos hX (ReflectedArithmetic.exteriorNorm_pos K S _))
      (ReflectedArithmetic.exteriorNorm_pos K S _))
      (pow_pos (ReflectedArithmetic.exteriorNorm_pos K S _) _))
    (sq_pos_of_pos (mul_pos
      (mul_pos (ReflectedArithmetic.exteriorNorm_pos K S _)
        (ReflectedArithmetic.exteriorNorm_pos K S _))
      (ReflectedArithmetic.exteriorNorm_pos K S _)))

def term (kernel : SixthLocalClasses K S → ℝ → ℂ) (X : ℝ)
    (i : ReflectionIndex K S d) : ℂ :=
  reflectedCoefficient K S D d i θ *
    kernel (frequencyClass K S D d i) (argument K S d X i)

theorem term_eq_reflectedTerm (F : FiniteMellinData K S) (V : ℝ → ℂ)
    (X : ℝ) (i : ReflectionIndex K S d) :
    term K S D d θ
      (fun κ y => mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit) κ V 0 y)
      X i = reflectedTerm K S D d i F θ V X := by
  rfl

theorem summable_term_of_quadratic_tail
    (kernel : SixthLocalClasses K S → ℝ → ℂ) {B X : ℝ}
    (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ κ y, 0 < y → ‖kernel κ y‖ ≤ B * inverseSquare y) :
    Summable (term K S D d θ kernel X) := by
  have h := summable_reflected_of_quadratic_tail
    (exteriorNorm K S) (ReflectedArithmetic.exteriorNorm_ge_one K S)
    (summable_exterior_inverseSquare K S)
    (reflectionEncode K S d) (reflectionEncode_injective K S d)
    (frequencyClass K S D d) (branchScale K S d X) (branchArithmeticBound K S D d)
    (branchScale_pos K S d hX) (branchArithmeticBound_nonneg K S D d)
    (fun i => reflectedCoefficient K S D d i θ)
    (fun i => norm_reflectedCoefficient_le K S D d i θ) kernel B hB htail
  apply h.congr
  intro i
  unfold term
  congr 1
  congr 1
  simp only [argument, branchScale, reflectionEncode, activeFrozenIdeal, activeMarkedIdeal,
    div_eq_mul_inv]
  ring

def majorant (B X : ℝ) (i : ReflectionIndex K S d) : ℝ :=
  ‖reflectedCoefficient K S D d i θ‖ * B * inverseSquare (argument K S d X i)

theorem summable_majorant {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X) :
    Summable (majorant K S D d θ B X) := by
  let kernel : SixthLocalClasses K S → ℝ → ℂ :=
    fun _ y => ((B * inverseSquare y : ℝ) : ℂ)
  have htail : ∀ κ y, 0 < y → ‖kernel κ y‖ ≤ B * inverseSquare y := by
    intro κ y _
    change ‖((B * inverseSquare y : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg y))]
  have h := summable_term_of_quadratic_tail K S D d θ kernel hB hX htail
  apply h.norm.congr
  intro i
  change ‖reflectedCoefficient K S D d i θ *
    ((B * inverseSquare (argument K S d X i) : ℝ) : ℂ)‖ =
    ‖reflectedCoefficient K S D d i θ‖ * B * inverseSquare (argument K S d X i)
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg _))]
  ring

theorem norm_term_le_majorant
    (kernel : SixthLocalClasses K S → ℝ → ℂ) {B X : ℝ} (hX : 0 < X)
    (htail : ∀ κ y, 0 < y → ‖kernel κ y‖ ≤ B * inverseSquare y)
    (i : ReflectionIndex K S d) :
    ‖term K S D d θ kernel X i‖ ≤ majorant K S D d θ B X i := by
  unfold term majorant
  rw [norm_mul]
  calc
    _ ≤ ‖reflectedCoefficient K S D d i θ‖ *
        (B * inverseSquare (argument K S d X i)) :=
      mul_le_mul_of_nonneg_left (htail _ _ (argument_pos K S d hX i)) (norm_nonneg _)
    _ = _ := by ring

/-- Uniform quadratic tails and pointwise scalar limits pass through the
actual reflected series. No convergence or coefficient bound is assumed. -/
theorem tendsto_tsum_actual {T : Type*} {l : Filter T} [l.NeBot]
    (kernel : T → SixthLocalClasses K S → ℝ → ℂ)
    (kernel₀ : SixthLocalClasses K S → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ κ y, 0 < y →
      ‖kernel n κ y‖ ≤ B * inverseSquare y)
    (hlim : ∀ κ y, 0 < y →
      Tendsto (fun n => kernel n κ y) l (𝓝 (kernel₀ κ y))) :
    Summable (term K S D d θ kernel₀ X) ∧
      Tendsto (fun n => ∑' i, term K S D d θ (kernel n) X i)
        l (𝓝 (∑' i, term K S D d θ kernel₀ X i)) := by
  have hmajor := summable_majorant K S D d θ hB hX
  have hpoint (i : ReflectionIndex K S d) :
      Tendsto (fun n => term K S D d θ (kernel n) X i)
        l (𝓝 (term K S D d θ kernel₀ X i)) :=
    tendsto_const_nhds.mul (hlim _ _ (argument_pos K S d hX i))
  have hbound : ∀ᶠ n in l, ∀ i,
      ‖term K S D d θ (kernel n) X i‖ ≤ majorant K S D d θ B X i :=
    htail.mono (fun n hn i => norm_term_le_majorant K S D d θ (kernel n) hX hn i)
  exact ⟨hmajor.of_norm_bounded (fun i =>
    le_of_tendsto (hpoint i).norm (hbound.mono (fun n hn => hn i))),
    tendsto_tsum_of_dominated_convergence hmajor hpoint hbound⟩

/-- The full regularizer limit for the literal project series. Finite local
power classes are required only to take a common scalar kernel constant.
FiniteMellinAdmissible is the existing local cutoff/decay/Mellin property. -/
theorem regularized_reflected_sum_tendsto [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (V : SmoothAnnularTest) (ε : ℕ → ℝ)
    (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) {X : ℝ} (hX : 0 < X) :
    Summable (fun i => reflectedTerm K S D d i F θ V.toFun X) ∧
      Tendsto
        (fun n => ∑' i, term K S D d θ
          (fun κ y => RegularizedKernelProject.regularizedKernel F θ
            (QuotientGroup.mk d.rowUnit) κ V (ε n) 0 y) X i)
        atTop (𝓝 (∑' i, reflectedTerm K S D d i F θ V.toFun X)) := by
  obtain ⟨B, hB, htail⟩ := RegularizedKernelProject.uniform_quadratic_tail
    F θ hF (QuotientGroup.mk d.rowUnit) V
  have h := tendsto_tsum_actual K S D d θ
    (fun n κ y => RegularizedKernelProject.regularizedKernel F θ
      (QuotientGroup.mk d.rowUnit) κ V (ε n) 0 y)
    (fun κ y => mellinReflectionKernel K S F θ
      (QuotientGroup.mk d.rowUnit) κ V.toFun 0 y) hB hX
    (Eventually.of_forall (fun n κ y hy => by
      have ht := htail (ε n) (hε₀ n) (hε₁ n) κ y hy
      simpa only [Real.rpow_neg hy.le 2, Real.rpow_two, inverseSquare] using ht))
    (fun κ y hy => RegularizedKernelProject.regularizedKernel_tendsto F θ hF
      (QuotientGroup.mk d.rowUnit) κ V ε hε₀ hε₁ hε hy)
  constructor
  · exact h.1.congr (fun i => term_eq_reflectedTerm K S D d θ F V.toFun X i)
  · simpa only [term_eq_reflectedTerm] using h.2

end ThetaGlobal.ReflectedLimitProject

