import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnularTerminal
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileControl

/-!
# Actual exceptional estimates uniform over a finite background family

The analytic continuation supplies each member's constants.  Finite sums
of the Euler orders and height orders, and one plus the sum of the scalar
constants, dominate every member.  Thus all choices precede the actual
background, both annular tests, the mask, the norm phase and the scales.
The empty background family is allowed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- One genuine exceptional estimate for all fixed backgrounds.  The
caller supplies no volume asymptotic, supremum bound or profile estimate. -/
theorem exists_actualAnnularExceptional_finite_family
    {β : Type*} [Fintype β]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : β → HeckeCharacter K) (hχ : ∀ k, ExceptionalNormReduced K (χ k))
    (ε B b : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∃ (J N : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (k : β) (V₁ V₂ : SmoothAnnularTest), V₁.upper ≤ b → V₂.upper ≤ b →
      ∀ (t X₁ X₂ Y₁ Y₂ T a : ℝ), 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K (χ k) R V₁.toFun t X₁ *
            heckeExceptionalSum K (χ k) R V₂.toFun t X₂ -
          heckeExceptionalSum K (χ k) R V₁.toFun t Y₁ *
            heckeExceptionalSum K (χ k) R V₂.toFun t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 *
            (1 + ‖t‖) ^ N := by
  classical
  choose J₀ N₀ C₀ hC₀ hbound using
    (fun k : β => exists_actualAnnularExceptional_equal_product_seminorm K hcomplex
      (χ k) (hχ k) ε B b hε hB hb)
  let J : ℕ := ∑ k : β, J₀ k
  let N : ℕ := ∑ k : β, N₀ k
  let C : ℝ := 1 + ∑ k : β, C₀ k
  have hsum : 0 ≤ ∑ k : β, C₀ k :=
    Finset.sum_nonneg (fun k _ => (hC₀ k).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨J, N, C, hC, ?_⟩
  intro Z hZ R hR hnorm k V₁ V₂ hu₁ hu₂
    t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hcoeff : C₀ k ≤ C := by
    have hs : C₀ k ≤ ∑ l : β, C₀ l :=
      Finset.single_le_sum (fun l _ => (hC₀ l).le) (Finset.mem_univ k)
    dsimp only [C]
    linarith
  have horder : J₀ k ≤ J :=
    Finset.single_le_sum (fun l _ => Nat.zero_le (J₀ l)) (Finset.mem_univ k)
  have hdegree : N₀ k ≤ N :=
    Finset.single_le_sum (fun l _ => Nat.zero_le (N₀ l)) (Finset.mem_univ k)
  have hseminorm :
      (testSeminorm V₁.toFun (J₀ k) 0 + testSeminorm V₂.toFun (J₀ k) 0) ^ 2 ≤
        (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 :=
    pow_le_pow_left₀
      (add_nonneg (testSeminorm_nonneg V₁.toFun (J₀ k) 0)
        (testSeminorm_nonneg V₂.toFun (J₀ k) 0))
      (add_le_add (testSeminorm_mono_order V₁.toFun 0 horder)
        (testSeminorm_mono_order V₂.toFun 0 horder)) 2
  have hheight : (1 + ‖t‖) ^ (N₀ k) ≤ (1 + ‖t‖) ^ N :=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hZn : 0 ≤ Z := zero_le_one.trans hZ
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg hZn _
  have hza : 0 ≤ Z ^ (-a) := Real.rpow_nonneg hZn _
  have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hleading : C₀ k * Z ^ ε * Real.sqrt T * Z ^ (-a) ≤
      C * Z ^ ε * Real.sqrt T * Z ^ (-a) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff hz) hsqrt) hza
  have hleading_nonneg : 0 ≤ C * Z ^ ε * Real.sqrt T * Z ^ (-a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le hz) hsqrt) hza
  have hbase : C₀ k * Z ^ ε * Real.sqrt T * Z ^ (-a) *
        (testSeminorm V₁.toFun (J₀ k) 0 + testSeminorm V₂.toFun (J₀ k) 0) ^ 2 ≤
      C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
        (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 :=
    mul_le_mul hleading hseminorm (sq_nonneg _) hleading_nonneg
  exact (hbound k Z hZ R hR hnorm V₁ V₂ hu₁ hu₂
    t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
      (mul_le_mul hbase hheight (by positivity)
        (mul_nonneg hleading_nonneg (sq_nonneg _)))

end HeckeSkeleton.Moments.MOM_PRIME

#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_actualAnnularExceptional_finite_family
