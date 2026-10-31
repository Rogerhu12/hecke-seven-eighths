import HeckeSkeleton.Moments.MOM_PRIME.ActualExceptionalMomentBridge
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnularFiniteFamily

/-!
# Uniform exceptional cancellation on the original polynomial family

The finite set of fixed Hecke backgrounds determines one Euler order,
one height order and one scalar before the row, the model, both original
tests and all four physical lengths.  The bridge preserves the exact
common mask and the whole norm phase of the original finite polynomials.

The canonical specialization normalizes one fixed background radially
and then permits every finite-order twist in the chosen finite family.
Its norm-reduction certificates are proved by the character API.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The actual finite-background estimate transferred to the literal
source polynomials.  All constants precede the family member, row and
annular tests; character and mask hypotheses identify original summands. -/
theorem plainPolynomial_actual_exceptional_finite_family
    {β : Type*} [Fintype β]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : β → HeckeCharacter K) (hχ : ∀ k, ExceptionalNormReduced K (χ k))
    (ε B b : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∃ (J N : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (k : β) {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K)
        (V₁ V₂ : SmoothAnnularTest) (t τ X₁ X₂ Y₁ Y₂ T a : ℝ),
        d.plainBackground * d.rowCharacter u = χ k →
        (∀ I : NonzeroIdeal K,
          maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0) →
        (∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₁.toFun y) →
        (∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₂.toFun y) →
        V₁.upper ≤ b → V₂.upper ≤ b →
        0 ≤ a → Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
        X₁ * X₂ = T → Y₁ * Y₂ = T →
        ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
            plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ ≤
          C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
            (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 *
              (1 + ‖t‖) ^ N := by
  obtain ⟨J, N, C, hC, hbound⟩ :=
    exists_actualAnnularExceptional_finite_family K hcomplex χ hχ ε B b hε hB hb
  refine ⟨J, N, C, hC, ?_⟩
  intro Z hZ R hR hRnorm k ω ψ d W₁ W₂ u V₁ V₂ t τ X₁ X₂ Y₁ Y₂ T a
    hcharacter hmask hprofile₁ hprofile₂ hupper₁ hupper₂ ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hL : 0 < Z ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  rw [plainPolynomial_exceptional_rectangle_norm K d W₁ W₂ u R
    V₁.toFun V₂.toFun t τ X₁ X₂ Y₁ Y₂ T
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)
    hpX hpY hmask hprofile₁ hprofile₂, hcharacter]
  exact hbound Z hZ R hR hRnorm k V₁ V₂ hupper₁ hupper₂
    t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY

/-- The manuscript's fixed normalized background and finite-order twist
family supply their own norm-reduction certificates.  The resulting
constant is uniform in the selected background and every original row. -/
theorem plainPolynomial_actual_exceptional_normalized_finite_background
    {β : Type*} [Fintype β]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (w : InfinitePlace K) (ω₀ : HeckeCharacter K)
    (θ : β → HeckeCharacter K) (hθ : ∀ k, FiniteOrder (θ k))
    (ε B b : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∃ (J N : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (k : β) {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K)
        (V₁ V₂ : SmoothAnnularTest) (t τ X₁ X₂ Y₁ Y₂ T a : ℝ),
        d.plainBackground * d.rowCharacter u = radialNormalization K w ω₀ * θ k →
        (∀ I : NonzeroIdeal K,
          maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0) →
        (∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₁.toFun y) →
        (∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₂.toFun y) →
        V₁.upper ≤ b → V₂.upper ≤ b →
        0 ≤ a → Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
        X₁ * X₂ = T → Y₁ * Y₂ = T →
        ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
            plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ ≤
          C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
            (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 *
              (1 + ‖t‖) ^ N := by
  exact plainPolynomial_actual_exceptional_finite_family K hcomplex
    (fun k => radialNormalization K w ω₀ * θ k)
    (fun k => exceptionalNormReduced_normalized_finite_background K w ω₀ (θ k) (hθ k))
    ε B b hε hB hb

/-- The companion absolute estimate for the same original polynomials.
It is uniform on the fixed annulus at every positive scale, including
subunit scales, with no lower-length or character-reduction hypothesis. -/
theorem plainPolynomial_actual_exceptional_fallback_seminorm
    (J : ℕ) (hJ : 2 ≤ J) (b : ℝ) (hb : 0 ≤ b)
    {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K) (R : Ideal (𝓞 K))
    (V₁ V₂ : SmoothAnnularTest) (hupper₁ : V₁.upper ≤ b) (hupper₂ : V₂.upper ≤ b)
    (t τ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = T) (hpY : Y₁ * Y₂ = T)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile₁ : ∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₁.toFun y)
    (hprofile₂ : ∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * V₂.toFun y) :
    ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
        plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ ≤
      2 * (HeckePort.CenteredMomentCounting.idealCountConstant K * b *
          (8 * annularContourMass)) ^ 2 * Real.sqrt T *
        (testSeminorm V₁.toFun J 0 + testSeminorm V₂.toFun J 0) ^ 2 := by
  let M₁ : ℝ := 8 * annularContourMass * testSeminorm V₁.toFun J 0
  let M₂ : ℝ := 8 * annularContourMass * testSeminorm V₂.toFun J 0
  have hM₁ : 0 ≤ M₁ := mul_nonneg
    (mul_nonneg (by norm_num) annularContourMass_nonneg)
    (HeckeSkeleton.Moments.UniformAmplify.testSeminorm_nonneg V₁.toFun J 0)
  have hM₂ : 0 ≤ M₂ := mul_nonneg
    (mul_nonneg (by norm_num) annularContourMass_nonneg)
    (HeckeSkeleton.Moments.UniformAmplify.testSeminorm_nonneg V₂.toFun J 0)
  have hsup₁ : ∀ y, ‖V₁.toFun y‖ ≤ M₁ :=
    smoothAnnular_norm_le_testSeminorm V₁ J hJ
  have hsup₂ : ∀ y, ‖V₂.toFun y‖ ≤ M₂ :=
    smoothAnnular_norm_le_testSeminorm V₂ J hJ
  calc
    _ ≤ 2 * (HeckePort.CenteredMomentCounting.idealCountConstant K *
        (b * M₁ + b * M₂)) ^ 2 * Real.sqrt T :=
      plainPolynomial_exceptional_fallback K d W₁ W₂ u R V₁.toFun V₂.toFun
        b b M₁ M₂ hb hb hM₁ hM₂ hsup₁ hsup₂
        (fun _ hy => (V₁.support hy).2.trans hupper₁)
        (fun _ hy => (V₂.support hy).2.trans hupper₂)
        t τ X₁ X₂ Y₁ Y₂ T hX₁ hX₂ hY₁ hY₂ hpX hpY hmask hprofile₁ hprofile₂
    _ = _ := by dsimp only [M₁, M₂]; ring

end HeckeSkeleton.Moments.MOM_PRIME

#print axioms HeckeSkeleton.Moments.MOM_PRIME.plainPolynomial_actual_exceptional_finite_family
#print axioms HeckeSkeleton.Moments.MOM_PRIME.plainPolynomial_actual_exceptional_normalized_finite_background
#print axioms HeckeSkeleton.Moments.MOM_PRIME.plainPolynomial_actual_exceptional_fallback_seminorm
