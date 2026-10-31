import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalAnnularTerminal
import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalNormReduction

/-!
# Actual exceptional cancellation for the original finite polynomials

The analytic residue and remainder are constructed before this bridge.
Only identities of the original summands are supplied here: the fixed
background, the complete common mask, and the two actual annular profiles.
The same norm phase and both equal products survive the normalization.
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

/-- The actual Lemma 4.11 producer applies to the literal finite plain
polynomials, uniformly before the model, mask, tests, and four lengths.
The profile size is the repository's original Euler `testSeminorm`.
There is no volume, remainder, or centered-energy hypothesis. -/
theorem plainPolynomial_actual_exceptional_equal_product
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ExceptionalNormReduced K χ)
    (ε B b : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    ∃ (J N : ℕ) (C : ℝ), 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K)
        (V₁ V₂ : SmoothAnnularTest) (t τ X₁ X₂ Y₁ Y₂ T a : ℝ),
        d.plainBackground * d.rowCharacter u = χ →
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
    exists_actualAnnularExceptional_equal_product_seminorm K hcomplex χ hχ ε B b hε hB hb
  refine ⟨J, N, C, hC, ?_⟩
  intro Z hZ R hR hRnorm ω ψ d W₁ W₂ u V₁ V₂ t τ X₁ X₂ Y₁ Y₂ T a
    hcharacter hmask hprofile₁ hprofile₂ hupper₁ hupper₂ ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hL : 0 < Z ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  rw [plainPolynomial_exceptional_rectangle_norm K d W₁ W₂ u R
    V₁.toFun V₂.toFun t τ X₁ X₂ Y₁ Y₂ T
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)
    hpX hpY hmask hprofile₁ hprofile₂, hcharacter]
  exact hbound Z hZ R hR hRnorm V₁ V₂ hupper₁ hupper₂
    t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY

end HeckeSkeleton.Moments.MOM_PRIME
