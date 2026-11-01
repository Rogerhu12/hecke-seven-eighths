import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalHecke
import HeckeGeneral.Analysis.MomentInputs

/-!
# The exceptional terminal on the actual finite plain polynomials

The source polynomials and the exceptional ideal sums use the same genuine
Hecke coefficients. This file identifies them using `IdealTest.support_spec`
and the unchanged common coprimality mask. The norm phase is retained in
the exact identity, then cancels from the norm of an equal-product rectangle.

The final theorem transfers the uniform exceptional estimate to the literal
`plainPolynomial` of `MomentData`. Its analytic volume/profile input stays
explicit. No finite-sum estimate or centered rectangle bound is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.CenteredMomentVolume HeckePort.Moments.Twist
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The exact support certificate changes only the notation of the finite
plain sum. No smoothness, boundedness, or scale assumption is needed. -/
theorem plainPolynomial_eq_tsum {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K) (u : NonzeroIdeal K) (X t : ℝ) :
    plainPolynomial d W u X t =
      (Real.sqrt X : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
        heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
          W.profile u t (idealNorm K I / X) * maskValue d u I.val := by
  unfold plainPolynomial
  congr 1
  symm
  apply tsum_eq_sum
  intro I hI
  have hw : W.profile u t (idealNorm K I / X) = 0 := by
    by_contra hn
    exact hI ((W.support_spec u t X I).mpr hn)
  simp only [hw, mul_zero, zero_mul]

/-- Removing the zero ideal gives exactly the nonzero ideal indexing used
by `plainPolynomial`; the zero coefficient makes the discarded term zero. -/
theorem heckeExceptionalSum_eq_nonzero_tsum (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (t X : ℝ) :
    heckeExceptionalSum K χ R W t X =
      ∑' I : NonzeroIdeal K,
        (if IsCoprime I.val R then (1 : ℂ) else 0) *
          (heckeIdealCoefficient K χ I * (idealNorm K I : ℂ) ^ (Complex.I * t) *
            W (idealNorm K I / X)) := by
  let f : Ideal (𝓞 K) → ℂ := fun I =>
    (if IsCoprime I R then (1 : ℂ) else 0) *
      (heckeExceptionalCharacter K χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
        W ((Ideal.absNorm I : ℝ) / X))
  have hv : Function.Injective (fun I : NonzeroIdeal K => I.val) := Subtype.val_injective
  have hs : Function.support f ⊆ Set.range (fun I : NonzeroIdeal K => I.val) := by
    intro I hI
    have hI0 : I ≠ ⊥ := by
      intro he
      apply hI
      simp only [f, he, heckeExceptionalCharacter_zero, zero_mul, mul_zero]
    exact ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, rfl⟩
  calc
    _ = ∑' I : Ideal (𝓞 K), f I := rfl
    _ = ∑' I : NonzeroIdeal K, f I.val := (hv.tsum_eq hs).symm
    _ = _ := by
      apply tsum_congr
      intro I
      simp only [f, heckeExceptionalCharacter_nonzero, idealNorm, Complex.ofReal_natCast]

/-- Exact phase-preserving bridge to the source's normalized finite plain
polynomial. The actual test parameter `τ` is independent of the norm phase `t`.
The mask equality is an identification of actual summands. -/
theorem plainPolynomial_norm_phase_bridge {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K) (u : NonzeroIdeal K)
    (R : Ideal (𝓞 K)) (w : ℝ → ℂ) (t τ X : ℝ) (hX : 0 < X)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile : ∀ y, W.profile u τ y = (y : ℂ) ^ (Complex.I * t) * w y) :
    (Real.sqrt X : ℂ)⁻¹ *
        heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w t X =
      (X : ℂ) ^ (Complex.I * t) * plainPolynomial d W u X τ := by
  have hphase (I : NonzeroIdeal K) :
      (idealNorm K I : ℂ) ^ (Complex.I * t) =
        (X : ℂ) ^ (Complex.I * t) *
          ((idealNorm K I / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (idealNorm_pos K I).le hX.le) (Complex.I * t)
    have heq : X * (idealNorm K I / X) = idealNorm K I := by field_simp
    rw [← Complex.ofReal_mul, heq] at h
    exact h
  have hsum :
      (∑' I : NonzeroIdeal K,
        (if IsCoprime I.val R then (1 : ℂ) else 0) *
          (heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
            (idealNorm K I : ℂ) ^ (Complex.I * t) * w (idealNorm K I / X))) =
        (X : ℂ) ^ (Complex.I * t) * ∑' I : NonzeroIdeal K,
          heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
            W.profile u τ (idealNorm K I / X) * maskValue d u I.val := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro I
    rw [hprofile, hmask, hphase]
    ring
  rw [heckeExceptionalSum_eq_nonzero_tsum, plainPolynomial_eq_tsum, hsum]
  ring

/-- The untwisted specialization identifies exactly the finite polynomial
with the normalized exceptional sum, including all original zeros. -/
theorem plainPolynomial_exceptional_bridge {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K) (u : NonzeroIdeal K)
    (R : Ideal (𝓞 K)) (w : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile : ∀ y, W.profile u 0 y = w y) :
    (Real.sqrt X : ℂ)⁻¹ *
        heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w 0 X =
      plainPolynomial d W u X 0 := by
  have hp : ∀ y, W.profile u 0 y = (y : ℂ) ^ (Complex.I * (0 : ℝ)) * w y := by
    intro y
    simpa only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, one_mul] using hprofile y
  simpa only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, one_mul] using
    plainPolynomial_norm_phase_bridge K d W u R w 0 0 X hX hmask hp

/-- The four source polynomials have the same whole norm phase, because
both products of scales equal `T`. Their centered norm is the exact norm
of the normalized exceptional rectangle. -/
theorem plainPolynomial_exceptional_rectangle_norm {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K)
    (R : Ideal (𝓞 K)) (w₁ w₂ : ℝ → ℂ) (t τ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = T) (hpY : Y₁ * Y₂ = T)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile₁ : ∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * w₁ y)
    (hprofile₂ : ∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * w₂ y) :
    ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
        plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ =
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t X₁ *
            heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t X₂ -
          heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t Y₁ *
            heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t Y₂)‖ := by
  have hT : 0 < T := hpX ▸ mul_pos hX₁ hX₂
  have hpair (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (hp : X * Y = T) :
      (Real.sqrt T : ℂ)⁻¹ *
          (heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t X *
            heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t Y) =
        (T : ℂ) ^ (Complex.I * t) *
          (plainPolynomial d W₁ u X τ * plainPolynomial d W₂ u Y τ) := by
    have hsqrt : (Real.sqrt T : ℂ) = (Real.sqrt X : ℂ) * (Real.sqrt Y : ℂ) := by
      rw [← hp, Real.sqrt_mul hX.le, Complex.ofReal_mul]
    have hphase : (X : ℂ) ^ (Complex.I * t) * (Y : ℂ) ^ (Complex.I * t) =
        (T : ℂ) ^ (Complex.I * t) := by
      rw [← Complex.mul_cpow_ofReal_nonneg hX.le hY.le, ← Complex.ofReal_mul, hp]
    calc
      _ = ((Real.sqrt X : ℂ)⁻¹ *
          heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t X) *
          ((Real.sqrt Y : ℂ)⁻¹ *
            heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t Y) := by
        rw [hsqrt, mul_inv_rev]
        ring
      _ = ((X : ℂ) ^ (Complex.I * t) * plainPolynomial d W₁ u X τ) *
          ((Y : ℂ) ^ (Complex.I * t) * plainPolynomial d W₂ u Y τ) := by
        rw [plainPolynomial_norm_phase_bridge K d W₁ u R w₁ t τ X hX hmask hprofile₁,
          plainPolynomial_norm_phase_bridge K d W₂ u R w₂ t τ Y hY hmask hprofile₂]
      _ = ((X : ℂ) ^ (Complex.I * t) * (Y : ℂ) ^ (Complex.I * t)) *
          (plainPolynomial d W₁ u X τ * plainPolynomial d W₂ u Y τ) := by ring
      _ = _ := by rw [hphase]
  have heq : (Real.sqrt T : ℂ)⁻¹ *
      (heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t X₁ *
          heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t X₂ -
        heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₁ t Y₁ *
          heckeExceptionalSum K (d.plainBackground * d.rowCharacter u) R w₂ t Y₂) =
      (T : ℂ) ^ (Complex.I * t) *
        (plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
          plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ) := by
    rw [mul_sub, hpair X₁ X₂ hX₁ hX₂ hpX, hpair Y₁ Y₂ hY₁ hY₂ hpY, mul_sub]
  symm
  rw [heq, norm_mul, norm_real_imaginary_power T t hT, one_mul]

/-- The actual finite-polynomial fallback has no analytic volume premise
and no lower length. The four positive scales may lie below one. -/
theorem plainPolynomial_exceptional_fallback {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K)
    (R : Ideal (𝓞 K)) (w₁ w₂ : ℝ → ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ y, ‖w₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖w₂ y‖ ≤ M₂)
    (hs₁ : Function.support w₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support w₂ ⊆ Set.Iic b₂)
    (t τ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = T) (hpY : Y₁ * Y₂ = T)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile₁ : ∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * w₁ y)
    (hprofile₂ : ∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * w₂ y) :
    ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
        plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ ≤
      2 * (HeckePort.CenteredMomentCounting.idealCountConstant K *
        (b₁ * M₁ + b₂ * M₂)) ^ 2 * Real.sqrt T := by
  rw [plainPolynomial_exceptional_rectangle_norm K d W₁ W₂ u R w₁ w₂ t τ
    X₁ X₂ Y₁ Y₂ T hX₁ hX₂ hY₁ hY₂ hpX hpY hmask hprofile₁ hprofile₂]
  exact exceptional_normalized_fallback
    (heckeExceptionalCharacter K (d.plainBackground * d.rowCharacter u))
    (norm_heckeExceptionalCharacter_le_one K (d.plainBackground * d.rowCharacter u))
    (heckeExceptionalCharacter_zero K (d.plainBackground * d.rowCharacter u))
    R w₁ w₂ b₁ b₂ M₁ M₂ hb₁ hb₂ hM₁ hM₂ hbound₁ hbound₂ hs₁ hs₂
    t X₁ X₂ Y₁ Y₂ T hX₁ hX₂ hY₁ hY₂ hpX hpY

/-- Uniform exceptional cancellation for the literal finite plain
polynomials. The fixed actual character and analytic profile family precede
the constant; all model data, same-mask identifications, and four scales
are chosen afterwards. -/
theorem plainPolynomial_exceptional_equal_product {ι : Type*} (χ : HeckeCharacter K)
    (V : IdealVolumeInput K (heckeExceptionalCharacter K χ))
    (F : ExceptionalProfiles V ι) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
        (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K) (i j : ι)
        (t τ X₁ X₂ Y₁ Y₂ T a : ℝ),
        d.plainBackground * d.rowCharacter u = χ →
        (∀ I : NonzeroIdeal K,
          maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0) →
        (∀ y, W₁.profile u τ y = (y : ℂ) ^ (Complex.I * t) * F.weight i y) →
        (∀ y, W₂.profile u τ y = (y : ℂ) ^ (Complex.I * t) * F.weight j y) →
        0 ≤ a → Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
        X₁ * X₂ = T → Y₁ * Y₂ = T →
        ‖plainPolynomial d W₁ u X₁ τ * plainPolynomial d W₂ u X₂ τ -
            plainPolynomial d W₁ u Y₁ τ * plainPolynomial d W₂ u Y₂ τ‖ ≤
          C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
            (F.seminorm i + F.seminorm j) ^ 2 * (1 + ‖t‖) ^ F.order := by
  obtain ⟨C, hC, hbound⟩ := hecke_exceptional_equal_product χ V F ε B hε hB
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm ω ψ d W₁ W₂ u i j t τ X₁ X₂ Y₁ Y₂ T a hχ hmask
    hprofile₁ hprofile₂ ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hL : 0 < Z ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  rw [plainPolynomial_exceptional_rectangle_norm K d W₁ W₂ u R
    (F.weight i) (F.weight j) t τ X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
    (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY hmask hprofile₁ hprofile₂, hχ]
  exact hbound Z hZ R hR hnorm i j t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY

end HeckeSkeleton.Moments.MOM_PRIME
