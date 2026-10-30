import HeckePort.Moments.Height

/-!
# Rectangle sums over pairs of ideals

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Rectangle.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`.  The coefficient `primaryIdealCharacter c χ` is the abstract
multiplicative `Ψ : Ideal (𝓞 K) →* ℂ`; the summability input is
`CenteredMomentMask.annular_ideal_sum_summable`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckePort.CenteredMomentMask HeckePort.Moments.Twist

variable {K : Type*} [Field K] [NumberField K]

def idealWeight (Ψ : Ideal (𝓞 K) → ℂ) (R : Ideal (𝓞 K)) (t : ℝ) (I : Ideal (𝓞 K)) : ℂ :=
  (if IsCoprime I R then (1 : ℂ) else 0) * Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

theorem idealWeight_mul (Ψ : Ideal (𝓞 K) →* ℂ) (R : Ideal (𝓞 K)) (t : ℝ)
    (I J : Ideal (𝓞 K)) :
    idealWeight Ψ R t (I * J) = idealWeight Ψ R t I * idealWeight Ψ R t J := by
  have hpow : ((Ideal.absNorm I : ℂ) * (Ideal.absNorm J : ℂ)) ^ (Complex.I * t) =
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * (Ideal.absNorm J : ℂ) ^ (Complex.I * t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I) : (0 : ℝ) ≤ Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J) : (0 : ℝ) ≤ Ideal.absNorm J) (Complex.I * t)
  simp only [idealWeight, map_mul, Nat.cast_mul, hpow, IsCoprime.mul_left_iff]
  by_cases hI : IsCoprime I R <;> by_cases hJ : IsCoprime J R <;> simp [hI, hJ] <;> ring

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal (𝓞 K)) : ℂ :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

theorem twistedMaskedSum_eq_weight (Ψ : Ideal (𝓞 K) → ℂ) (R : Ideal (𝓞 K)) (t : ℝ)
    (W : ℝ → ℂ) (X : ℝ) :
    twistedMaskedSum Ψ R W t X =
      ∑' I : Ideal (𝓞 K), idealWeight Ψ R t I * W ((Ideal.absNorm I : ℝ) / X) := by
  apply tsum_congr
  intro I
  unfold idealWeight
  ring

theorem actual_rectangle_sum
    (Ψ : Ideal (𝓞 K) →* ℂ) (R : Ideal (𝓞 K)) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal (𝓞 K), ∑' J : Ideal (𝓞 K),
      idealWeight Ψ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂ -
        twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂ := by
  let w := idealWeight Ψ R t
  let f₁ := fun I : Ideal (𝓞 K) => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal (𝓞 K) => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal (𝓞 K) => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal (𝓞 K) => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal (𝓞 K)) :
      idealWeight Ψ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [idealWeight_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal (𝓞 K)) : (∑' J : Ideal (𝓞 K), (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal (𝓞 K), f₂ J) - g₁ I * (∑' J : Ideal (𝓞 K), g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [twistedMaskedSum_eq_weight]
  rfl

end HeckePort.Moments

end
