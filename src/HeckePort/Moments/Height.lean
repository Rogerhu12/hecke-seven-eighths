import HeckePort.Moments.Twist

/-!
# Polynomial height dependence of the twisted rectangle estimate

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Height.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`, on top of `Moments/Twist`.

openai bounds the error `V.error (normPowerProfile W a b ha hs hW t)` by `C (1 + ‖t / (2π)‖) ^ n`
via `normPowerProfile_uniform_degree` (the Schwartz seminorms of the norm-power profile grow
polynomially in the height, a statement about `CompletedHeight.uniformTwistedSchwartz`) and the
`pvControl` seminorm bound of the `ℤ[ω]` lattice volume estimate.  Both enter here as the
explicit hypothesis `herr` on the error functional of the `IdealVolumeInput` `V`
(polynomial growth in `t`, with `t` indexing the profile `prof t = x ^ (I t) W x` directly, so
that the normalization `normalized_height_le` is not needed in the estimate; it is kept).  The
uniform bound `M` on `W` (openai: the sup seminorm of `prof 0`) is likewise a datum.
The divisor-count part is `HeckePort.CenteredMomentMask.polynomial_mask_divisor_bound`.
The constant `128` is `idealCountConstant K`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators SchwartzMap
open HeckePort.CenteredMomentCancellation HeckePort.CenteredMomentCounting
open HeckePort.CenteredMomentVolume HeckePort.CenteredMomentMask HeckePort.Moments.Twist

variable {K : Type*} [Field K] [NumberField K]

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

/-- openai `maskedError_polynomial_height`, for an error functional of polynomial growth. -/
theorem maskedError_polynomial_height {Ψ : Ideal (𝓞 K) → ℂ} (V : IdealVolumeInput K Ψ)
    (prof : ℝ → 𝓢(ℝ, ℂ)) (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (n : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (herr : ∀ t : ℝ, V.error (prof t) ≤ C₀ * (1 + ‖t‖) ^ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, maskedError V R (prof t) ≤ C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound (K := K) ε B hε hB
  refine ⟨1 + D * C₀, by positivity, ?_⟩
  intro Z hZ R hR hnorm t
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hpow : 0 ≤ (1 + ‖t‖) ^ n := by positivity
  have herr' : maskedError V R (prof t) ≤ (D * Z ^ ε) * (C₀ * (1 + ‖t‖) ^ n) := by
    unfold maskedError
    exact mul_le_mul (hdiv Z hZ R hR hnorm) (herr t) (V.error_nonneg _)
      (mul_nonneg hD.le hz)
  calc
    _ ≤ (D * Z ^ ε) * (C₀ * (1 + ‖t‖) ^ n) := herr'
    _ = (D * C₀) * Z ^ ε * (1 + ‖t‖) ^ n := by ring
    _ ≤ (1 + D * C₀) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hz) hpow

/-- openai `normalized_masked_rectangle_estimate`. -/
theorem normalized_masked_rectangle_estimate {Ψ : Ideal (𝓞 K) →* ℂ} (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (hΨ0 : Ψ ⊥ = 0) (V : IdealVolumeInput K Ψ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hε : 0 < ε) (hB : 0 ≤ B)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁) (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (prof₁ prof₂ : ℝ → 𝓢(ℝ, ℂ))
    (hprof₁ : ∀ t x, prof₁ t x = (x : ℂ) ^ (Complex.I * t) * W₁ x)
    (hprof₂ : ∀ t x, prof₂ t x = (x : ℂ) ^ (Complex.I * t) * W₂ x)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (n₁ n₂ : ℕ) (D₁ D₂ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (herr₁ : ∀ t : ℝ, V.error (prof₁ t) ≤ D₁ * (1 + ‖t‖) ^ n₁)
    (herr₂ : ∀ t : ℝ, V.error (prof₂ t) ≤ D₂ * (1 + ‖t‖) ^ n₂) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂ -
          twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨E₁, hE₁, hen₁⟩ := maskedError_polynomial_height V prof₁ ε B hε hB n₁ D₁ hD₁ herr₁
  obtain ⟨E₂, hE₂, hen₂⟩ := maskedError_polynomial_height V prof₂ ε B hε hB n₂ D₂ hD₂ herr₂
  have hc0 : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  refine ⟨max n₁ n₂, ?_⟩
  let Vc := idealCountConstant K * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ Vc := mul_nonneg hc0 (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (E₁ + E₂) * Vc
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := maskedError V R (prof₁ t) + maskedError V R (prof₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (E₁ + E₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (hen₁ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hE₁.le hz))
    have h₂ := (hen₂ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hE₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := twisted_rectangle_saving hΨ hΨ0 V R hR W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ prof₁ prof₂ hprof₁ hprof₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := HeckePort.CenteredMoment.normalized_centered_saving _ T L Vc E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * Vc * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((E₁ + E₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * Vc *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (E₁ + E₂) * Vc) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

end HeckePort.Moments

end
