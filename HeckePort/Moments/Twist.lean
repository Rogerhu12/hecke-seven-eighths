import HeckePort.CenteredMoment.Counting

/-!
# Norm-twisted masked sums

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Twist.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`, on top of the abstract masked sums of `CenteredMoment.Cancellation`.

Changes:
* The coefficient `primaryIdealCharacter c χ` is the abstract multiplicative `Ψ : Ideal (𝓞 K) →* ℂ`
  with `‖Ψ I‖ ≤ 1` and `Ψ ⊥ = 0`; the volume asymptotic is the `IdealVolumeInput` of the pilot
  (`density` replaces `paperRadialFourier · 0`, the factor `maskedDensity` of openai is
  `maskedDensity Ψ R`).
* The norm-power profile `normPowerProfile W a b ha hs hW t` (openai `Moments/Lattice`, the
  Schwartz function `x ↦ x ^ (I t) W x`, built from `CompletedHeight.uniformTwistedSchwartz`) is
  the explicit datum `prof : ℝ → 𝓢(ℝ, ℂ)` with `hprof : ∀ t x, prof t x = x ^ (I t) * W x`.
  Its existence for smooth `W` supported in `[a, b] ⊂ (0, ∞)` is the only analytic input.
* The constant `128` is `idealCountConstant K`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators SchwartzMap
open HeckePort.CenteredMomentCancellation HeckePort.CenteredMomentCounting
open HeckePort.CenteredMomentVolume

variable {K : Type*} [Field K] [NumberField K]

namespace Twist

def twistedMaskedSum (Ψ : Ideal (𝓞 K) → ℂ) (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal (𝓞 K), (if IsCoprime I R then (1 : ℂ) else 0) *
    (Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I : ℝ) / X))

section Profile

variable (W : ℝ → ℂ) (prof : ℝ → 𝓢(ℝ, ℂ))

lemma norm_cpow_imaginary (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := norm_cpow_imaginary X t hX

lemma profile_support (hprof : ∀ t x, prof t x = (x : ℂ) ^ (Complex.I * t) * W x) (t : ℝ) :
    Function.support (prof t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [hprof, hz, mul_zero])

lemma profile_norm (hprof : ∀ t x, prof t x = (x : ℂ) ^ (Complex.I * t) * W x)
    (hW : ∀ x, W x ≠ 0 → 0 < x) (t x : ℝ) :
    ‖prof t x‖ = ‖W x‖ := by
  rw [hprof, norm_mul]
  by_cases hx : W x = 0
  · simp [hx]
  · rw [norm_cpow_imaginary x t (hW x hx), one_mul]

end Profile

variable {Ψ : Ideal (𝓞 K) →* ℂ} (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
  (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K))
  (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
  (prof : ℝ → 𝓢(ℝ, ℂ)) (hprof : ∀ t x, prof t x = (x : ℂ) ^ (Complex.I * t) * W x)

include hprof in
theorem twistedMaskedSum_scale (t X : ℝ) (hX : 0 < X) :
    twistedMaskedSum Ψ R W t X = (X : ℂ) ^ (Complex.I * t) *
      maskedSum Ψ R (prof t) X := by
  unfold twistedMaskedSum maskedSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [hprof]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

include hprof hs ha in
lemma prof_support_Iic (t : ℝ) : Function.support (prof t : ℝ → ℂ) ⊆ Set.Iic b :=
  (profile_support W prof hprof t).trans (fun _ hx => (hs hx).2)

include hprof hs ha in
lemma prof_norm (t x : ℝ) : ‖prof t x‖ = ‖W x‖ :=
  profile_norm W prof hprof (fun y hy => lt_of_lt_of_le ha (hs hy).1) t x

include hΨ hΨ0 hprof hs ha in
theorem twistedMaskedSum_volume (hR : R ≠ ⊥) (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum Ψ R W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * (maskedDensity Ψ R * V.density (prof t))‖ ≤
      maskedError V R (prof t) := by
  rw [twistedMaskedSum_scale R W prof hprof t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * (maskedDensity Ψ R * V.density (prof t)) =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (maskedDensity Ψ R * V.density (prof t))) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_volume Ψ hΨ V R hR (prof t) b X hX (prof_support_Iic W a b ha hs prof hprof t)

include hΨ hΨ0 hprof hs ha in
theorem twistedMaskedSum_absolute (M : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum Ψ R W t X‖ ≤ (idealCountConstant K * b * M) * X := by
  rw [twistedMaskedSum_scale R W prof hprof t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_absolute Ψ hΨ hΨ0 R _ b M X hb hM hX
    (fun y => (prof_norm W a b ha hs prof hprof t y).trans_le (hbound y))
    (prof_support_Iic W a b ha hs prof hprof t)

include hΨ hΨ0 hprof hs ha in
theorem twisted_volumeCoefficient_norm_le (hR : R ≠ ⊥) (M : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖maskedDensity Ψ R * V.density (prof t)‖ ≤ idealCountConstant K * b * M := by
  exact norm_linear_coefficient_le (fun X => maskedSum Ψ R (prof t) X)
    _ (idealCountConstant K * b * M) (maskedError V R (prof t))
    (maskedError_nonneg V R (prof t))
    (fun X hX => maskedSum_volume Ψ hΨ V R hR (prof t) b X hX
      (prof_support_Iic W a b ha hs prof hprof t))
    (fun X hX => maskedSum_absolute Ψ hΨ hΨ0 R (prof t) b M X hb hM hX
      (fun y => (prof_norm W a b ha hs prof hprof t y).trans_le (hbound y))
      (prof_support_Iic W a b ha hs prof hprof t))

/-- openai `twisted_rectangle_saving`. -/
theorem twisted_rectangle_saving {Ψ : Ideal (𝓞 K) →* ℂ} (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (V : IdealVolumeInput K Ψ) (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (prof₁ prof₂ : ℝ → 𝓢(ℝ, ℂ))
    (hprof₁ : ∀ t x, prof₁ t x = (x : ℂ) ^ (Complex.I * t) * W₁ x)
    (hprof₂ : ∀ t x, prof₂ t x = (x : ℂ) ^ (Complex.I * t) * W₂ x)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError V R (prof₁ t) + maskedError V R (prof₂ t)
    ‖twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂ -
      twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂‖ ≤
      4 * E * (idealCountConstant K * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  have hc0 : 0 ≤ idealCountConstant K := (zero_le_one.trans (one_le_idealCountConstant K))
  let V₁ := prof₁ t
  let V₂ := prof₂ t
  let E := maskedError V R V₁ + maskedError V R V₂
  let C := idealCountConstant K * (b₁ * M₁ + b₂ * M₂)
  let v₁ := maskedDensity Ψ R * V.density V₁
  let v₂ := maskedDensity Ψ R * V.density V₂
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := maskedError_nonneg V R V₁
  have hE₂ := maskedError_nonneg V R V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg hc0 (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : idealCountConstant K * b₁ * M₁ ≤ C := by
    dsimp only [C]; nlinarith [mul_nonneg hc0 (mul_nonneg hb₂ hM₂)]
  have hC₂ : idealCountConstant K * b₂ * M₂ ≤ C := by
    dsimp only [C]; nlinarith [mul_nonneg hc0 (mul_nonneg hb₁ hM₁)]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₁ t X - m₁ X‖ ≤ E :=
    (twistedMaskedSum_volume hΨ hΨ0 V R W₁ a₁ b₁ ha₁ hs₁ prof₁ hprof₁ hR t X
      (lt_of_lt_of_le hL hX)).trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₂ t X - m₂ X‖ ≤ E :=
    (twistedMaskedSum_volume hΨ hΨ0 V R W₂ a₂ b₂ ha₂ hs₂ prof₂ hprof₂ hR t X
      (lt_of_lt_of_le hL hX)).trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_volumeCoefficient_norm_le hΨ hΨ0 V R W₁ a₁ b₁ ha₁ hs₁ prof₁ hprof₁ hR M₁
      hb₁ hM₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₂ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute hΨ hΨ0 R W₂ a₂ b₂ ha₂ hs₂ prof₂ hprof₂ M₂ hb₂ hM₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := HeckePort.CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [HeckePort.CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact HeckePort.CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end Twist

end HeckePort.Moments

end
