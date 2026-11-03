import HeckePort.Moments.Height
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Equal-product cancellation on the exceptional terminal

This file completes the uniform algebraic consumer of manuscript Lemma 4.11.
All sums are the existing `Twist.twistedMaskedSum` on actual integral ideals.
The common coprimality mask and the same height `t` occur in all four factors.

The analytic input is deliberately explicit: `IdealVolumeInput` supplies the
unmasked volume estimate, and `ExceptionalProfiles` supplies its seminorm and
height control. The residue identification in `exceptional_main_of_volume`
is also an explicit input. These are the existing general-field analytic inputs; neither a centered bound nor a final moment bound is assumed.

The new uniform conclusion chooses its constant before the two profiles,
the common radical, the height and all four scales. The absolute fallback
needs only ideal counting and bounded compact support, and has no volume
or Schwartz-profile premise.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open scoped NumberField Classical BigOperators SchwartzMap
open MeasureTheory UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckePort.CenteredMoment HeckePort.CenteredMomentMask
open HeckePort.CenteredMomentCancellation HeckePort.CenteredMomentCounting
open HeckePort.CenteredMomentVolume HeckePort.Moments.Twist

variable {K : Type*} [Field K] [NumberField K]

/-- The norm phase as a multiplicative function on actual ideals. -/
def idealNormPhase (t : ℝ) : Ideal (𝓞 K) →* ℂ where
  toFun I := (Ideal.absNorm I : ℂ) ^ (Complex.I * t)
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

/-- Exact inclusion--exclusion for the original twisted ideal sum. No
analytic continuation, asymptotic, or change of mask is used here. -/
theorem twisted_mask_deletion (Ψ : Ideal (𝓞 K) →* ℂ)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W : ℝ → ℂ)
    (b t X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    twistedMaskedSum Ψ R W t X =
      ∑ D ∈ idealDivisors R,
        (moebius D : ℂ) * Ψ D * (Ideal.absNorm D : ℂ) ^ (Complex.I * t) *
          ∑' I : Ideal (𝓞 K), Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
            W ((Ideal.absNorm I : ℝ) / (X / Ideal.absNorm D)) := by
  have h := masked_plain_ideal_sum R hR (Ψ * idealNormPhase (K := K) t) W b X hX hs
  simpa only [twistedMaskedSum, MonoidHom.mul_apply, idealNormPhase,
    MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc] using h

/-- The residue coefficient after deleting the common radical. It depends
on the character and mask, and is independent of scale and height. -/
def exceptionalResidue (Ψ : Ideal (𝓞 K) → ℂ) (residue : ℂ)
    (R : Ideal (𝓞 K)) : ℂ :=
  residue * maskedDensity Ψ R

@[simp] theorem exceptionalResidue_zero (Ψ : Ideal (𝓞 K) → ℂ)
    (R : Ideal (𝓞 K)) : exceptionalResidue Ψ 0 R = 0 := by
  simp [exceptionalResidue]

/-- In each divisor term, the phase on the divisor cancels the phase in
the rescaled main term. This is the exact residue before absolute values. -/
theorem exceptional_residue_extraction (Ψ : Ideal (𝓞 K) → ℂ)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (residue I : ℂ)
    (t X : ℝ) (hX : 0 ≤ X) :
    (∑ D ∈ idealDivisors R,
      (moebius D : ℂ) * Ψ D * (Ideal.absNorm D : ℂ) ^ (Complex.I * t) *
        volumeTerm residue I t (X / Ideal.absNorm D)) =
      volumeTerm (exceptionalResidue Ψ residue R) I t X := by
  have hn (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors R) :
      0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ ⊥ := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero
      (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  simpa only [exceptionalResidue, maskedDensity, Complex.ofReal_natCast]
    using extracted_volume_sum (idealDivisors R) (fun D => (moebius D : ℂ) * Ψ D)
      (fun D => (Ideal.absNorm D : ℝ)) hn residue I t X hX

/-- Absolute ideal counting for the original twisted sum, including every
positive subunit scale. No auxiliary Schwartz realization is required. -/
theorem twistedMaskedSum_absolute_direct (Ψ : Ideal (𝓞 K) → ℂ)
    (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b M t X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hbound : ∀ y, ‖W y‖ ≤ M)
    (hs : Function.support W ⊆ Set.Iic b) :
    ‖twistedMaskedSum Ψ R W t X‖ ≤ (idealCountConstant K * b * M) * X := by
  have h := norm_tsum_ideal_ball
    (fun I : Ideal (𝓞 K) => (if IsCoprime I R then (1 : ℂ) else 0) *
      (Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
        W ((Ideal.absNorm I : ℝ) / X)))
    (b * X) M (mul_nonneg hb hX.le) hM
    (by simp only [hΨ0, zero_mul, mul_zero])
    (by
      intro I
      by_cases hI : I = ⊥
      · simp only [hI, hΨ0, zero_mul, mul_zero, norm_zero]
        exact hM
      · have hn : 0 < (Ideal.absNorm I : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero
            (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
        have hp : ‖(Ideal.absNorm I : ℂ) ^ (Complex.I * t)‖ = 1 := by
          simpa only [Complex.ofReal_natCast] using norm_cpow_imaginary
            (Ideal.absNorm I : ℝ) t hn
        rw [← mul_assoc, ← mul_assoc, norm_mul, norm_mul, hp, mul_one]
        exact (mul_le_mul (masked_coefficient_norm_le_one Ψ hΨ R I)
          (hbound _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by
      intro I hI
      have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
        intro hz
        exact hI (by simp only [hz, mul_zero])
      exact (div_le_iff₀ hX).mp (hs hw))
  change ‖twistedMaskedSum Ψ R W t X‖ ≤ _ at h
  convert h using 1 <;> ring

/-- The terminal estimate when no nonnegative lower length is available.
It uses only the two original absolute ideal-sum bounds. -/
theorem exceptional_normalized_fallback (Ψ : Ideal (𝓞 K) → ℂ)
    (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hpX : X₁ * X₂ = T) (hpY : Y₁ * Y₂ = T) :
    ‖(Real.sqrt T : ℂ)⁻¹ *
      (twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂ -
        twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂)‖ ≤
      2 * (idealCountConstant K * (b₁ * M₁ + b₂ * M₂)) ^ 2 * Real.sqrt T := by
  let C := idealCountConstant K * (b₁ * M₁ + b₂ * M₂)
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hc₁ : idealCountConstant K * b₁ * M₁ ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hcount (mul_nonneg hb₂ hM₂)]
  have hc₂ : idealCountConstant K * b₂ * M₂ ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hcount (mul_nonneg hb₁ hM₁)]
  have h₁ (X : ℝ) (hX : 0 < X) : ‖twistedMaskedSum Ψ R W₁ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute_direct Ψ hΨ hΨ0 R W₁ b₁ M₁ t X hb₁ hM₁ hX
      hbound₁ hs₁).trans (mul_le_mul_of_nonneg_right hc₁ hX.le)
  have h₂ (X : ℝ) (hX : 0 < X) : ‖twistedMaskedSum Ψ R W₂ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute_direct Ψ hΨ hΨ0 R W₂ b₂ M₂ t X hb₂ hM₂ hX
      hbound₂ hs₂).trans (mul_le_mul_of_nonneg_right hc₂ hX.le)
  have hraw := centered_volume_fallback _ _ _ _ X₁ X₂ Y₁ Y₂ T C
    (h₁ X₁ hX₁) (h₂ X₂ hX₂) (h₁ Y₁ hY₁) (h₂ Y₂ hY₂) hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos hX₁ hX₂
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hsqrt.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (2 * C ^ 2 * T) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsqrt.le)
    _ = 2 * C ^ 2 * Real.sqrt T := by
      have htdiv : T / Real.sqrt T = Real.sqrt T :=
        (div_eq_iff hsqrt.ne').mpr (Real.mul_self_sqrt hT.le).symm
      calc
        _ = 2 * C ^ 2 * (T / Real.sqrt T) := by ring
        _ = _ := by rw [htdiv]

/-- Analytic control for an entire profile class. The seminorm is explicit;
the terminal constant will be chosen before the two profile indices. -/
structure ExceptionalProfiles {Ψ : Ideal (𝓞 K) → ℂ}
    (V : IdealVolumeInput K Ψ) (ι : Type*) where
  weight : ι → ℝ → ℂ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_nonneg : 0 ≤ upper
  seminorm : ι → ℝ
  seminorm_nonneg : ∀ i, 0 ≤ seminorm i
  support : ∀ i, Function.support (weight i) ⊆ Set.Icc lower upper
  norm_bound : ∀ i y, ‖weight i y‖ ≤ seminorm i
  profile : ι → ℝ → 𝓢(ℝ, ℂ)
  profile_eq : ∀ i t y, profile i t y = (y : ℂ) ^ (Complex.I * t) * weight i y
  order : ℕ
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  error_bound : ∀ i t,
    V.error (profile i t) ≤ errorConstant * seminorm i * (1 + ‖t‖) ^ order

variable {Ψ : Ideal (𝓞 K) →* ℂ} {V : IdealVolumeInput K Ψ}
variable {ι : Type*}

/-- The finite radical loss is uniform over the whole profile class. -/
theorem exceptional_masked_error_uniform (F : ExceptionalProfiles V ι)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ i t, maskedError V R (F.profile i t) ≤
        C * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order := by
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound (K := K) ε B hε hB
  refine ⟨1 + D * F.errorConstant, ?_, ?_⟩
  · have := F.errorConstant_nonneg
    positivity
  intro Z hZ R hR hnorm i t
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hp : 0 ≤ F.seminorm i := F.seminorm_nonneg i
  have ht : 0 ≤ (1 + ‖t‖) ^ F.order := by positivity
  have hb := mul_le_mul (hdiv Z hZ R hR hnorm) (F.error_bound i t)
    (V.error_nonneg _) (mul_nonneg hD.le hz)
  change maskedError V R (F.profile i t) ≤
    (D * Z ^ ε) * (F.errorConstant * F.seminorm i * (1 + ‖t‖) ^ F.order) at hb
  calc
    _ ≤ (D * Z ^ ε) * (F.errorConstant * F.seminorm i * (1 + ‖t‖) ^ F.order) := hb
    _ = (D * F.errorConstant) * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order := by ring
    _ ≤ (1 + D * F.errorConstant) * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hz) hp) ht

/-- The Mellin moment occurring in the residue at `s = 1`. -/
def exceptionalProfileIntegral (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), W y * (y : ℂ) ^ (Complex.I * t)

/-- The all-scale asymptotic from the explicit unmasked volume estimate.
`hdensity` is the identification of that volume with the genuine residue;
it must be supplied by the analytic construction of `V`. -/
theorem exceptional_main_of_volume (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (F : ExceptionalProfiles V ι) (residue : ℂ)
    (hdensity : ∀ i t, V.density (F.profile i t) =
      residue * exceptionalProfileIntegral (F.weight i) t)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ i t X, 0 < X →
        ‖twistedMaskedSum Ψ R (F.weight i) t X -
          volumeTerm (exceptionalResidue Ψ residue R)
            (exceptionalProfileIntegral (F.weight i) t) t X‖ ≤
          C * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order := by
  obtain ⟨C, hC, herror⟩ := exceptional_masked_error_uniform F ε B hε hB
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm i t X hX
  have h := twistedMaskedSum_volume hΨ hΨ0 V R (F.weight i) F.lower F.upper
    F.lower_pos (F.support i) (F.profile i) (F.profile_eq i) hR t X hX
  rw [hdensity i t] at h
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) *
      (maskedDensity Ψ R * (residue * exceptionalProfileIntegral (F.weight i) t)) =
      volumeTerm (exceptionalResidue Ψ residue R)
        (exceptionalProfileIntegral (F.weight i) t) t X := by
    unfold volumeTerm exceptionalResidue
    ring
  rw [hmain] at h
  exact h.trans (herror Z hZ R hR hnorm i t)

/-- The residue cancels exactly for equal products, before a norm is taken. -/
theorem exceptional_equal_product_main (R : Ideal (𝓞 K)) (residue : ℂ)
    (W₁ W₂ : ℝ → ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hprod : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm (exceptionalResidue Ψ residue R) (exceptionalProfileIntegral W₁ t) t X₁ *
        volumeTerm (exceptionalResidue Ψ residue R) (exceptionalProfileIntegral W₂ t) t X₂ -
      volumeTerm (exceptionalResidue Ψ residue R) (exceptionalProfileIntegral W₁ t) t Y₁ *
        volumeTerm (exceptionalResidue Ψ residue R) (exceptionalProfileIntegral W₂ t) t Y₂ = 0 := by
  exact sub_eq_zero.mpr (volume_products_eq _ _ _ t X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hprod)

/-- Uniform equal-product cancellation for the original masked ideal sums.
One constant works for the whole profile family and every polynomial-size
common radical. The saving is the manuscript's literal `Z ^ (-a)`.

Using the absolute bound for a full factor avoids squaring the divisor
loss, and even keeps the height exponent at `F.order`. -/
theorem exceptional_equal_product_cancellation (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (hΨ0 : Ψ ⊥ = 0) (F : ExceptionalProfiles V ι)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ (i j : ι) (t X₁ X₂ Y₁ Y₂ T a : ℝ), 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedMaskedSum Ψ R (F.weight i) t X₁ * twistedMaskedSum Ψ R (F.weight j) t X₂ -
          twistedMaskedSum Ψ R (F.weight i) t Y₁ * twistedMaskedSum Ψ R (F.weight j) t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          (F.seminorm i + F.seminorm j) ^ 2 * (1 + ‖t‖) ^ F.order := by
  obtain ⟨D, hD, herror⟩ := exceptional_masked_error_uniform F ε B hε hB
  let C₀ := idealCountConstant K * F.upper
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (zero_le_one.trans (one_le_idealCountConstant K)) F.upper_nonneg
  let C := 1 + 4 * D * C₀
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm i j t X₁ X₂ Y₁ Y₂ T a _ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hL : 0 < Z ^ a := Real.rpow_pos_of_pos hZ0 _
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  let P := F.seminorm i + F.seminorm j
  let E := maskedError V R (F.profile i t) + maskedError V R (F.profile j t)
  have hP : 0 ≤ P := add_nonneg (F.seminorm_nonneg i) (F.seminorm_nonneg j)
  have hz : 0 ≤ Z ^ ε := (Real.rpow_pos_of_pos hZ0 _).le
  have ht : 0 ≤ (1 + ‖t‖) ^ F.order := by positivity
  have hE : E ≤ D * Z ^ ε * P * (1 + ‖t‖) ^ F.order := by
    have hi := herror Z hZ R hR hnorm i t
    have hj := herror Z hZ R hR hnorm j t
    calc
      _ ≤ D * Z ^ ε * F.seminorm i * (1 + ‖t‖) ^ F.order +
          D * Z ^ ε * F.seminorm j * (1 + ‖t‖) ^ F.order := add_le_add hi hj
      _ = _ := by dsimp only [P]; ring
  have hraw := twisted_rectangle_saving hΨ hΨ0 V R hR
    (F.weight i) (F.weight j) F.lower F.upper F.lower F.upper
    (F.seminorm i) (F.seminorm j) F.lower_pos F.lower_pos
    F.upper_nonneg F.upper_nonneg (F.seminorm_nonneg i) (F.seminorm_nonneg j)
    (F.support i) (F.support j) (F.profile i) (F.profile j)
    (F.profile_eq i) (F.profile_eq j) (F.norm_bound i) (F.norm_bound j)
    t X₁ X₂ Y₁ Y₂ T (Z ^ a) hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hcoef : idealCountConstant K *
      (F.upper * F.seminorm i + F.upper * F.seminorm j) = C₀ * P := by
    dsimp only [C₀, P]
    ring
  rw [hcoef] at hraw
  have hn := normalized_centered_saving _ T (Z ^ a) (C₀ * P) E hT hraw
  have hratio : 0 ≤ Real.sqrt T / Z ^ a := div_nonneg (Real.sqrt_nonneg T) hL.le
  have heq : Real.sqrt T / Z ^ a = Real.sqrt T * Z ^ (-a) := by
    rw [Real.rpow_neg hZ0.le, div_eq_mul_inv]
  calc
    _ ≤ 4 * E * (C₀ * P) * (Real.sqrt T / Z ^ a) := hn
    _ ≤ 4 * (D * Z ^ ε * P * (1 + ‖t‖) ^ F.order) * (C₀ * P) *
        (Real.sqrt T / Z ^ a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE (by norm_num)) (mul_nonneg hC₀ hP)) hratio
    _ = (4 * D * C₀) * Z ^ ε * Real.sqrt T * Z ^ (-a) * P ^ 2 *
        (1 + ‖t‖) ^ F.order := by rw [heq]; ring
    _ ≤ C * Z ^ ε * Real.sqrt T * Z ^ (-a) * P ^ 2 * (1 + ‖t‖) ^ F.order := by
      apply mul_le_mul_of_nonneg_right _ ht
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg P)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
      apply mul_le_mul_of_nonneg_right _ hz
      dsimp only [C]
      linarith

end HeckeSkeleton.Moments.MOM_PRIME
