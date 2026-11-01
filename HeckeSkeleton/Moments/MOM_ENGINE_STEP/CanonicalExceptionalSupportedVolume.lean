import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPrimitiveBounds

/-!
# Exceptional volume from the original supported ideal series

Only tests supported in the original fixed compact positive window enter
the analytic primitive.  The imaginary norm twist preserves that support,
and the Möbius expansion changes the positive scale, not the test.  The
masked estimate and the centered cancellation are proved directly from
these supported single-series estimates.  No global `IdealVolumeInput`
is constructed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.IdealMobiusDivisorSum HeckePort.CenteredMomentMask
open HeckePort.CenteredMomentCancellation HeckePort.CenteredMomentCounting
open HeckePort.Moments HeckePort.Moments.Twist

variable {K : Type} [Field K] [NumberField K]

theorem twistedProfile_support (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) (t : ℝ) :
    tsupport (twistedProfile window hcompact hpositive φ hsupport t) ⊆ window := by
  change tsupport (CanonicalLogProfiles.shapeProduct 0 t φ) ⊆ window
  exact (CanonicalLogProfiles.tsupport_shapeProduct_subset 0 t φ).trans hsupport

/-- The only series estimate used by Möbius inversion concerns this
same original test at all positive scales. -/
theorem masked_volume_of_single_series
    (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (φ : 𝓢(ℝ, ℂ))
    (b : ℝ) (hs : Function.support (φ : ℝ → ℂ) ⊆ Set.Iic b)
    (density : ℂ) (error : ℝ)
    (hvolume : ∀ X : ℝ, 0 < X →
      ‖(∑' I : Ideal (𝓞 K), Ψ I * φ ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density‖ ≤ error)
    (X : ℝ) (hX : 0 < X) :
    ‖maskedSum Ψ R φ X - (X : ℂ) * (maskedDensity Ψ R * density)‖ ≤
      ((idealDivisors R).card : ℝ) * error := by
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal (𝓞 K), Ψ I * φ ((Ideal.absNorm I : ℝ) / Y)
  have hnD (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors R) :
      0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ ⊥ := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal (𝓞 K)) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * density‖ ≤ error :=
    hvolume (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
  have hcoef (D : Ideal (𝓞 K)) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D) (hΨ D)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq : maskedSum Ψ R φ X - (X : ℂ) * (maskedDensity Ψ R * density) =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * density) := by
    unfold maskedSum maskedDensity
    rw [masked_plain_ideal_sum R hR Ψ φ b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * density)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, error := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul error)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

private theorem twisted_volume_of_single_series
    (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b)
    (prof : ℝ → 𝓢(ℝ, ℂ))
    (hprof : ∀ t x, prof t x = (x : ℂ) ^ (Complex.I * t) * W x)
    (t : ℝ) (density : ℂ) (error : ℝ)
    (hvolume : ∀ X : ℝ, 0 < X →
      ‖(∑' I : Ideal (𝓞 K), Ψ I * prof t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density‖ ≤ error)
    (X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum Ψ R W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * (maskedDensity Ψ R * density)‖ ≤
      ((idealDivisors R).card : ℝ) * error := by
  rw [twistedMaskedSum_scale R W prof hprof t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * (maskedDensity Ψ R * density) =
      (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) * (maskedDensity Ψ R * density)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact masked_volume_of_single_series Ψ hΨ R hR (prof t) b
    (prof_support_Iic W a b ha hs prof hprof t) density error hvolume X hX

private theorem density_norm_of_single_series
    (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
    (W : ℝ → ℂ) (a b P : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hs : Function.support W ⊆ Set.Icc a b) (hbound : ∀ y, ‖W y‖ ≤ P)
    (prof : ℝ → 𝓢(ℝ, ℂ))
    (hprof : ∀ t x, prof t x = (x : ℂ) ^ (Complex.I * t) * W x)
    (t : ℝ) (density : ℂ) (error : ℝ) (herror : 0 ≤ error)
    (hvolume : ∀ X : ℝ, 0 < X →
      ‖(∑' I : Ideal (𝓞 K), Ψ I * prof t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density‖ ≤ error) :
    ‖maskedDensity Ψ R * density‖ ≤ idealCountConstant K * b * P := by
  exact norm_linear_coefficient_le (fun X => maskedSum Ψ R (prof t) X)
    _ (idealCountConstant K * b * P) (((idealDivisors R).card : ℝ) * error)
    (mul_nonneg (Nat.cast_nonneg _) herror)
    (fun X hX => masked_volume_of_single_series Ψ hΨ R hR (prof t) b
      (prof_support_Iic W a b ha hs prof hprof t) density error hvolume X hX)
    (fun X hX => maskedSum_absolute Ψ hΨ hΨ0 R (prof t) b P X hb hP hX
      (fun y => (prof_norm W a b ha hs prof hprof t y).trans_le (hbound y))
      (prof_support_Iic W a b ha hs prof hprof t))

private theorem rectangle_of_single_series
    (Ψ : Ideal (𝓞 K) →* ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
    (W₁ W₂ : ℝ → ℂ) (a b P : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (prof₁ prof₂ : ℝ → 𝓢(ℝ, ℂ))
    (hprof₁ : ∀ t x, prof₁ t x = (x : ℂ) ^ (Complex.I * t) * W₁ x)
    (hprof₂ : ∀ t x, prof₂ t x = (x : ℂ) ^ (Complex.I * t) * W₂ x)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ P) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ P)
    (t : ℝ) (density₁ density₂ : ℂ) (error₁ error₂ : ℝ)
    (he₁ : 0 ≤ error₁) (he₂ : 0 ≤ error₂)
    (hvolume₁ : ∀ X : ℝ, 0 < X →
      ‖(∑' I : Ideal (𝓞 K), Ψ I * prof₁ t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density₁‖ ≤ error₁)
    (hvolume₂ : ∀ X : ℝ, 0 < X →
      ‖(∑' I : Ideal (𝓞 K), Ψ I * prof₂ t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density₂‖ ≤ error₂)
    (X₁ X₂ Y₁ Y₂ Q L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hpX : X₁ * X₂ = Q) (hpY : Y₁ * Y₂ = Q) :
    ‖normalizedMaskedRectangle Ψ R W₁ W₂ t X₁ X₂ Y₁ Y₂ Q‖ ≤
      4 * (((idealDivisors R).card : ℝ) * error₁ +
        ((idealDivisors R).card : ℝ) * error₂) *
        (idealCountConstant K * (b * P + b * P)) * (Real.sqrt Q / L) := by
  let E := ((idealDivisors R).card : ℝ) * error₁ +
    ((idealDivisors R).card : ℝ) * error₂
  let C := idealCountConstant K * (b * P + b * P)
  let v₁ := maskedDensity Ψ R * density₁
  let v₂ := maskedDensity Ψ R * density₂
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hc0 : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hE₁ : 0 ≤ ((idealDivisors R).card : ℝ) * error₁ := mul_nonneg (Nat.cast_nonneg _) he₁
  have hE₂ : 0 ≤ ((idealDivisors R).card : ℝ) * error₂ := mul_nonneg (Nat.cast_nonneg _) he₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg hc0 (add_nonneg (mul_nonneg hb hP) (mul_nonneg hb hP))
  have hC₁ : idealCountConstant K * b * P ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hc0 (mul_nonneg hb hP)]
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₁ t X - m₁ X‖ ≤ E :=
    (twisted_volume_of_single_series Ψ hΨ R hR W₁ a b ha hs₁ prof₁ hprof₁ t
      density₁ error₁ hvolume₁ X (hL.trans_le hX)).trans (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₂ t X - m₂ X‖ ≤ E :=
    (twisted_volume_of_single_series Ψ hΨ R hR W₂ a b ha hs₂ prof₂ hprof₂ t
      density₂ error₂ hvolume₂ X (hL.trans_le hX)).trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (density_norm_of_single_series Ψ hΨ hΨ0 R hR W₁ a b P ha hb hP
      hs₁ hbound₁ prof₁ hprof₁ t density₁ error₁ he₁ hvolume₁).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hL.trans_le hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (hL.le.trans hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum Ψ R W₂ t X‖ ≤ C * X :=
    (twisted_sum_absolute Ψ hΨ hΨ0 R W₂ b P t X hb hP (hL.trans_le hX)
      hbound₂ (fun y hy => (hs₂ hy).2)).trans
      (mul_le_mul_of_nonneg_right hC₁ (hL.le.trans hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hp := HeckePort.CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (hL.le.trans hX₁) (hL.le.trans hX₂)
      (hL.le.trans hY₁) (hL.le.trans hY₂) (hpX.trans hpY.symm)
    simpa only [HeckePort.CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hp
  have hraw := HeckePort.CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ Q L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hQ : 0 < Q := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  exact HeckePort.CenteredMoment.normalized_centered_saving _ Q L C E hQ hraw

section Allocated

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h' : A.R} {k : ℕ}

private theorem supported_source_from_rectangle (hΨ0 : Ψ ⊥ = 0)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (B : ℝ) (hB : 0 ≤ B)
    (hrectangle : ‖normalizedMaskedRectangle Ψ s.mask W₁ W₂ s.time
      (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
      (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
      (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product‖ ≤
        B * Real.sqrt s.product) : ‖s.value‖ ≤ B * s.rawMass := by
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (s.characters.restrictSlots s.allocation.keep)
    g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
    s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
    (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ
  rw [s.identity hΨ0, norm_mul, norm_mul, norm_mul, norm_jointPhase, mul_one]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul hrectangle hs (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _)))
    (norm_nonneg (s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w))
  convert hm using 1 <;> dsimp only [AllocatedExceptionalSource.rawMass,
    AllocatedExceptionalSource.slotMass] <;> ring

private theorem supported_source_from_product (hΨ0 : Ψ ⊥ = 0)
    (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h' k)
    (B : ℝ) (hB : 0 ≤ B)
    (hproduct : ‖(Real.sqrt s.product : ℂ)⁻¹ *
      (twistedMaskedSum Ψ s.mask W₁ s.time
          (s.X₁ / idealNorm K (s.allocation.plainDivisor 0)) *
        twistedMaskedSum Ψ s.mask W₂ s.time
          (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))))‖ ≤
        B * Real.sqrt s.product) : ‖s.ordinaryValue‖ ≤ B * s.rawMass := by
  have hs := norm_actualSourceSlotPolynomial_le (σ := σ) (s.characters.restrictSlots s.allocation.keep)
    g h' s.Zslot (fun j => s.length (SlotRestriction.index s.allocation.keep j))
    s.allocation.childSlots (fun j => s.w (SlotRestriction.index s.allocation.keep j))
    (fun j => s.x (SlotRestriction.index s.allocation.keep j)) s.ξ
  rw [s.ordinary_identity hΨ0, norm_mul, norm_mul, norm_mul, norm_jointPhase, mul_one]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul hproduct hs (norm_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _)))
    (norm_nonneg (s.allocation.scalar (σ := σ) s.characters g h' s.Zslot s.length s.w))
  convert hm using 1 <;> dsimp only [AllocatedExceptionalSource.rawMass,
    AllocatedExceptionalSource.slotMass] <;> ring

end Allocated

section Uniform

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem supported_source_absolute
    (χ : HeckeCharacter K) (W₁ W₂ : ℝ → ℂ) (b P : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hW₁ : ∀ y, ‖W₁ y‖ ≤ P) (hW₂ : ∀ y, ‖W₂ y‖ ≤ P)
    {g h' : A.R} {k : ℕ}
    (s : AllocatedExceptionalSource (V := V) (σ := σ)
      (coefficient χ) W₁ W₂ g h' k) :
    ‖s.ordinaryValue‖ ≤ (idealCountConstant K * b) ^ 2 * P ^ 2 * s.rawMass ∧
    ‖s.value‖ ≤ (2 * (idealCountConstant K * b) ^ 2) * P ^ 2 * s.rawMass := by
  have hp (X₁ X₂ Q : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hQ : X₁ * X₂ = Q) :
      ‖(Real.sqrt Q : ℂ)⁻¹ *
        (twistedMaskedSum (coefficient χ) s.mask W₁ s.time X₁ *
          twistedMaskedSum (coefficient χ) s.mask W₂ s.time X₂)‖ ≤
        ((idealCountConstant K * b) ^ 2 * P ^ 2) * Real.sqrt Q := by
    convert normalized_product_absolute χ s.mask W₁ W₂ b b P P s.time X₁ X₂ Q
      hb hb hP hP hX₁ hX₂ hQ hW₁ hW₂ hs₁ hs₂ using 1 <;>
      dsimp only [pairConstant] <;> ring
  have hx := hp _ _ s.product (s.lower_pos.trans_le s.X₁_lower)
    (s.lower_pos.trans_le s.X₂_lower) s.productX
  have hy := hp _ _ s.product (s.lower_pos.trans_le s.Y₁_lower)
    (s.lower_pos.trans_le s.Y₂_lower) s.productY
  constructor
  · exact supported_source_from_product (coefficient_zero χ) s _
      (mul_nonneg (sq_nonneg _) (sq_nonneg P)) hx
  · have hr : ‖normalizedMaskedRectangle (coefficient χ) s.mask W₁ W₂ s.time
        (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
        (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product‖ ≤
        ((2 * (idealCountConstant K * b) ^ 2) * P ^ 2) * Real.sqrt s.product := by
      unfold normalizedMaskedRectangle
      rw [mul_sub]
      exact (norm_sub_le _ _).trans ((add_le_add hx hy).trans_eq (by ring))
    exact supported_source_from_rectangle (coefficient_zero χ) s _
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg P)) hr

variable {ι : Type*} [Fintype ι]

/-- All analytic tests lie in the fixed original positive window. The
finite orders, height degree and constant are chosen before the profiles,
mask, Fourier height, allocation and four actual rectangle scales. -/
theorem exists_original_source_bounds_supported
    (χ : ι → HeckeCharacter K)
    (density : ι → 𝓢(ℝ, ℂ) → ℂ)
    (remainder : ι → Seminorm ℂ (𝓢(ℝ, ℂ)))
    (hcontinuous : ∀ i, Continuous (remainder i))
    (window : Set ℝ)
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X → tsupport φ ⊆ window →
      ‖(∑' I : Ideal (𝓞 K), coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
      ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (i : ι) (φ₁ φ₂ : 𝓢(ℝ, ℂ)),
        tsupport φ₁ ⊆ window → tsupport φ₂ ⊆ window →
        ∀ P : ℝ, 0 ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₁ ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₂ ≤ P →
        (∀ {g h' : A.R} {k : ℕ}
          (s : AllocatedExceptionalSource (V := V) (σ := σ)
            (coefficient (χ i)) φ₁ φ₂ g h' k),
          ‖s.ordinaryValue‖ ≤ C * P ^ 2 * s.rawMass ∧
          ‖s.value‖ ≤ C * P ^ 2 * s.rawMass) ∧
        (∀ Z : ℝ, 1 ≤ Z → ∀ {g h' : A.R} {k : ℕ}
          (s : AllocatedExceptionalSource (V := V) (σ := σ)
            (coefficient (χ i)) φ₁ φ₂ g h' k),
          s.mask ≠ ⊥ → (Ideal.absNorm s.mask : ℝ) ≤ Z ^ maskExponent →
          ∀ L : ℝ, Z ^ L ≤ s.lower →
          ‖s.value‖ ≤ C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n *
            s.rawMass * Z ^ (-max L 0)) := by
  obtain ⟨orders, hzero, n, Cv, hCv, herror⟩ :=
    exists_uniform_error_control remainder hcontinuous window hcompact hpositive
  obtain ⟨a, b, ha, hb, hwindow⟩ := exists_positive_interval window hcompact hpositive
  obtain ⟨D, hD, hdivisor⟩ := polynomial_mask_divisor_bound (K := K)
    ε maskExponent hε hmask
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hcount : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  let rectangleCoefficient := 16 * D * Cv * idealCountConstant K * b
  have hrectangleCoefficient : 0 ≤ rectangleCoefficient := by
    dsimp only [rectangleCoefficient]; positivity
  let Ccenter := 1 + rectangleCoefficient
  have hCcenter : 0 < Ccenter := by dsimp only [Ccenter]; linarith
  let Cabs := 2 * (idealCountConstant K * b) ^ 2
  have hCabs : 0 ≤ Cabs := mul_nonneg (by norm_num) (sq_nonneg _)
  let C := Ccenter + Cabs
  have hC : 0 < C := add_pos_of_pos_of_nonneg hCcenter hCabs
  have hCcenterC : Ccenter ≤ C := by dsimp only [C]; linarith
  have hCabsC : Cabs ≤ C := by dsimp only [C]; linarith
  refine ⟨orders, hzero, n, C, hC, ?_⟩
  intro i φ₁ φ₂ hs₁ hs₂ P hP hP₁ hP₂
  have hnorm (φ : 𝓢(ℝ, ℂ))
      (hφ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ P) (y : ℝ) : ‖φ y‖ ≤ P :=
    (SchwartzMap.norm_le_seminorm ℂ φ y).trans
      ((Seminorm.le_finset_sup_apply hzero).trans hφ)
  have hs₁' : Function.support (φ₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    fun y hy => hwindow (hs₁ (subset_tsupport φ₁ hy))
  have hs₂' : Function.support (φ₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    fun y hy => hwindow (hs₂ (subset_tsupport φ₂ hy))
  let prof₁ := twistedProfile window hcompact hpositive φ₁ hs₁
  let prof₂ := twistedProfile window hcompact hpositive φ₂ hs₂
  have he₁ (t : ℝ) : remainder i (prof₁ t) ≤ Cv * P * (1 + ‖t‖) ^ n :=
    (herror i φ₁ hs₁ t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP₁ hCv.le) (pow_nonneg (by positivity) _))
  have he₂ (t : ℝ) : remainder i (prof₂ t) ≤ Cv * P * (1 + ‖t‖) ^ n :=
    (herror i φ₂ hs₂ t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP₂ hCv.le) (pow_nonneg (by positivity) _))
  have hv₁ (t X : ℝ) (hX : 0 < X) :
      ‖(∑' I : Ideal (𝓞 K), (coefficient (χ i)) I * prof₁ t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density i (prof₁ t)‖ ≤ remainder i (prof₁ t) :=
    hvolume i (prof₁ t) X hX (twistedProfile_support window hcompact hpositive φ₁ hs₁ t)
  have hv₂ (t X : ℝ) (hX : 0 < X) :
      ‖(∑' I : Ideal (𝓞 K), (coefficient (χ i)) I * prof₂ t ((Ideal.absNorm I : ℝ) / X)) -
        (X : ℂ) * density i (prof₂ t)‖ ≤ remainder i (prof₂ t) :=
    hvolume i (prof₂ t) X hX (twistedProfile_support window hcompact hpositive φ₂ hs₂ t)
  have hrectangle (Z : ℝ) (hZ : 1 ≤ Z) (R : Ideal (𝓞 K)) (hR : R ≠ ⊥)
      (hRnorm : (Ideal.absNorm R : ℝ) ≤ Z ^ maskExponent)
      (t X₁ X₂ Y₁ Y₂ Q L : ℝ) (hL : 0 < L)
      (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
      (hpX : X₁ * X₂ = Q) (hpY : Y₁ * Y₂ = Q) :
      ‖normalizedMaskedRectangle (coefficient (χ i)) R φ₁ φ₂ t X₁ X₂ Y₁ Y₂ Q‖ ≤
        Ccenter * P ^ 2 * Z ^ ε * (1 + ‖t‖) ^ n * (Real.sqrt Q / L) := by
    have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
    have hheight : 0 ≤ (1 + ‖t‖) ^ n := pow_nonneg (by positivity) _
    have hm₁ : ((idealDivisors R).card : ℝ) * remainder i (prof₁ t) ≤
        (D * Z ^ ε) * (Cv * P * (1 + ‖t‖) ^ n) :=
      mul_le_mul (hdivisor Z hZ R hR hRnorm) (he₁ t)
        (apply_nonneg _ _) (mul_nonneg hD.le hz)
    have hm₂ : ((idealDivisors R).card : ℝ) * remainder i (prof₂ t) ≤
        (D * Z ^ ε) * (Cv * P * (1 + ‖t‖) ^ n) :=
      mul_le_mul (hdivisor Z hZ R hR hRnorm) (he₂ t)
        (apply_nonneg _ _) (mul_nonneg hD.le hz)
    let E := ((idealDivisors R).card : ℝ) * remainder i (prof₁ t) +
      ((idealDivisors R).card : ℝ) * remainder i (prof₂ t)
    have hE : E ≤ 2 * ((D * Z ^ ε) * (Cv * P * (1 + ‖t‖) ^ n)) := by
      dsimp only [E]
      linarith
    let Vc := idealCountConstant K * (b * P + b * P)
    have hVc : 0 ≤ Vc := by dsimp only [Vc]; positivity
    have hn := rectangle_of_single_series (coefficient (χ i)) (coefficient_norm (χ i))
      (coefficient_zero (χ i)) R hR φ₁ φ₂ a b P ha hb0 hP hs₁' hs₂'
      prof₁ prof₂ (twistedProfile_apply window hcompact hpositive φ₁ hs₁)
      (twistedProfile_apply window hcompact hpositive φ₂ hs₂)
      (hnorm φ₁ hP₁) (hnorm φ₂ hP₂) t (density i (prof₁ t)) (density i (prof₂ t))
      (remainder i (prof₁ t)) (remainder i (prof₂ t))
      (apply_nonneg _ _) (apply_nonneg _ _) (hv₁ t) (hv₂ t)
      X₁ X₂ Y₁ Y₂ Q L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
    have hratio : 0 ≤ Real.sqrt Q / L := div_nonneg (Real.sqrt_nonneg Q) hL.le
    calc
      _ ≤ 4 * E * Vc * (Real.sqrt Q / L) := hn
      _ ≤ 4 * (2 * ((D * Z ^ ε) * (Cv * P * (1 + ‖t‖) ^ n))) *
          Vc * (Real.sqrt Q / L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hVc) hratio
      _ = rectangleCoefficient * P ^ 2 * Z ^ ε * (1 + ‖t‖) ^ n * (Real.sqrt Q / L) := by
        dsimp only [rectangleCoefficient, Vc]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (by dsimp only [Ccenter]; linarith : rectangleCoefficient ≤ Ccenter)
              (sq_nonneg P)) hz) hheight) hratio
  have habs {g h' : A.R} {k : ℕ}
      (s : AllocatedExceptionalSource (V := V) (σ := σ)
        (coefficient (χ i)) φ₁ φ₂ g h' k) :
      ‖s.ordinaryValue‖ ≤ Cabs * P ^ 2 * s.rawMass ∧
      ‖s.value‖ ≤ Cabs * P ^ 2 * s.rawMass := by
    have h := supported_source_absolute (χ i) φ₁ φ₂ b P hb0 hP
      (fun y hy => (hs₁' hy).2) (fun y hy => (hs₂' hy).2)
      (hnorm φ₁ hP₁) (hnorm φ₂ hP₂) s
    refine ⟨h.1.trans ?_, h.2⟩
    apply mul_le_mul_of_nonneg_right _ s.rawMass_nonneg
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg P)
    dsimp only [Cabs]
    nlinarith [sq_nonneg (idealCountConstant K * b)]
  constructor
  · intro g h' k s
    have hc : Cabs * P ^ 2 * s.rawMass ≤ C * P ^ 2 * s.rawMass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCabsC (sq_nonneg P)) s.rawMass_nonneg
    exact ⟨(habs s).1.trans hc, (habs s).2.trans hc⟩
  · intro Z hZ g h' k s hR hRnorm L hL
    have hz : 0 < Z := zero_lt_one.trans_le hZ
    have hheight : 1 ≤ (1 + ‖s.time‖) ^ n :=
      one_le_pow₀ (by linarith [norm_nonneg s.time])
    have hpower : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
    have hfront : 0 ≤ C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n := by positivity
    by_cases hlength : 0 ≤ L
    · have hr := hrectangle Z hZ s.mask hR hRnorm s.time
        (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
        (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
        (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product s.lower
        s.lower_pos s.X₁_lower s.X₂_lower s.Y₁_lower s.Y₂_lower s.productX s.productY
      have hr' : ‖normalizedMaskedRectangle (coefficient (χ i)) s.mask φ₁ φ₂ s.time
          (s.X₁ / idealNorm K (s.allocation.plainDivisor 0))
          (s.X₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0)))
          (s.Y₁ / idealNorm K (s.allocation.plainDivisor 0))
          (s.Y₂ / idealNorm K (s.allocation.plainDivisor (Fin.succ 0))) s.product‖ ≤
        (Ccenter * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n / s.lower) *
          Real.sqrt s.product := by convert hr using 1 <;> ring
      have hrectangleCoefficient :
          0 ≤ Ccenter * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n / s.lower :=
        div_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCcenter.le (sq_nonneg P))
              (zero_le_one.trans hpower))
            (zero_le_one.trans hheight)) s.lower_pos.le
      have hbound := supported_source_from_rectangle (coefficient_zero (χ i)) s _
        hrectangleCoefficient hr'
      have hinv : s.lower⁻¹ ≤ Z ^ (-L) := by
        simpa only [one_div, Real.rpow_neg hz.le] using
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz L) hL
      have hcoeff : Ccenter * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n ≤
          C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCcenterC (sq_nonneg P))
            (Real.rpow_nonneg hz.le _)) (zero_le_one.trans hheight)
      rw [max_eq_left hlength]
      apply hbound.trans
      have hm := mul_le_mul
        (mul_le_mul_of_nonneg_right hcoeff s.rawMass_nonneg) hinv
        (inv_nonneg.mpr s.lower_pos.le) (mul_nonneg hfront s.rawMass_nonneg)
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
    · rw [max_eq_right (le_of_not_ge hlength), neg_zero, Real.rpow_zero, mul_one]
      have hcoeff : Cabs * P ^ 2 ≤
          C * P ^ 2 * Z ^ ε * (1 + ‖s.time‖) ^ n := by
        calc
          _ ≤ C * P ^ 2 := mul_le_mul_of_nonneg_right hCabsC (sq_nonneg P)
          _ ≤ (C * P ^ 2) * (Z ^ ε * (1 + ‖s.time‖) ^ n) := by
            apply le_mul_of_one_le_right (mul_nonneg hC.le (sq_nonneg P))
            exact one_le_mul_of_one_le_of_one_le hpower hheight
          _ = _ := by ring
      exact (habs s).2.trans (mul_le_mul_of_nonneg_right hcoeff s.rawMass_nonneg)

end Uniform

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.masked_volume_of_single_series
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.exists_original_source_bounds_supported
