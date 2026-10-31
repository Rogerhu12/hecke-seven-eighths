import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger
import HeckePort.Moments.Height

/-!
# Centered exceptional amplitudes on a finite row set

The centered estimate is applied to one whole normalized difference of
the actual twisted masked ideal sums.  It is paired with the bound on the
other side before summing rows.  Thus the centered saving occurs once,
as required by the exceptional ledger, rather than being squared twice.
The analytic volume and profile-error inputs are exactly those of the
existing `HeckePort.Moments.normalized_masked_rectangle_estimate`.
-/

noncomputable section
open scoped NumberField Classical BigOperators SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open HeckePort.CenteredMomentVolume HeckePort.Moments.Twist

theorem finite_paired_norm_bound {ι : Type*} (rows : Finset ι) (left right : ι → ℂ)
    (L R : ℝ) (hL : 0 ≤ L)
    (hleft : ∀ i ∈ rows, ‖left i‖ ≤ L) (hright : ∀ i ∈ rows, ‖right i‖ ≤ R) :
    (∑ i ∈ rows, ‖left i‖ * ‖right i‖) ≤ (rows.card : ℝ) * L * R := by
  have h := Finset.sum_le_sum (s := rows) (fun i hi =>
    mul_le_mul (hleft i hi) (hright i hi) (norm_nonneg _) hL)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

/-- Combine an actual finite row count with the two amplitude bounds. -/
theorem finite_paired_power_bound {ι : Type*} (rows : Finset ι) (left right : ι → ℂ)
    (Z Crows Cleft Cright rowExp leftExp rightExp : ℝ) (hZ : 1 ≤ Z)
    (hCleft : 0 ≤ Cleft) (hCright : 0 ≤ Cright)
    (hrows : (rows.card : ℝ) ≤ Crows * Z ^ rowExp)
    (hleft : ∀ i ∈ rows, ‖left i‖ ≤ Cleft * Z ^ leftExp)
    (hright : ∀ i ∈ rows, ‖right i‖ ≤ Cright * Z ^ rightExp) :
    (∑ i ∈ rows, ‖left i‖ * ‖right i‖) ≤
      (Crows * Cleft * Cright) * Z ^ (rowExp + leftExp + rightExp) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hL : 0 ≤ Cleft * Z ^ leftExp :=
    mul_nonneg hCleft (Real.rpow_nonneg hZpos.le _)
  have hR : 0 ≤ Cright * Z ^ rightExp :=
    mul_nonneg hCright (Real.rpow_nonneg hZpos.le _)
  calc
    _ ≤ (rows.card : ℝ) * (Cleft * Z ^ leftExp) * (Cright * Z ^ rightExp) :=
      finite_paired_norm_bound rows left right _ _ hL hleft hright
    _ ≤ (Crows * Z ^ rowExp) * (Cleft * Z ^ leftExp) * (Cright * Z ^ rightExp) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrows hL) hR
    _ = _ := by
      rw [Real.rpow_add hZpos, Real.rpow_add hZpos]
      ring

/-- The first and second savings close the centered exceptional exponent. -/
theorem exceptional_paired_exponent (A M c w b₂ v F₁ F₂ σ δ : ℝ)
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - 5 * δ / 6 ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) (hv : v ≤ c + w + b₂) :
    A - 5 * M / 6 - F₁ - F₂ - max (M / 4 - v) 0 ≤
      max (A - M) 0 + 3 * σ + 5 * δ / 6 := by
  have h := centered_exceptional_ledger A M v
  linarith

variable {K : Type*} [Field K] [NumberField K]

/-- The literal normalized centered product of two twisted masked ideal sums. -/
def normalizedMaskedRectangle (Ψ : Ideal (𝓞 K) →* ℂ) (R : Ideal (𝓞 K))
    (W₁ W₂ : ℝ → ℂ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt T : ℂ)⁻¹ *
    (twistedMaskedSum Ψ R W₁ t X₁ * twistedMaskedSum Ψ R W₂ t X₂ -
      twistedMaskedSum Ψ R W₁ t Y₁ * twistedMaskedSum Ψ R W₂ t Y₂)

/-- Uniformly pair the actual centered rectangle with the other amplitude
on any finite set of rows.  The common product and all four formal scales
are retained, including their exact equality. -/
theorem masked_centered_paired_rows {ι : Type*}
    {Ψ : Ideal (𝓞 K) →* ℂ} (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (V : IdealVolumeInput K Ψ) (W₁ W₂ : ℝ → ℂ)
    (a₁ b₁ a₂ b₂ M₁ M₂ ε B : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hε : 0 < ε) (hB : 0 ≤ B)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (prof₁ prof₂ : ℝ → 𝓢(ℝ, ℂ))
    (hprof₁ : ∀ t x, prof₁ t x = (x : ℂ) ^ (Complex.I * t) * W₁ x)
    (hprof₂ : ∀ t x, prof₂ t x = (x : ℂ) ^ (Complex.I * t) * W₂ x)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (n₁ n₂ : ℕ) (D₁ D₂ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (herr₁ : ∀ t : ℝ, V.error (prof₁ t) ≤ D₁ * (1 + ‖t‖) ^ n₁)
    (herr₂ : ∀ t : ℝ, V.error (prof₂ t) ≤ D₂ * (1 + ‖t‖) ^ n₂) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ (rows : Finset ι) (R : ι → Ideal (𝓞 K)) (t : ι → ℝ),
        (∀ i ∈ rows, R i ≠ ⊥) → (∀ i ∈ rows, (Ideal.absNorm (R i) : ℝ) ≤ Z ^ B) →
        ∀ height : ℝ, 0 ≤ height → (∀ i ∈ rows, ‖t i‖ ≤ height) →
        ∀ X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
          L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
        ∀ (right : ι → ℂ) (U : ℝ),
          (∀ i ∈ rows, ‖right i‖ ≤ U) →
          (∑ i ∈ rows, ‖normalizedMaskedRectangle Ψ (R i) W₁ W₂ (t i) X₁ X₂ Y₁ Y₂ T‖ *
            ‖right i‖) ≤
            (rows.card : ℝ) * (C * Z ^ ε * (1 + height) ^ J * (Real.sqrt T / L)) * U := by
  obtain ⟨J, C, hC, hrect⟩ := HeckePort.Moments.normalized_masked_rectangle_estimate
    hΨ hΨ0 V W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂ ε B ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hε hB
    hs₁ hs₂ prof₁ prof₂ hprof₁ hprof₂ hbound₁ hbound₂ n₁ n₂ D₁ D₂ hD₁ hD₂ herr₁ herr₂
  refine ⟨J, C, hC, ?_⟩
  intro Z hZ rows R t hR hRnorm height hheight ht X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY right U hright
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  have hbound : 0 ≤ C * Z ^ ε * (1 + height) ^ J * (Real.sqrt T / L) := by
    positivity
  apply finite_paired_norm_bound rows _ right _ U hbound _ hright
  intro i hi
  have h := hrect Z hZ (R i) (hR i hi) (hRnorm i hi) (t i) X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : (1 + ‖t i‖) ^ J ≤ (1 + height) ^ J :=
    pow_le_pow_left₀ (by positivity) (by linarith [ht i hi]) J
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hz)) hratio)

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.finite_paired_power_bound
#print axioms HeckeSkeleton.Moments.EngineStep.exceptional_paired_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.masked_centered_paired_rows
