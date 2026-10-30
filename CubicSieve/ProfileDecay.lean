import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicDerivativeBounds

/-! Mild growth at zero and rapid decay at infinity of actual annular-test
Fourier sheets. The small-radius estimate integrates the entire norm-one group;
it does not replace that integral by a bounded compact-group average. -/

set_option autoImplicit false
noncomputable section

namespace CubicSieve.Profile

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open scoped Classical NumberField

theorem decay_of_two_powers (f : ℝ → ℝ) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ r > 0, f r ≤ C₁ * r ^ (-(1 / 6 : ℝ)))
    (h₂ : ∀ r > 0, f r ≤ C₂ * r ^ (-(19 / 6 : ℝ))) :
    ∀ r > 0, f r ≤ (8 * (C₁ + C₂)) * r ^ (-(1 / 6 : ℝ)) / (1 + r) ^ 3 := by
  intro r hr
  have hd : 0 < (1 + r) ^ 3 := by positivity
  have hp : 0 ≤ r ^ (-(1 / 6 : ℝ)) := Real.rpow_nonneg hr.le _
  apply (le_div_iff₀ hd).mpr
  by_cases hsmall : r ≤ 1
  · have hcube : (1 + r) ^ 3 ≤ (8 : ℝ) := by
      calc (1 + r) ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr; linarith
           _ = 8 := by norm_num
    calc
      f r * (1 + r) ^ 3 ≤ (C₁ * r ^ (-(1 / 6 : ℝ))) * (1 + r) ^ 3 :=
        mul_le_mul_of_nonneg_right (h₁ r hr) hd.le
      _ ≤ (C₁ * r ^ (-(1 / 6 : ℝ))) * 8 :=
        mul_le_mul_of_nonneg_left hcube (mul_nonneg hC₁ hp)
      _ ≤ 8 * (C₁ + C₂) * r ^ (-(1 / 6 : ℝ)) := by nlinarith
  · have hlarge : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hcube : (1 + r) ^ 3 ≤ 8 * r ^ 3 := by
      calc (1 + r) ^ 3 ≤ (2 * r) ^ 3 := by gcongr; linarith
           _ = 8 * r ^ 3 := by ring
    have hp₂ : 0 ≤ r ^ (-(19 / 6 : ℝ)) := Real.rpow_nonneg hr.le _
    have hpow : r ^ (-(19 / 6 : ℝ)) * r ^ (3 : ℕ) = r ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]
      norm_num
    calc
      f r * (1 + r) ^ 3 ≤ (C₂ * r ^ (-(19 / 6 : ℝ))) * (1 + r) ^ 3 :=
        mul_le_mul_of_nonneg_right (h₂ r hr) hd.le
      _ ≤ (C₂ * r ^ (-(19 / 6 : ℝ))) * (8 * r ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (mul_nonneg hC₂ hp₂)
      _ = 8 * C₂ * r ^ (-(1 / 6 : ℝ)) := by rw [show
          (C₂ * r ^ (-(19 / 6 : ℝ))) * (8 * r ^ 3) =
            (8 * C₂) * (r ^ (-(19 / 6 : ℝ)) * r ^ (3 : ℕ)) by ring, hpow]
      _ ≤ 8 * (C₁ + C₂) * r ^ (-(1 / 6 : ℝ)) := by nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- A proved all-radius norm-integral bound, for every logarithmic derivative
of the Fourier transform of an actual compact annular tensor. -/
theorem sheet_log_derivative_decay
    (A : SArithmeticData K)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion K) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct K A.Sf) (borel _))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct K A.Sf) _ _ (borel _) μ)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (w : InfinitePlace K)
    (W₀ : SLocalProduct K A.Sf → ℂ)
    (hW₀ : ProbeWeight.IsAnnularTensor K A.Sf W₀)
    (hcompact : HasCompactSupport W₀) (hannular : tsupport W₀ ⊆ {x | IsUnit x})
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r > 0,
      Integrable (fun t => ProbeSheetFourierMellinBounds.logDerivativeRaw A w k
        (ProbeWeight.fourier K A.Sf e μ W₀)
        (ProbeSheetFourierMellinBounds.sheetPointRaw A r t).val) dt ∧
      (∫ t, ‖ProbeSheetFourierMellinBounds.logDerivativeRaw A w k
        (ProbeWeight.fourier K A.Sf e μ W₀)
        (ProbeSheetFourierMellinBounds.sheetPointRaw A r t).val‖ ∂dt) ≤
          C * r ^ (-(1 / 6 : ℝ)) / (1 + r) ^ 3 := by
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  obtain ⟨C₁, hC₁, h₁⟩ := ProbeSheetFourierMellinBounds.sheet_log_derivative_bounds
    A e he hne μ dt hμ hdt w W₀ hW₀ hcompact hannular (1 / 6) k (by norm_num)
  obtain ⟨C₂, hC₂, h₂⟩ := ProbeSheetFourierMellinBounds.sheet_log_derivative_bounds
    A e he hne μ dt hμ hdt w W₀ hW₀ hcompact hannular (19 / 6) k (by norm_num)
  refine ⟨8 * (C₁ + C₂), by positivity, fun r hr => ⟨(h₁ r hr).1, ?_⟩⟩
  exact decay_of_two_powers _ C₁ C₂ hC₁ hC₂
    (fun s hs => (h₁ s hs).2) (fun s hs => (h₂ s hs).2) r hr

end CubicSieve.Profile
