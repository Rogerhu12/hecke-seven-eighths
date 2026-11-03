import ActualGramZeroFrequency
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.ActualPrimeGeometryAbsoluteBound

/-!
Uncompiled candidate. The literal zero-frequency diagonal has size O(Y^2),
uniformly in the Mellin frequency, the probe generators, and coefficients
bounded by one. The linear ideal count and the annular test bound are proved
inputs from the main library. With the original central factor Y^(-3), this
is the O(1/Y) diagonal contribution. No sign of a Fourier majorant is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The phase on the central line contributes only the inverse real radius. -/
private theorem norm_cpow_central_line {y : ℝ} (hy : 0 < y) (ν : ℝ) :
    ‖(y : ℂ) ^ ((-1 : ℂ) + Complex.I * (ν : ℂ))‖ = y⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, Real.rpow_neg_one]

/-- Uniform bound on the actual diagonal coefficient. Annular support
controls the inverse radius even for an ideal outside the finite envelope. -/
theorem norm_actualAdditiveGramPairCoefficient_self_le
    (c : ExteriorIdeal K SF → ℂ) (hc : ∀ I, ‖c I‖ ≤ 1)
    (W : SmoothAnnularTest) (B : ℝ) (hB : 0 ≤ B)
    (hWB : ∀ y, ‖W.toFun y‖ ≤ B) (Y ν : ℝ) (hY : 0 < Y)
    (I : ExteriorIdeal K SF) :
    ‖actualAdditiveGramPairCoefficient K SF c W Y ν I I‖ ≤
      B ^ 2 * (W.lower⁻¹) ^ 2 := by
  by_cases hW : W.toFun (exteriorNorm K SF I / Y) = 0
  · simp only [actualAdditiveGramPairCoefficient, hW, zero_mul, mul_zero, norm_zero]
    positivity
  have hq : 0 < exteriorNorm K SF I := by
    change (0 : ℝ) < (I.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
  have hy : 0 < exteriorNorm K SF I / Y := div_pos hq hY
  have hlo : W.lower ≤ exteriorNorm K SF I / Y := (W.support hW).1
  have hi : (exteriorNorm K SF I / Y)⁻¹ ≤ W.lower⁻¹ :=
    (inv_le_inv₀ hy W.lower_pos).mpr hlo
  have hc2 : ‖c I‖ * ‖c I‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (hc I) (hc I) (norm_nonneg _) zero_le_one
  have hW2 : ‖W.toFun (exteriorNorm K SF I / Y)‖ *
      ‖W.toFun (exteriorNorm K SF I / Y)‖ ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul (hWB _) (hWB _) (norm_nonneg _) hB
  have hi2 : (exteriorNorm K SF I / Y)⁻¹ *
      (exteriorNorm K SF I / Y)⁻¹ ≤ (W.lower⁻¹) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi hi (inv_nonneg.mpr hy.le)
      (inv_nonneg.mpr W.lower_pos.le)
  calc
    _ = (‖c I‖ * ‖c I‖) *
        (‖W.toFun (exteriorNorm K SF I / Y)‖ *
          ‖W.toFun (exteriorNorm K SF I / Y)‖) *
        ((exteriorNorm K SF I / Y)⁻¹ * (exteriorNorm K SF I / Y)⁻¹) := by
      simp only [actualAdditiveGramPairCoefficient, norm_mul, Complex.norm_conj,
        norm_cpow_central_line hy]
    _ ≤ (1 * B ^ 2) * (W.lower⁻¹) ^ 2 :=
      mul_le_mul (mul_le_mul hc2 hW2 (mul_self_nonneg _) zero_le_one)
        hi2 (mul_self_nonneg _) (by positivity)
    _ = _ := by rw [one_mul]

/-- Actual ideal counting yields the full diagonal bound; its constant is
chosen before P, the coefficients, Y and nu. -/
theorem exists_actualGramDiagonal_norm_bound (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ),
      (∀ I, ‖c I‖ ≤ 1) → ∀ Y ν : ℝ, Y₀ ≤ Y →
      ‖∑ I ∈ additiveGramIdealSupport K SF W Y,
        actualAdditiveGramPairCoefficient K SF c W Y ν I I *
          (additiveGramDiagonalUnitCount K S P I : ℂ)‖ ≤ C * Y ^ 2 := by
  obtain ⟨B, hB, hWB⟩ := smoothAnnularTest_exists_pos_norm_bound W
  obtain ⟨C₀, hC₀, hcount⟩ := dyadicIdealSupport_linear_count K
  have hu : 0 < W.upper := W.lower_pos.trans_le W.upper_ge
  let A : ℝ := B ^ 2 * (W.lower⁻¹) ^ 2
  have hA : 0 < A := mul_pos (sq_pos_of_pos hB) (sq_pos_of_pos (inv_pos.mpr W.lower_pos))
  refine ⟨C₀ * A * W.upper ^ 2, max 1 W.upper⁻¹, by positivity,
    le_max_left _ _, ?_⟩
  intro P c hc Y ν hY₀
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hY₀)
  have huY : 1 ≤ W.upper * Y :=
    (inv_le_iff_one_le_mul₀' hu).mp ((le_max_right _ _).trans hY₀)
  let F := additiveGramIdealSupport K SF W Y
  have hcard : (F.card : ℝ) ≤ C₀ * (W.upper * Y) := by
    have hf : F.card ≤ (dyadicIdealSupport K (W.upper * Y / 2)).card := by
      dsimp only [F, additiveGramIdealSupport]
      rw [Finset.card_subtype]
      exact Finset.card_filter_le _ _
    exact (Nat.cast_le.mpr hf).trans (hcount _ huY)
  have hterm (I : ExteriorIdeal K SF) (hI : I ∈ F) :
      ‖actualAdditiveGramPairCoefficient K SF c W Y ν I I *
        (additiveGramDiagonalUnitCount K S P I : ℂ)‖ ≤ A * (W.upper * Y) := by
    have huI := (mem_additiveGramIdealSupport_iff K SF W Y hY I).mp hI
    have hunit := (additiveGramDiagonalUnitCount_le_norm K S P I).trans huI
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul
      (norm_actualAdditiveGramPairCoefficient_self_le K S c hc W B hB.le hWB Y ν hY I)
      hunit (Nat.cast_nonneg _) hA.le
  calc
    _ ≤ ∑ I ∈ F, A * (W.upper * Y) := norm_sum_le_of_le _ hterm
    _ = (F.card : ℝ) * (A * (W.upper * Y)) := by simp
    _ ≤ (C₀ * (W.upper * Y)) * (A * (W.upper * Y)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C₀ * A * W.upper ^ 2) * Y ^ 2 := by ring

/-- The exact original central normalization turns the diagonal estimate
into O(1/Y). This is uniform in the original Mellin parameter. -/
theorem exists_actualGramNormalizedDiagonal_norm_bound (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ),
      (∀ I, ‖c I‖ ≤ 1) → ∀ Y ν : ℝ, Y₀ ≤ Y →
      ‖((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y ν I I *
            (additiveGramDiagonalUnitCount K S P I : ℂ))‖ ≤ C / Y := by
  obtain ⟨C, Y₀, hC, hY₀, hbound⟩ := exists_actualGramDiagonal_norm_bound K S W
  refine ⟨C, Y₀, hC, hY₀, ?_⟩
  intro P c hc Y ν hY
  have hYpos : 0 < Y := zero_lt_one.trans_le (hY₀.trans hY)
  have hz : 0 ≤ Y ^ (-3 : ℝ) := Real.rpow_nonneg hYpos.le _
  have hpow : Y ^ (-3 : ℝ) = (Y ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hYpos.le]
    norm_num
  have hscale : Y ^ (-3 : ℝ) * Y ^ 2 = Y⁻¹ := by
    rw [hpow]
    field_simp [hYpos.ne']
    <;> ring
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hz]
  calc
    _ ≤ Y ^ (-3 : ℝ) * (C * Y ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound P c hc Y ν hY) hz
    _ = C * (Y ^ (-3 : ℝ) * Y ^ 2) := by ring
    _ = C / Y := by rw [hscale, div_eq_mul_inv]

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
