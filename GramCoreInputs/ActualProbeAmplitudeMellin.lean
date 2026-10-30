import ActualProbeLogProfile
import ActualAdditiveGramAmplitude

/-!
UNCOMPILED / native 0. The actual fixed-frequency denominator column is
expanded into the original additive amplitude with c=1. Standard Mathlib
Fourier frequency xi corresponds to nu=2*pi*xi; no 1/(2*pi) substitution
is silently made. The outer theta sum and fundamental-domain integral are
not rearranged here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S

/-- Positive real cpow gives precisely the positive inverse-Fourier phase. -/
theorem cpow_central_line_eq_fourierChar {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    (y : ℂ) ^ ((-1 : ℂ) + Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) =
      (y : ℂ)⁻¹ * (Real.fourierChar (ξ * Real.log y) : ℂ) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_add _ _ hyC, Complex.cpow_neg_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hyC, ← Complex.ofReal_log hy.le,
    Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem integrable_probeLogFourier_phase (P : ProbeData K S) (x : G) (v : ℝ) :
    Integrable (fun ξ : ℝ =>
      Real.fourierChar (ξ * v) • (𝓕 (probeLogSchwartz K S P x)) ξ) := by
  apply (probeLogSchwartz_fourier_integrable K S P x).mono
  · exact ((Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const)).smul
        (𝓕 (probeLogSchwartz K S P x)).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ξ =>
      le_of_eq (Circle.norm_smul _ _))

private theorem gramTerm_central_line (P : ProbeData K S) (Y ξ : ℝ)
    (hY : 0 < Y) (m : S.integer K) (I : ExteriorIdeal K S) :
    actualAdditiveGramTerm K S P (fun _ => 1)
        P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m I =
      (P.denominator.toFun (exteriorNorm K S I / Y) *
        ((exteriorNorm K S I / Y : ℝ) : ℂ)⁻¹ * probeGauss K S P I (-m)) *
        (Real.fourierChar (ξ * Real.log (exteriorNorm K S I / Y)) : ℂ) := by
  have hq : 0 < exteriorNorm K S I := by
    change (0 : ℝ) < (I.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
  rw [actualAdditiveGramTerm,
    cpow_central_line_eq_fourierChar (div_pos hq hY)]
  ring

/-- Actual finite ideal/Fourier interchange. The coefficient is literally one. -/
theorem integral_probeLogFourier_mul_amplitude (P : ProbeData K S)
    (x : G) (Y : ℝ) (hY : 0 < Y) (m : S.integer K) :
    (∫ ξ : ℝ, (𝓕 (probeLogSchwartz K S P x)) ξ *
      actualAdditiveGramAmplitude K S P (fun _ => 1)
        P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m) =
      additiveGramCentralNormalization Y *
        ∑ I ∈ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y,
          P.denominator.toFun (exteriorNorm K S I / Y) *
            ((exteriorNorm K S I / Y : ℝ) : ℂ)⁻¹ * probeGauss K S P I (-m) *
            probeRawLogProfile K S P x (Real.log (exteriorNorm K S I / Y)) := by
  let E := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
  let b : ExteriorIdeal K S → ℂ := fun I =>
    P.denominator.toFun (exteriorNorm K S I / Y) *
      ((exteriorNorm K S I / Y : ℝ) : ℂ)⁻¹ * probeGauss K S P I (-m)
  let f : ExteriorIdeal K S → ℝ → ℂ := fun I ξ =>
    b I * (Real.fourierChar (ξ * Real.log (exteriorNorm K S I / Y)) •
      (𝓕 (probeLogSchwartz K S P x)) ξ)
  have hf (I : ExteriorIdeal K S) : Integrable (f I) :=
    (integrable_probeLogFourier_phase K S P x _).const_mul (b I)
  have he (ξ : ℝ) :
      (𝓕 (probeLogSchwartz K S P x)) ξ *
          actualAdditiveGramAmplitude K S P (fun _ => 1)
            P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m =
        additiveGramCentralNormalization Y * ∑ I ∈ E, f I ξ := by
    rw [actualAdditiveGramAmplitude_eq_sum K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y _ hY m]
    calc
      _ = additiveGramCentralNormalization Y *
          ((𝓕 (probeLogSchwartz K S P x)) ξ *
            ∑ I ∈ E, actualAdditiveGramTerm K S P (fun _ => 1)
              P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m I) := by
        dsimp only [E]
        ring
      _ = _ := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro I hI
        rw [gramTerm_central_line K S P Y ξ hY m I]
        simp only [f, b, Circle.smul_def, smul_eq_mul]
        ring
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum E (fun I _ => hf I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  change (∫ ξ : ℝ, b I *
      (Real.fourierChar (ξ * Real.log (exteriorNorm K S I / Y)) •
        (𝓕 (probeLogSchwartz K S P x)) ξ)) = _
  rw [integral_const_mul, ← probeLogSchwartz_inversion]
  by_cases hW : P.denominator.toFun (exteriorNorm K S I / Y) = 0
  · simp only [b, hW, zero_mul]
  · rw [probeLogSchwartz_log_eq K S P x hW]

/-- The spectral integral above is genuinely integrable, not only totalized. -/
theorem integrable_probeLogFourier_mul_amplitude (P : ProbeData K S)
    (x : G) (Y : ℝ) (hY : 0 < Y) (m : S.integer K) :
    Integrable (fun ξ : ℝ => (𝓕 (probeLogSchwartz K S P x)) ξ *
      actualAdditiveGramAmplitude K S P (fun _ => 1)
        P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m) := by
  have hi (I : ExteriorIdeal K S) : Integrable (fun ξ : ℝ =>
      (𝓕 (probeLogSchwartz K S P x)) ξ *
        actualAdditiveGramTerm K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m I) := by
    have h := (integrable_probeLogFourier_phase K S P x
      (Real.log (exteriorNorm K S I / Y))).const_mul
        (P.denominator.toFun (exteriorNorm K S I / Y) *
          ((exteriorNorm K S I / Y : ℝ) : ℂ)⁻¹ * probeGauss K S P I (-m))
    convert h using 1
    funext ξ
    rw [gramTerm_central_line K S P Y ξ hY m I]
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  have hsum := (integrable_finsetSum
    (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y)
    (fun I _ => hi I)).const_mul (additiveGramCentralNormalization Y)
  convert hsum using 1
  funext ξ
  rw [actualAdditiveGramAmplitude_eq_sum K S P (fun _ => 1)
    P.denominator.toSmoothAnnularTest Y _ hY m]
  calc
    _ = additiveGramCentralNormalization Y *
        ((𝓕 (probeLogSchwartz K S P x)) ξ *
          ∑ I ∈ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y,
            actualAdditiveGramTerm K S P (fun _ => 1)
              P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m I) := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- Real scalar normalization of the literal two square-root weights. -/
theorem probe_column_real_normalization {X Y q : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hq : 0 < q) :
    Y⁻¹ * (Real.sqrt (q * X))⁻¹ * (Real.sqrt q)⁻¹ =
      (X * Y) ^ (-(1 / 2 : ℝ)) * Y ^ (-(3 / 2 : ℝ)) * (q / Y)⁻¹ := by
  have hhalf (z : ℝ) (hz : 0 < z) :
      z ^ (-(1 / 2 : ℝ)) = (Real.sqrt z)⁻¹ := by
    rw [Real.rpow_neg hz.le, Real.sqrt_eq_rpow]
  have hthree : Y ^ (-(3 / 2 : ℝ)) = Y⁻¹ * (Real.sqrt Y)⁻¹ := by
    calc
      _ = Y ^ ((-1 : ℝ) + -(1 / 2 : ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hY, Real.rpow_neg_one, hhalf Y hY]
  have hqinv : (Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹ = q⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hq.le]
  have hYinv : (Real.sqrt Y)⁻¹ * (Real.sqrt Y)⁻¹ = Y⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hY.le]
  rw [hhalf (X * Y) (mul_pos hX hY), hthree,
    Real.sqrt_mul hq.le, Real.sqrt_mul hX.le]
  simp only [mul_inv_rev, div_eq_mul_inv, inv_inv]
  calc
    _ = (Real.sqrt X)⁻¹ * Y⁻¹ * ((Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹) := by ring
    _ = (Real.sqrt X)⁻¹ * Y⁻¹ * q⁻¹ := by rw [hqinv]
    _ = (Real.sqrt X)⁻¹ * q⁻¹ *
        ((Real.sqrt Y)⁻¹ * (Real.sqrt Y)⁻¹) * (Y⁻¹ * Y) := by
      rw [hYinv, inv_mul_cancel₀ hY.ne']
      ring
    _ = _ := by ring

/-- Base point before the logarithmic ideal-norm displacement. -/
def probeColumnBasePoint (m : NonzeroRingElements (S.integer K))
    (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) : G :=
  sLocalNonzeroIntegerDiagonal K S m /
    ((t : G) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩)

/-- The actual fixed-m denominator column, before multiplying by completedThetaSum.
All exterior ideals, original negative Gauss frequencies and both sqrt weights remain.
No finite-ray, theta-reflection or Gram bound is an input. -/
theorem probe_fixed_frequency_column_eq_amplitude_integral (P : ProbeData K S)
    (m : NonzeroRingElements (S.integer K)) (t : sLocalNormOneGroup K S)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (∑' I : ExteriorIdeal K S,
      (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
        (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
        (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ * probeGauss K S P I (-m.val) *
        additiveTest K S P.additive
          (sLocalNonzeroIntegerDiagonal K S m /
            ((t : G) * sLocalNormSection K S
              ⟨exteriorNorm K S I * X,
                mul_pos (by
                  change (0 : ℝ) < (I.val.val.absNorm : ℝ)
                  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val) hX⟩))) =
      (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ ξ : ℝ,
          (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
            actualAdditiveGramAmplitude K S P (fun _ => 1)
              P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val := by
  rw [integral_probeLogFourier_mul_amplitude K S P
    (probeColumnBasePoint K S m t X Y hX hY) Y hY m.val]
  rw [tsum_eq_sum (s := additiveGramIdealSupport K S
    P.denominator.toSmoothAnnularTest Y) (fun I hI => ?_)]
  · rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    have hq : 0 < exteriorNorm K S I := by
      change (0 : ℝ) < (I.val.val.absNorm : ℝ)
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
    rw [probeColumnBasePoint, probeRawLogProfile_original_scale K S P m t X Y _ hX hY hq]
    have hn := congrArg (fun z : ℝ => (z : ℂ))
      (probe_column_real_normalization hX hY hq)
    push_cast at hn
    let A : ℂ := additiveTest K S P.additive
      (sLocalNonzeroIntegerDiagonal K S m /
        ((t : G) * sLocalNormSection K S
          ⟨exteriorNorm K S I * X, mul_pos hq hX⟩))
    change (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
        (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
        (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ * probeGauss K S P I (-m.val) * A =
      (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((Y ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      (P.denominator.toFun (exteriorNorm K S I / Y) *
        ((exteriorNorm K S I / Y : ℝ) : ℂ)⁻¹ * probeGauss K S P I (-m.val) * A)
    calc
      _ = ((Y : ℂ)⁻¹ * (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
          (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹) *
          (P.denominator.toFun (exteriorNorm K S I / Y) * probeGauss K S P I (-m.val) * A) := by ring
      _ = _ := by
        rw [hn]
        push_cast
        ring
  · have hW : P.denominator.toFun (exteriorNorm K S I / Y) = 0 := by
      by_contra hW
      apply hI
      apply (mem_additiveGramIdealSupport_iff K S P.denominator.toSmoothAnnularTest Y hY I).mpr
      exact (div_le_iff₀ hY).mp (P.denominator.support hW).2
    simp only [hW, mul_zero, zero_mul]

/-- The same identity with the original probeRowTerm, and its unchanged completed
theta factor. This does not interchange the outer frequency sum or Haar integral. -/
theorem probe_row_column_eq_amplitude_integral (P : ProbeData K S)
    (ψ : HeckeGeneral.Characters.HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (m : NonzeroRingElements (S.integer K))
    (t : sLocalNormOneGroup K S) (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (∑' I : ExteriorIdeal K S,
      (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
        (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
          probeRowTerm K S P ψ Q X Z t I m) =
      ((((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ ξ : ℝ,
          (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
            actualAdditiveGramAmplitude K S P (fun _ => 1)
              P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val) *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) Q logGaussianProfile Z := by
  have he (I : ExteriorIdeal K S) :
      (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
        (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
          probeRowTerm K S P ψ Q X Z t I m =
      ((Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
        (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
        (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ * probeGauss K S P I (-m.val) *
        additiveTest K S P.additive
          (sLocalNonzeroIntegerDiagonal K S m /
            ((t : G) * sLocalNormSection K S
              ⟨exteriorNorm K S I * X,
                mul_pos (by
                  change (0 : ℝ) < (I.val.val.absNorm : ℝ)
                  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val) hX⟩))) *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) Q logGaussianProfile Z := by
    have hq : 0 < exteriorNorm K S I := by
      change (0 : ℝ) < (I.val.val.absNorm : ℝ)
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
    rw [probeRowTerm, dif_pos (mul_pos hq hX)]
    ring
  simp_rw [he]
  rw [tsum_mul_right, probe_fixed_frequency_column_eq_amplitude_integral K S P m t X Y hX hY]

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
