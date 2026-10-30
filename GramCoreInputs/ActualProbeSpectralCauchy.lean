import ActualProbeSpectralFrequencyExpansion
import ActualProbeLogUniformFourier
import ActualProbeLogRowNormEnvelope
import ActualProbeSpectralOrbitSupport
import Mathlib.Analysis.Real.Sqrt

/-!
Uncompiled candidate. Cauchy-Schwarz for the literal separated probe rows.
One finite set, chosen before the frequency and the theta parameters, supports
the entire spectral sum and lies in the actual norm ball C*X*Y. The uniform
Fourier decay is proved by the imported construction, not assumed here.
The original endpoints retain their same S-integer energies. The new consumer
explicitly selects the geometric support and bounds both energies on the same
ORIGINAL sixth-unit orbit image. Reflected theta energy remains separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- Common support is genuinely finite by the full local compact support,
and the independently proved product-norm bound trims it to the row ball. -/
theorem exists_probeAmplitudeSpectralRow_bounded_common_support (P : ProbeData K S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ)
      (hX : 0 < X) (hY : 0 < Y), ∃ M : Finset NZ,
      (∀ m ∈ M, (sIntegerElementNorm K S m).val ≤ C * (X * Y)) ∧
      ∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
        (Z : ℝ) (ξ : ℝ) (m : NZ), m ∉ M →
        probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ = 0 := by
  obtain ⟨C, hC, hnorm⟩ := exists_probeLogSchwartz_row_norm_envelope K S P
  refine ⟨C, hC, ?_⟩
  intro t X Y hX hY
  obtain ⟨M₀, hM₀⟩ := exists_probeAmplitudeSpectralRow_common_support K S P t X Y hX hY
  let M := M₀.filter (fun m => (sIntegerElementNorm K S m).val ≤ C * (X * Y))
  refine ⟨M, fun m hm => (Finset.mem_filter.mp hm).2, ?_⟩
  intro ψ Q Z ξ m hm
  by_cases hm₀ : m ∈ M₀
  · have hlarge : C * (X * Y) < (sIntegerElementNorm K S m).val := by
      by_contra h
      exact hm (Finset.mem_filter.mpr ⟨hm₀, le_of_not_gt h⟩)
    have hz := (hnorm t X Y hX hY m hlarge).2
    simp only [probeAmplitudeSpectralRow, hz, SchwartzMap.zero_apply, zero_mul]
  · exact hM₀ ψ Q Z m hm₀ ξ

/-- The true spectral sum is bounded by the two literal energies on the
same finite row set. Both constants precede every moving target parameter;
M precedes the theta parameters and the Fourier frequency. -/
theorem exists_probeSpectral_cauchy_bound (P : ProbeData K S) (N : ℕ) :
    ∃ C Cball : ℝ, 0 ≤ C ∧ 0 < Cball ∧
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y),
      ∃ M : Finset NZ,
      (∀ m ∈ M, (sIntegerElementNorm K S m).val ≤ Cball * (X * Y)) ∧
      ∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z ξ : ℝ),
      (1 + |ξ|) ^ N *
        ‖∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
      C * Real.sqrt (∑ m ∈ M,
        ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2) *
        Real.sqrt (∑ m ∈ M,
          ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) Q logGaussianProfile Z‖ ^ 2) := by
  obtain ⟨C, hC, hFourier⟩ := exists_probeLogFourier_uniform_rapid_decay K S P N
  obtain ⟨Cball, hCball, hsupport⟩ :=
    exists_probeAmplitudeSpectralRow_bounded_common_support K S P
  refine ⟨C, Cball, hC, hCball, ?_⟩
  intro t X Y hX hY
  obtain ⟨M, hMnorm, hM⟩ := hsupport t X Y hX hY
  refine ⟨M, hMnorm, ?_⟩
  intro ψ Q Z ξ
  let a : NZ → ℝ := fun m =>
    ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖
  let b : NZ → ℝ := fun m =>
    ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
      (primeSetIdeal K S ∅) Q logGaussianProfile Z‖
  let w : ℝ := (1 + |ξ|) ^ N
  have hw : 0 ≤ w := pow_nonneg (by positivity) _
  have hrow (m : NZ) :
      w * ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
        C * (a m * b m) := by
    have hab : 0 ≤ a m * b m := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      _ = (w * ‖(𝓕 (probeLogSchwartz K S P
          (probeColumnBasePoint K S m t X Y hX hY))) ξ‖) * (a m * b m) := by
        simp only [probeAmplitudeSpectralRow, norm_mul, a, b]
        ring
      _ ≤ C * (a m * b m) := mul_le_mul_of_nonneg_right (hFourier _ ξ) hab
  rw [tsum_eq_sum (fun m hm => hM ψ Q Z ξ m hm)]
  change w * ‖∑ m ∈ M, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
    C * Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)
  calc
    _ ≤ w * (∑ m ∈ M, ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ m ∈ M, w * ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ m ∈ M, C * (a m * b m) := Finset.sum_le_sum (fun m _ => hrow m)
    _ = C * ∑ m ∈ M, a m * b m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt M a b) hC
    _ = _ := by ring

/-- Cauchy for any given finite support, with its Fourier constant chosen
before all row and theta parameters. The final geometric consumer supplies
this support from the actual compact shape. -/
theorem exists_probeSpectral_finite_cauchy_bound (P : ProbeData K S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
        (M : Finset NZ) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z ξ : ℝ),
      (∀ m : NZ, m ∉ M →
        probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ = 0) →
      (1 + |ξ|) ^ N *
        ‖∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
      C * Real.sqrt (∑ m ∈ M,
        ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
          P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2) *
        Real.sqrt (∑ m ∈ M,
          ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) Q logGaussianProfile Z‖ ^ 2) := by
  obtain ⟨C, hC, hFourier⟩ := exists_probeLogFourier_uniform_rapid_decay K S P N
  refine ⟨C, hC, ?_⟩
  intro t X Y hX hY M ψ Q Z ξ hM
  let a : NZ → ℝ := fun m =>
    ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖
  let b : NZ → ℝ := fun m =>
    ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
      (primeSetIdeal K S ∅) Q logGaussianProfile Z‖
  let w : ℝ := (1 + |ξ|) ^ N
  have hw : 0 ≤ w := pow_nonneg (by positivity) _
  have hrow (m : NZ) :
      w * ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
        C * (a m * b m) := by
    have hab : 0 ≤ a m * b m := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      _ = (w * ‖(𝓕 (probeLogSchwartz K S P
          (probeColumnBasePoint K S m t X Y hX hY))) ξ‖) * (a m * b m) := by
        simp only [probeAmplitudeSpectralRow, norm_mul, a, b]
        ring
      _ ≤ C * (a m * b m) := mul_le_mul_of_nonneg_right (hFourier _ ξ) hab
  rw [tsum_eq_sum (fun m hm => hM m hm)]
  change w * ‖∑ m ∈ M, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
    C * Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)
  calc
    _ ≤ w * (∑ m ∈ M, ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw
    _ = ∑ m ∈ M, w * ‖probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ m ∈ M, C * (a m * b m) := Finset.sum_le_sum (fun m _ => hrow m)
    _ = C * ∑ m ∈ M, a m * b m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt (∑ m ∈ M, a m ^ 2) * Real.sqrt (∑ m ∈ M, b m ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt M a b) hC
    _ = _ := by ring


/-- Actual same-M Cauchy on the SAME original sixth-power-unit orbit image.
The geometric M is selected explicitly from fixed compact shape, not from the
older norm/support-only existential. Its derived multiplicity B is absorbed
as C_F*B. No Gram, theta-energy or reflected-theta estimate is assumed. -/
theorem exists_probeSpectral_originalGamma_cauchy_bound (P : ProbeData K S) (N : ℕ) :
    ∃ C Cball : ℝ, 0 ≤ C ∧ 0 < Cball ∧
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y),
      ∃ M : Finset NZ,
        (∀ m ∈ M, (sIntegerElementNorm K S m).val ≤ Cball * (X * Y)) ∧
        (∀ q ∈ M.image (probeSixthOrbit K S),
          (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ Cball * (X * Y)) ∧
        ∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z ξ : ℝ),
        (1 + |ξ|) ^ N *
          ‖∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ‖ ≤
        C * Real.sqrt (∑ q ∈ M.image (probeSixthOrbit K S),
          ‖actualAdditiveGramOrbitAmplitude K S P (fun _ => 1)
            P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) q‖ ^ 2) *
          Real.sqrt (∑ q ∈ M.image (probeSixthOrbit K S),
            ‖probeCompletedThetaOrbit K S P ψ Q Z q‖ ^ 2) := by
  obtain ⟨CF, hCF, hfinite⟩ := exists_probeSpectral_finite_cauchy_bound K S P N
  obtain ⟨Cball, hCball, B, hgeometric⟩ := exists_probeSpectral_sameM_sector_support K S P
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  refine ⟨CF * (B : ℝ), Cball, mul_nonneg hCF hB, hCball, ?_⟩
  intro t X Y hX hY
  obtain ⟨M, hnorm, horbitnorm, hsupport, henergy⟩ := hgeometric t X Y hX hY
  refine ⟨M, hnorm, horbitnorm, ?_⟩
  intro ψ Q Z ξ
  have hcauchy := hfinite t X Y hX hY M ψ Q Z ξ
    (fun m hm => hsupport ψ Q Z ξ m hm)
  have he := henergy (fun _ => 1) P.denominator.toSmoothAnnularTest
    (2 * Real.pi * ξ) ψ Q Z
  let EA : ℝ := ∑ m ∈ M,
    ‖actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val‖ ^ 2
  let ET : ℝ := ∑ m ∈ M,
    ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
      (primeSetIdeal K S ∅) Q logGaussianProfile Z‖ ^ 2
  let EAO : ℝ := ∑ q ∈ M.image (probeSixthOrbit K S),
    ‖actualAdditiveGramOrbitAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) q‖ ^ 2
  let ETO : ℝ := ∑ q ∈ M.image (probeSixthOrbit K S),
    ‖probeCompletedThetaOrbit K S P ψ Q Z q‖ ^ 2
  have hEA : EA ≤ (B : ℝ) * EAO := he.1
  have hET : ET ≤ (B : ℝ) * ETO := he.2
  calc
    _ ≤ CF * Real.sqrt EA * Real.sqrt ET := hcauchy
    _ ≤ CF * Real.sqrt ((B : ℝ) * EAO) * Real.sqrt ET :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEA) hCF) (Real.sqrt_nonneg _)
    _ ≤ CF * Real.sqrt ((B : ℝ) * EAO) * Real.sqrt ((B : ℝ) * ETO) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hET)
        (mul_nonneg hCF (Real.sqrt_nonneg _))
    _ = CF * (Real.sqrt (B : ℝ) * Real.sqrt EAO) *
        (Real.sqrt (B : ℝ) * Real.sqrt ETO) := by
      rw [Real.sqrt_mul hB, Real.sqrt_mul hB]
    _ = (CF * (Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ))) *
        Real.sqrt EAO * Real.sqrt ETO := by ring
    _ = _ := by rw [Real.mul_self_sqrt hB]

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
