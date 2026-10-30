import ActualProbeFiniteFrequencyExpansion

/-!
UNCOMPILED candidate. A compact enlargement of the actual additive support
contains every nonzero logarithmic profile. At fixed t,X,Y this gives a
single finite set of S-integer frequencies for every Fourier parameter.
The resulting frequency/Fourier interchange is genuinely finite, and its
integrability is proved from the actual Schwartz profiles. No theta energy,
Gram estimate, or outer Haar interchange is asserted here.
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
local notation "G" => sLocalMultiplicativeGroup K S
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- Undo the logarithmic displacement only over its actual compact support. -/
def probeLogSpatialSupport (P : ProbeData K S) : Set G :=
  (fun p : ℝ × G =>
    (sLocalNormSection K S ⟨Real.exp (-p.1), Real.exp_pos _⟩)⁻¹ * p.2) ''
      (tsupport (denominatorLogCutoff P.denominator.toSmoothAnnularTest) ×ˢ
        tsupport (additiveTest K S P.additive))

theorem isCompact_probeLogSpatialSupport (P : ProbeData K S) :
    IsCompact (probeLogSpatialSupport K S P) := by
  have hrad : Continuous (fun p : ℝ × G =>
      (⟨Real.exp (-p.1), Real.exp_pos _⟩ : {r : ℝ // 0 < r})) :=
    (Real.continuous_exp.comp continuous_fst.neg).subtype_mk _
  exact ((denominatorLogCutoff P.denominator.toSmoothAnnularTest).hasCompactSupport.isCompact.prod
    P.additive.tensor_compactSupport.isCompact).image
      (((continuous_sLocalNormSection K S).comp hrad).inv.mul continuous_snd)

theorem probeLogSchwartz_eq_zero_of_not_mem (P : ProbeData K S) (x : G)
    (hx : x ∉ probeLogSpatialSupport K S P) : probeLogSchwartz K S P x = 0 := by
  apply SchwartzMap.ext
  intro v
  by_cases hc : denominatorLogCutoff P.denominator.toSmoothAnnularTest v = 0
  · simp only [probeLogSchwartz_apply, probeCutLogProfile, hc, zero_smul,
      SchwartzMap.zero_apply]
  by_cases hf : additiveTest K S P.additive
      (sLocalNormSection K S ⟨Real.exp (-v), Real.exp_pos _⟩ * x) = 0
  · simp only [probeLogSchwartz_apply, probeCutLogProfile, probeRawLogProfile,
      hf, smul_zero, SchwartzMap.zero_apply]
  exfalso
  apply hx
  refine ⟨(v, sLocalNormSection K S ⟨Real.exp (-v), Real.exp_pos _⟩ * x),
    ⟨subset_closure hc, subset_closure hf⟩, ?_⟩
  simp only [inv_mul_cancel_left]

/-- This finite set precedes the Fourier frequency and every theta parameter. -/
theorem exists_probeLogFourier_common_frequency_support (P : ProbeData K S)
    (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    ∃ M : Finset NZ, ∀ m : NZ, m ∉ M →
      probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY) = 0 ∧
        ∀ ξ : ℝ,
          (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ = 0 := by
  let d : G := (t : G) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩
  have hfin := finite_nonzeroSIntegerDiagonal_preimage_compact K S
    ((fun x : G => x * d) '' probeLogSpatialSupport K S P)
    ((isCompact_probeLogSpatialSupport K S P).image
      (continuous_id.mul continuous_const))
  refine ⟨hfin.toFinset, ?_⟩
  intro m hm
  have hx : probeColumnBasePoint K S m t X Y hX hY ∉ probeLogSpatialSupport K S P := by
    intro hx
    apply hm
    apply hfin.mem_toFinset.mpr
    refine ⟨probeColumnBasePoint K S m t X Y hX hY, hx, ?_⟩
    exact div_mul_cancel _ _
  have hz := probeLogSchwartz_eq_zero_of_not_mem K S P _ hx
  refine ⟨hz, fun ξ => ?_⟩
  rw [hz]
  simp

/-- Literal separated row with the original theta coefficient. -/
def probeAmplitudeSpectralRow (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (t : sLocalNormOneGroup K S)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (m : NZ) (ξ : ℝ) : ℂ :=
  ((𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
    actualAdditiveGramAmplitude K S P (fun _ => 1)
      P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val) *
    completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
      (primeSetIdeal K S ∅) Q logGaussianProfile Z

theorem integrable_probeAmplitudeSpectralRow (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (t : sLocalNormOneGroup K S)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (m : NZ) :
    Integrable (probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m) :=
  (integrable_probeLogFourier_mul_amplitude K S P
    (probeColumnBasePoint K S m t X Y hX hY) Y hY m.val).mul_const _

theorem exists_probeAmplitudeSpectralRow_common_support
    (P : ProbeData K S) (t : sLocalNormOneGroup K S)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    ∃ M : Finset NZ, ∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
      (Z : ℝ) (m : NZ), m ∉ M → ∀ ξ : ℝ,
        probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ = 0 := by
  obtain ⟨M, hM⟩ := exists_probeLogFourier_common_frequency_support K S P t X Y hX hY
  refine ⟨M, fun ψ Q Z m hm ξ => ?_⟩
  simp only [probeAmplitudeSpectralRow, (hM m hm).2 ξ, zero_mul]

/-- A true integrable finite frequency sum at every fixed norm-one point. -/
theorem integrable_tsum_probeAmplitudeSpectralRow
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (t : sLocalNormOneGroup K S) (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    Integrable (fun ξ : ℝ =>
      ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ) := by
  obtain ⟨M, hM⟩ := exists_probeAmplitudeSpectralRow_common_support K S P t X Y hX hY
  have he (ξ : ℝ) :
      (∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ) =
        ∑ m ∈ M, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ :=
    tsum_eq_sum (fun m hm => hM ψ Q Z m hm ξ)
  simp_rw [he]
  exact integrable_finsetSum M (fun m _ =>
    integrable_probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m)

/-- The frequency/Fourier interchange follows from one common finite support. -/
theorem tsum_integral_probeAmplitudeSpectralRow
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (t : sLocalNormOneGroup K S) (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (∑' m : NZ, ∫ ξ : ℝ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ) =
      ∫ ξ : ℝ, ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ := by
  obtain ⟨M, hM⟩ := exists_probeAmplitudeSpectralRow_common_support K S P t X Y hX hY
  have he (ξ : ℝ) :
      (∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ) =
        ∑ m ∈ M, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ :=
    tsum_eq_sum (fun m hm => hM ψ Q Z m hm ξ)
  have hz (m : NZ) (hm : m ∉ M) :
      (∫ ξ : ℝ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ) = 0 := by
    simp_rw [hM ψ Q Z m hm]
    exact integral_zero _ _
  rw [tsum_eq_sum hz]
  simp_rw [he]
  exact (integral_finsetSum M (fun m _ =>
    integrable_probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m)).symm

/-- Exact separated formula for the original probe integrand. Its spectral
sum is finite and integrable by the preceding actual-support theorems. -/
theorem probeIntegrand_eq_integral_tsum_amplitude
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (t : sLocalNormOneGroup K S) (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    probeIntegrand K S P ψ Q X Y Z t =
      (((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ ξ : ℝ, ∑' m : NZ, probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ := by
  rw [probeIntegrand_eq_tsum_amplitude_integrals K S P ψ Q X Y Z hX hY t,
    ← tsum_integral_probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  unfold probeAmplitudeSpectralRow
  rw [integral_mul_const]
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
