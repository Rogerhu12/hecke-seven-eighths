import ActualProbeAmplitudeMellin
import HeckeGeneral.Arithmetic.SIntegerBalancedRepresentatives
import Mathlib.Topology.Order.Compact

/-!
UNCOMPILED / native 0. The actual tensor compact support and the fixed
logarithmic denominator cutoff bound the row norm before t, X, Y, m or xi
is chosen. The product norm includes every finite coordinate. Norm-one t
disappears from the exact base-point norm, rather than from a bound on a
chosen fundamental domain. No Fourier/infinite-sum interchange is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- A genuine upper norm bound derived from the original tensor's compact
support, without replacing the tensor by its archimedean factor. -/
theorem exists_additiveTest_productNorm_upper (P : ProbeData K S) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : G,
      additiveTest K S P.additive x ≠ 0 → sLocalProductNorm K S x ≤ B := by
  have hcs : HasCompactSupport (additiveTest K S P.additive) :=
    P.additive.tensor_compactSupport
  obtain ⟨b, hb⟩ := hcs.isCompact.bddAbove_image
    (continuous_sLocalProductNorm K S).continuousOn
  refine ⟨|b| + 1, by positivity, ?_⟩
  intro x hx
  have hxb : sLocalProductNorm K S x ≤ b :=
    hb ⟨x, subset_closure hx, rfl⟩
  exact hxb.trans (by linarith [le_abs_self b])

/-- The original compact logarithmic cutoff yields one product-norm envelope
for the whole family of Schwartz profiles. -/
theorem exists_probeLogSchwartz_productNorm_envelope (P : ProbeData K S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : G) (v : ℝ),
      probeLogSchwartz K S P x v ≠ 0 → sLocalProductNorm K S x ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_additiveTest_productNorm_upper K S P
  let b := denominatorLogCutoff P.denominator.toSmoothAnnularTest
  refine ⟨B * Real.exp b.rOut, mul_pos hB (Real.exp_pos _), ?_⟩
  intro x v hne
  have hcut : b v ≠ 0 := by
    intro hz
    apply hne
    simp only [probeLogSchwartz_apply, probeCutLogProfile, show
      denominatorLogCutoff P.denominator.toSmoothAnnularTest v = 0 from hz,
      zero_smul]
  have htest : additiveTest K S P.additive
      (sLocalNormSection K S ⟨Real.exp (-v), Real.exp_pos _⟩ * x) ≠ 0 := by
    intro hz
    apply hne
    simp only [probeLogSchwartz_apply, probeCutLogProfile, probeRawLogProfile,
      hz, smul_zero]
  have hvball : v ∈ Metric.ball (0 : ℝ) b.rOut := by
    rw [← b.support_eq]
    exact hcut
  have hvabs : |v| < b.rOut := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hvball
  have hvle : v ≤ b.rOut := (le_abs_self v).trans hvabs.le
  have hscaled : Real.exp (-v) * sLocalProductNorm K S x ≤ B := by
    simpa only [sLocalProductNorm_mul, sLocalProductNorm_section] using hbound _ htest
  have hcancel : Real.exp v * Real.exp (-v) = 1 := by
    rw [← Real.exp_add]
    simp
  have hnorm : sLocalProductNorm K S x ≤ Real.exp v * B := by
    have h := mul_le_mul_of_nonneg_left hscaled (Real.exp_pos v).le
    simpa only [← mul_assoc, hcancel, one_mul] using h
  calc
    sLocalProductNorm K S x ≤ Real.exp v * B := hnorm
    _ ≤ Real.exp b.rOut * B :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hvle) hB.le
    _ = B * Real.exp b.rOut := mul_comm _ _

/-- Exact norm of the actual row base point: all finite factors are retained,
and t has norm one by membership in the actual norm-one subgroup. -/
theorem sLocalProductNorm_probeColumnBasePoint (m : NZ)
    (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    sLocalProductNorm K S (probeColumnBasePoint K S m t X Y hX hY) =
      (sIntegerElementNorm K S m).val / (X * Y) := by
  have ht : sLocalProductNorm K S (t : G) = 1 :=
    (mem_sLocalNormOneGroup K S t.val).mp t.property
  simp only [probeColumnBasePoint, div_eq_mul_inv, sLocalProductNorm_mul,
    sLocalProductNorm_inv, sLocalProductNorm_section, sIntegerElementNorm, ht, one_mul]

/-- One constant precedes every moving variable. Beyond C*X*Y the original
Schwartz profile and its actual standard Fourier transform both vanish. -/
theorem exists_probeLogSchwartz_row_norm_envelope (P : ProbeData K S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ)
      (hX : 0 < X) (hY : 0 < Y) (m : NZ),
      C * (X * Y) < (sIntegerElementNorm K S m).val →
        probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY) = 0 ∧
        𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY)) = 0 := by
  obtain ⟨C, hC, hbound⟩ := exists_probeLogSchwartz_productNorm_envelope K S P
  refine ⟨C, hC, ?_⟩
  intro t X Y hX hY m hm
  have hlarge : C < sLocalProductNorm K S
      (probeColumnBasePoint K S m t X Y hX hY) := by
    rw [sLocalProductNorm_probeColumnBasePoint K S m t X Y hX hY]
    exact (lt_div_iff₀ (mul_pos hX hY)).mpr hm
  have hzero : probeLogSchwartz K S P
      (probeColumnBasePoint K S m t X Y hX hY) = 0 := by
    ext v
    change probeLogSchwartz K S P
      (probeColumnBasePoint K S m t X Y hX hY) v = 0
    by_contra hne
    exact (not_le_of_gt hlarge) (hbound _ v hne)
  refine ⟨hzero, ?_⟩
  simpa only [hzero] using
    (FourierTransform.fourier_zero : 𝓕 (0 : SchwartzMap ℝ ℂ) = 0)

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
