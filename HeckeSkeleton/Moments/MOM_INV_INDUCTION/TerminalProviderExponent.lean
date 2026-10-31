import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderSlices
import HeckeSkeleton.LowFrozenCube.Scale

/-!
# The canonical block's exact reflected exponent

The actual minimum-ideal charges, common Mellin scale, and two sieve
factors give `E_ref` before any canonical conductor inequality is used.
Dyadic upper endpoints cost a fixed factor, and their sieve small power
is displayed explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalExponent

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy
open TerminalMellin
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "Ext" => ExteriorIdeal K S

theorem rpow_logNorm {Z : ℝ} (hZ : 1 < Z) (I : Ext) :
    Z ^ GeneralReflectedEnergy.logNorm K S Z I = exteriorNorm K S I := by
  simpa only [GeneralReflectedEnergy.logNorm, Real.logb] using
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (exteriorNorm_pos K S I)

theorem logNorm_nonneg {Z : ℝ} (hZ : 1 < Z) (I : Ext) :
    0 ≤ GeneralReflectedEnergy.logNorm K S Z I := by
  have hn : 1 ≤ exteriorNorm K S I := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
  exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

/-- The completed scale has exactly the paper's minimum-linear and
minimum-cube charge. The active-mark norm occurs twice. -/
theorem canonicalScale_eq {Z : ℝ} (hZ : 1 < Z) (Nstar H za v ell : ℝ) :
    canonicalScale K S f s (Z ^ Nstar) (Z ^ H) (Z ^ za) (Z ^ v) (Z ^ ell) =
      Z ^ (v + 3 * ell - GeneralReflectedEnergy.threshold K S f s Z Nstar H za) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  conv_lhs =>
    rw [canonicalScale, canonicalBase, minimum_norm_decomposition,
      ← rpow_logNorm K S hZ (minimumLinearIdeal K S s),
      ← rpow_logNorm K S hZ (minimumCubeIdeal K S s),
      ← rpow_logNorm K S hZ (primeSetIdeal K S s.active)]
  simp only [← Real.rpow_mul_natCast hz.le, ← Real.rpow_add hz, ← Real.rpow_sub hz]
  congr 1
  unfold GeneralReflectedEnergy.threshold
  push_cast
  ring

theorem state_charge_le {Z : ℝ} (hZ : 1 < Z) :
    stateMajorant K S s ^ 2 ≤
      Z ^ (-GeneralReflectedEnergy.logNorm K S Z (minimumSmallIdeal K S s) -
        GeneralReflectedEnergy.logNorm K S Z (minimumCubeIdeal K S s)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := stateMajorant_sq_le_inverse_charge K S s
  rw [← rpow_logNorm K S hZ (minimumSmallIdeal K S s),
    ← rpow_logNorm K S hZ (minimumCubeIdeal K S s), ← Real.rpow_add hz,
    ← Real.rpow_neg hz.le] at hc
  convert hc using 1
  congr 1
  ring

/-- Including the actual squarefree/cube normalizations gives the
coefficient exponent without any conductor input. -/
theorem normalized_state_charge_le {Z : ℝ} (hZ : 1 < Z) (v ell : ℝ) :
    stateMajorant K S s ^ 2 / (Z ^ v * (Z ^ ell) ^ 2) ≤
      Z ^ (LowFrozenCube.squaredCoefficientExponent v ell
        (GeneralReflectedEnergy.logNorm K S Z (minimumSmallIdeal K S s))
        (GeneralReflectedEnergy.logNorm K S Z (minimumCubeIdeal K S s))) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  apply (div_le_div_of_nonneg_right (state_charge_le K S f s hZ) (by positivity)).trans_eq
  simp only [← Real.rpow_mul_natCast hz.le, ← Real.rpow_add hz, ← Real.rpow_sub hz]
  congr 1
  unfold LowFrozenCube.squaredCoefficientExponent
  push_cast
  ring

/-- The positive-line part only strengthens the block bound. Its
arbitrary-saving use is handled separately for the actual tail. -/
theorem scalar_sq_le (Z T v ell : ℝ) (hZ : 1 ≤ Z) :
    CommonMellinTail.scalar (Z ^ (v + 3 * ell - T)) ^ 2 ≤
      Z ^ LowFrozenCube.squaredKernelExponent T v ell := by
  rw [CommonMellinTail.scalar_sq_exponent Z T v ell hZ]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  unfold LowFrozenCube.squaredKernelExponent
  linarith [le_max_right (v + 3 * ell - T) 0]

/-- Replacing each dyadic upper endpoint by twice its lower endpoint
has a fixed factor. In particular there is no additional scale power. -/
theorem doubled_hybrid_le (Z H v ell za : ℝ) (hZ : 1 ≤ Z) :
    (2 * Z ^ H + (2 * Z ^ v) * (2 * Z ^ ell)) * (2 * Z ^ ell) *
      (2 * Z ^ v + 2 * Z ^ za + ((2 * Z ^ v) * (2 * Z ^ za)) ^ (2 / 3 : ℝ)) ≤
      192 * Z ^ LowFrozenCube.hybridGrowthExponent H v ell za := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpow : ((2 * Z ^ v) * (2 * Z ^ za)) ^ (2 / 3 : ℝ) ≤
      4 * (Z ^ v * Z ^ za) ^ (2 / 3 : ℝ) := by
    rw [show (2 * Z ^ v) * (2 * Z ^ za) = 4 * (Z ^ v * Z ^ za) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (2 / 3 : ℝ) ≤ 1)
    simpa using h
  have hq : 2 * Z ^ H + (2 * Z ^ v) * (2 * Z ^ ell) ≤
      4 * LowFrozenCube.quadraticScale Z H v ell := by
    unfold LowFrozenCube.quadraticScale
    nlinarith [Real.rpow_nonneg hz.le H]
  have hc : 2 * Z ^ v + 2 * Z ^ za + ((2 * Z ^ v) * (2 * Z ^ za)) ^ (2 / 3 : ℝ) ≤
      4 * LowFrozenCube.cubicScale Z v za := by
    unfold LowFrozenCube.cubicScale
    nlinarith [Real.rpow_nonneg hz.le v, Real.rpow_nonneg hz.le za]
  calc
    _ ≤ (4 * LowFrozenCube.quadraticScale Z H v ell) * (2 * Z ^ ell) *
        (4 * LowFrozenCube.cubicScale Z v za) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hq (by positivity)) hc
      · positivity
      · unfold LowFrozenCube.quadraticScale
        positivity
    _ = 32 * LowFrozenCube.hybridScale Z H v ell za := by
      unfold LowFrozenCube.hybridScale
      ring
    _ ≤ 32 * (6 * Z ^ LowFrozenCube.hybridGrowthExponent H v ell za) :=
      mul_le_mul_of_nonneg_left (LowFrozenCube.hybridScale_le Z H v ell za hZ) (by norm_num)
    _ = _ := by ring

theorem doubled_small_power (Z H v ell za eps : ℝ) (hZ : 0 < Z) :
    ((2 * Z ^ H) * (2 * Z ^ v) * (2 * Z ^ ell) * (2 * Z ^ za)) ^ eps =
      16 ^ eps * Z ^ (eps * (H + v + ell + za)) := by
  rw [show (2 * Z ^ H) * (2 * Z ^ v) * (2 * Z ^ ell) * (2 * Z ^ za) =
      16 * (Z ^ H * Z ^ v * Z ^ ell * Z ^ za) by ring,
    Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_mul hZ.le]
  congr 1
  ring

/-- The complete numerical factor of the actual block gives precisely
`E_ref`; the sieve small power is still explicit. -/
theorem actual_factor_le {Z : ℝ} (hZ : 1 < Z)
    (Nstar H za v ell eps : ℝ) :
    CommonMellinTail.scalar
        (canonicalScale K S f s (Z ^ Nstar) (Z ^ H) (Z ^ za) (Z ^ v) (Z ^ ell)) ^ 2 *
      (stateMajorant K S s ^ 2 / (Z ^ v * (Z ^ ell) ^ 2)) *
      ((2 * Z ^ H) * (2 * Z ^ v) * (2 * Z ^ ell) * (2 * Z ^ za)) ^ eps *
      (2 * Z ^ H + (2 * Z ^ v) * (2 * Z ^ ell)) * (2 * Z ^ ell) *
      (2 * Z ^ v + 2 * Z ^ za + ((2 * Z ^ v) * (2 * Z ^ za)) ^ (2 / 3 : ℝ)) ≤
      (192 * 16 ^ eps) *
        Z ^ (GeneralReflectedEnergy.exponent K S f s Z Nstar H za v ell +
          eps * (H + v + ell + za)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hk := scalar_sq_le Z (GeneralReflectedEnergy.threshold K S f s Z Nstar H za) v ell hZ.le
  rw [← canonicalScale_eq K S f s hZ Nstar H za v ell] at hk
  have hc := normalized_state_charge_le K S f s hZ v ell
  have hh := doubled_hybrid_le Z H v ell za hZ.le
  have hp := doubled_small_power Z H v ell za eps hz
  have hleft := mul_le_mul_of_nonneg_right (mul_le_mul hk hc (by positivity) (by positivity))
    (show 0 ≤ ((2 * Z ^ H) * (2 * Z ^ v) * (2 * Z ^ ell) * (2 * Z ^ za)) ^ eps by positivity)
  have h := mul_le_mul hleft hh (by positivity) (by positivity)
  apply (by simpa only [mul_assoc] using h : _ ≤ _).trans_eq
  rw [hp]
  unfold GeneralReflectedEnergy.exponent HeckePort.Moments.reflectedExponent
    HeckePort.Moments.hybridSaving LowFrozenCube.squaredCoefficientExponent
    LowFrozenCube.hybridGrowthExponent LowFrozenCube.squaredKernelExponent
  rw [LowFrozenCube.cubic_growth_identity]
  unfold LowFrozenCube.cubicSaving
  rw [max_comm 0]
  simp only [Real.rpow_add hz, Real.rpow_sub hz, Real.rpow_neg hz.le]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalExponent

end
