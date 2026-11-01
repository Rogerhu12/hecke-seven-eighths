import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProvider
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderExponent
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderTerminalConductor

/-!
# Exact logarithmic conductor geometry of the original frozen row

The lower endpoint of a powerful-part annulus is charged once. The
supported factor is eliminated using the actual product decomposition
of the row. Consequently the row and dual conductor inequalities are
proved from ideal norms, with no assumed conductor cost and no rounding
loss in either inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalGeometry

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualFrozenCube (exteriorPower)
open GeneralReflectedEnergy ProviderTerminalConductor
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

theorem logNorm_eq_logb (Z : ℝ) (I : Ext) :
    logNorm K S Z I = Real.logb Z (exteriorNorm K S I) := rfl

theorem logNorm_mul (Z : ℝ) (I J : Ext) :
    logNorm K S Z (exteriorMul K S I J) = logNorm K S Z I + logNorm K S Z J := by
  simp only [logNorm_eq_logb, exteriorNorm, exteriorMul, Submonoid.coe_mul,
    map_mul, Nat.cast_mul]
  exact Real.logb_mul (idealNorm_pos K I.val).ne' (idealNorm_pos K J.val).ne'

theorem logNorm_pow (Z : ℝ) (I : Ext) (n : ℕ) :
    logNorm K S Z (exteriorPower K S I n) = n * logNorm K S Z I := by
  simp only [logNorm_eq_logb, exteriorNorm, exteriorPower,
    SubmonoidClass.coe_pow, map_pow, Nat.cast_pow, Real.logb_pow]

theorem logNorm_le_iff {Z a : ℝ} (hZ : 1 < Z) (I : Ext) :
    logNorm K S Z I ≤ a ↔ exteriorNorm K S I ≤ Z ^ a :=
  Real.logb_le_iff_le_rpow hZ (exteriorNorm_pos K S I)

theorem le_logNorm_iff {Z a : ℝ} (hZ : 1 < Z) (I : Ext) :
    a ≤ logNorm K S Z I ↔ Z ^ a ≤ exteriorNorm K S I :=
  Real.le_logb_iff_rpow_le hZ (exteriorNorm_pos K S I)

theorem row_log_budget {Z M : ℝ} (hZ : 1 < Z) (P J k : Ext)
    (hrow : exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M) :
    logNorm K S Z P + logNorm K S Z J + logNorm K S Z k ≤ M := by
  have h := (logNorm_le_iff K S hZ _).mpr hrow
  simpa only [logNorm_mul] using h

/-- The true powerful and residual lower endpoints cost no dyadic width. -/
theorem row_conductor {Z O H M : ℝ} (hZ : 1 < Z) (P J k : Ext)
    (hrow : exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M)
    (hP : Z ^ O ≤ exteriorNorm K S P) (hk : Z ^ H ≤ exteriorNorm K S k) :
    H ≤ M - O := by
  have hbudget := row_log_budget K S hZ P J k hrow
  have hp := (le_logNorm_iff K S hZ P).mpr hP
  have hr := (le_logNorm_iff K S hZ k).mpr hk
  have hj := TerminalExponent.logNorm_nonneg K S hZ J
  linarith

theorem frozen_conductor_log (Z : ℝ) (hZ : 1 < Z) (P J f r : Ext)
    (hP : Powerful P.val) (s : FrozenState K S (frozenIdeal K S P J f) r) :
    2 * logNorm K S Z (primeSetIdeal K S s.active) -
      logNorm K S Z (minimumLinearIdeal K S s) -
      logNorm K S Z (minimumSmallIdeal K S s) -
      4 * logNorm K S Z (minimumCubeIdeal K S s) ≤
      logNorm K S Z P + 2 * logNorm K S Z J +
        logNorm K S Z f + logNorm K S Z r := by
  have ha := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hl := exteriorNorm_pos K S (minimumLinearIdeal K S s)
  have hs := exteriorNorm_pos K S (minimumSmallIdeal K S s)
  have hb := exteriorNorm_pos K S (minimumCubeIdeal K S s)
  have hp := exteriorNorm_pos K S P
  have hj := exteriorNorm_pos K S J
  have hf := exteriorNorm_pos K S f
  have hr := exteriorNorm_pos K S r
  have h := Real.logb_le_logb_of_le hZ
    (show 0 < exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 /
      (exteriorNorm K S (minimumLinearIdeal K S s) *
        exteriorNorm K S (minimumSmallIdeal K S s) *
          exteriorNorm K S (minimumCubeIdeal K S s) ^ 4) by positivity)
    (conductor_ratio_bound K S P J f r hP s)
  rw [Real.logb_div (pow_ne_zero 2 ha.ne')
      (mul_ne_zero (mul_ne_zero hl.ne' hs.ne') (pow_ne_zero 4 hb.ne')),
    Real.logb_mul (mul_ne_zero hl.ne' hs.ne') (pow_ne_zero 4 hb.ne'),
    Real.logb_mul hl.ne' hs.ne',
    Real.logb_mul (mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero 2 hj.ne')) hf.ne') hr.ne',
    Real.logb_mul (mul_ne_zero hp.ne' (pow_ne_zero 2 hj.ne')) hf.ne',
    Real.logb_mul hp.ne' (pow_ne_zero 2 hj.ne')] at h
  simp only [Real.logb_pow] at h
  simp only [logNorm_eq_logb]
  linarith

/-- The supported part cancels against two copies of the original row
budget; the remaining powerful norm is a genuine saving. -/
theorem dual_conductor {Z O H M V Q Nstar za : ℝ} (hZ : 1 < Z)
    (P J f r k : Ext) (hP : Powerful P.val)
    (s : FrozenState K S (frozenIdeal K S P J f) r)
    (hrow : exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M)
    (hpower : Z ^ O ≤ exteriorNorm K S P)
    (hres : Z ^ H ≤ exteriorNorm K S k)
    (hf : exteriorNorm K S f ≤ Z ^ V) (hr : exteriorNorm K S r ≤ Z ^ Q) :
    (2 * H + 2 * logNorm K S Z (primeSetIdeal K S s.active) + 2 * za - Nstar -
      logNorm K S Z (minimumLinearIdeal K S s) -
        3 * logNorm K S Z (minimumCubeIdeal K S s)) -
      logNorm K S Z (minimumSmallIdeal K S s) -
        logNorm K S Z (minimumCubeIdeal K S s) ≤
      2 * M - O + Q + V - Nstar + 2 * za := by
  have hcost := frozen_conductor_log K S Z hZ P J f r hP s
  have hbudget := row_log_budget K S hZ P J k hrow
  have hp := (le_logNorm_iff K S hZ P).mpr hpower
  have hk := (le_logNorm_iff K S hZ k).mpr hres
  have hfl := (logNorm_le_iff K S hZ f).mpr hf
  have hrl := (logNorm_le_iff K S hZ r).mpr hr
  linarith

/-- Assemble the terminal ledger geometry using the actual frozen
conductor and every original norm bound. -/
def actualGeometry {Z N V M Q z d eta tau O H za v ell h : ℝ}
    (hZ : 1 < Z) (P J f r k : Ext) (hP : Powerful P.val)
    (s : FrozenState K S (frozenIdeal K S P J f) r)
    (hrow : exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M)
    (hpower : Z ^ O ≤ exteriorNorm K S P)
    (hres : Z ^ H ≤ exteriorNorm K S k)
    (hf : exteriorNorm K S f ≤ Z ^ V) (hr : exteriorNorm K S r ≤ Z ^ Q)
    (hO : 0 ≤ O) (hza : 0 ≤ za) (hz : za ≤ z) (hv : 0 ≤ v) (hell : 0 ≤ ell)
    (heta : 0 ≤ eta) (hh : 0 ≤ h) (hd : h ≤ d + eta)
    (hretained : v + 3 * ell ≤
      (2 * H + 2 * logNorm K S Z (primeSetIdeal K S s.active) + 2 * za - (N - 3 * h) -
        logNorm K S Z (minimumLinearIdeal K S s) -
          3 * logNorm K S Z (minimumCubeIdeal K S s)) + tau) :
    TerminalBlockGeometry N V M Q z d eta tau where
  powerful := O
  residual := H
  small := logNorm K S Z (minimumSmallIdeal K S s)
  cubeCharge := logNorm K S Z (minimumCubeIdeal K S s)
  active := za
  dual := v
  cube := ell
  ramified := 0
  threshold := 2 * H + 2 * logNorm K S Z (primeSetIdeal K S s.active) + 2 * za - (N - 3 * h) -
    logNorm K S Z (minimumLinearIdeal K S s) -
      3 * logNorm K S Z (minimumCubeIdeal K S s)
  completion := h
  powerful_nonneg := hO
  small_nonneg := TerminalExponent.logNorm_nonneg K S hZ _
  cubeCharge_nonneg := TerminalExponent.logNorm_nonneg K S hZ _
  active_nonneg := hza
  active_le := hz
  dual_nonneg := hv
  cube_nonneg := hell
  ramified_lower := by linarith
  completion_nonneg := hh
  completion_le := hd
  retained := by simpa only [add_zero] using hretained
  row_conductor := (row_conductor K S hZ P J k hrow hpower hres).trans (by linarith)
  dual_conductor := (dual_conductor K S hZ P J f r k hP s hrow hpower hres hf hr).trans
    (by linarith)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalGeometry

end
