/-
Copyright (c) 2026. Released under the Apache 2.0 license.

The local logarithm and translated Borel--Carathéodory proofs are adapted
from the public OpenAI mathematical-research repository, revision fd4aeeb2,
lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean (Apache 2.0).
Their underlying logarithm, inverse-function, Borel--Carathéodory, and
Cauchy-estimate APIs are supplied by mathlib (Apache 2.0).

This file imports only mathlib and has no dependency on the OAI namespace.
It proves a zero-free-disk logarithmic-derivative estimate. It does not
assert that a Hecke L-function satisfies the analytic hypotheses.
-/

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open scoped Classical Topology
open Set Filter Metric Complex

namespace PrimeCancellationLogDerivative

/-- A continuous lift through `exp` of a holomorphic map is holomorphic.
The inverse function theorem is applied locally, so no chosen principal
branch of the logarithm is involved. -/
theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {F g : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) F U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hFc : DifferentiableAt ℂ F z := (hF z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (F z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (F w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hFc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- Nonvanishing on a disk produces a holomorphic logarithm. -/
theorem exists_holomorphic_log {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (ball c R))
    (h0 : ∀ z ∈ ball c R, F z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) F (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hF.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hF hg he, he⟩

/-- The logarithm can be normalized to any prescribed logarithm of the
value at the center. This will use an Euler-product logarithm in the
Hecke application. -/
theorem exists_holomorphic_log_normalized {F : ℂ → ℂ} {c m : ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F (ball c R))
    (h0 : ∀ z ∈ ball c R, F z ≠ 0) (hm : Complex.exp m = F c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) F (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hF h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = F z
  have hez : Complex.exp (g z) = F z := he hz
  have hec : Complex.exp (g c) = F c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

/-- Differentiating a holomorphic exponential representation gives the
logarithmic derivative without assuming that identity in advance. -/
theorem logarithmic_derivative_eq {F g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) F U)
    {z : ℂ} (hz : z ∈ U) : deriv F z / F z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : F =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdf := hd.congr_of_eventuallyEq heq
  rw [hdf.deriv]
  have hez : Complex.exp (g z) = F z := he hz
  rw [← hez]
  field_simp

/-- Translate mathlib's Borel--Carathéodory theorem from a disk centered
at zero to an arbitrary center, and replace the point radius by a fixed
closed-ball radius. -/
theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

/-- Borel--Carathéodory on radius `(R+r)/2`, followed by the Cauchy
estimate on radius `(R-r)/2`, bounds the derivative on the inner disk. -/
theorem norm_deriv_le_of_re_le {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv g z‖ ≤ 8 * R * (M + A) / (R - r) ^ 2 := by
  let ρ : ℝ := (R + r) / 2
  let q : ℝ := (R - r) / 2
  have hρ : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hgap : R - ρ = q := by dsimp [ρ, q]; ring
  have hsum : q + r = ρ := by dsimp [ρ, q]; ring
  have hzn : dist z c ≤ r := hz
  have hsub : closedBall z q ⊆ ball c R := by
    intro w hw
    have hw' : dist w z ≤ q := hw
    have hdist := dist_triangle w z c
    change dist w c < R
    linarith
  have hnum : 2 * M * ρ + A * (R + ρ) ≤ 2 * R * (M + A) := by
    calc
      2 * M * ρ + A * (R + ρ) ≤ 2 * M * R + A * (R + R) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hρR.le (by positivity)
        · exact mul_le_mul_of_nonneg_left (add_le_add (le_refl R) hρR.le) hA
      _ = 2 * R * (M + A) := by ring
  have hb : ∀ w ∈ closedBall c ρ, ‖g w‖ ≤ 2 * R * (M + A) / q := by
    intro w hw
    calc
      ‖g w‖ ≤ 2 * M * ρ / (R - ρ) + A * (R + ρ) / (R - ρ) :=
        borel_caratheodory_closedBall hρ hρR hM hA hg hRe hc hw
      _ = (2 * M * ρ + A * (R + ρ)) / q := by rw [hgap, ← add_div]
      _ ≤ 2 * R * (M + A) / q := (div_le_div_iff_of_pos_right hq).mpr hnum
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq
    (hg.diffContOnCl_ball hsub) (C := 2 * R * (M + A) / q) (by
      intro w hw
      apply hb
      have hw' : dist w z = q := hw
      have hdist := dist_triangle w z c
      change dist w c ≤ ρ
      linarith)
  refine hd.trans_eq ?_
  have hne : R - r ≠ 0 := ne_of_gt (sub_pos.mpr hrR)
  dsimp [q]
  field_simp [hne]
  ring

/-- A holomorphic nonvanishing function of exponential size has a
logarithmic derivative controlled by the logarithm of that size.

The logarithm is constructed from nonvanishing; it is not an assumption.
The center input is a single bounded logarithm, supplied by the Euler
product in the intended Hecke application. -/
theorem norm_logDeriv_le_of_exp_bound {F : ℂ → ℂ} {c m : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M)
    (hF : DifferentiableOn ℂ F (ball c R))
    (h0 : ∀ z ∈ ball c R, F z ≠ 0)
    (hm : Complex.exp m = F c) (hmA : ‖m‖ ≤ A)
    (hbound : ∀ z ∈ ball c R, ‖F z‖ ≤ Real.exp M)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv F z / F z‖ ≤ 8 * R * (M + A) / (R - r) ^ 2 := by
  have hA : 0 ≤ A := (norm_nonneg m).trans hmA
  obtain ⟨g, hg, he, hgc⟩ :=
    exists_holomorphic_log_normalized (hr.trans_lt hrR) hF h0 hm
  have hRe : ∀ w ∈ ball c R, (g w).re ≤ M := by
    intro w hw
    have hew : Complex.exp (g w) = F w := he hw
    have hb := hbound w hw
    rw [← hew, Complex.norm_exp] at hb
    exact Real.exp_le_exp.mp hb
  have hc : ‖g c‖ ≤ A := by simpa [hgc] using hmA
  rw [logarithmic_derivative_eq isOpen_ball hg he (closedBall_subset_ball hrR hz)]
  exact norm_deriv_le_of_re_le hr hrR hM hA hg hRe hc hz

/-- A polynomial upper bound in an arbitrary parameter Q gives only
logarithmic dependence on Q in the logarithmic derivative. -/
theorem norm_logDeriv_le_of_rpow_bound {F : ℂ → ℂ} {c m : ℂ}
    {r R Q p A : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hF : DifferentiableOn ℂ F (ball c R))
    (h0 : ∀ z ∈ ball c R, F z ≠ 0)
    (hm : Complex.exp m = F c) (hmA : ‖m‖ ≤ A)
    (hbound : ∀ z ∈ ball c R, ‖F z‖ ≤ Q ^ p)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv F z / F z‖ ≤ 8 * R * (1 + p * Real.log Q + A) / (R - r) ^ 2 := by
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hM : 0 < 1 + p * Real.log Q := by positivity
  apply norm_logDeriv_le_of_exp_bound hr hrR hM hF h0 hm hmA ?_ hz
  intro w hw
  refine (hbound w hw).trans ?_
  rw [Real.rpow_def_of_pos hQp]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- With the disks used for prime cancellation, the universal constant
is at most `48 / δ^2`, uniformly for `1/2 ≤ β ≤ 1`. -/
theorem norm_logDeriv_le_on_bufferedDisk {F : ℂ → ℂ} {c m : ℂ}
    {β δ M A : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hM : 0 < M)
    (hF : DifferentiableOn ℂ F (ball c (2 - β - δ / 2)))
    (h0 : ∀ z ∈ ball c (2 - β - δ / 2), F z ≠ 0)
    (hm : Complex.exp m = F c) (hmA : ‖m‖ ≤ A)
    (hbound : ∀ z ∈ ball c (2 - β - δ / 2), ‖F z‖ ≤ Real.exp M)
    {z : ℂ} (hz : z ∈ closedBall c (2 - β - δ)) :
    ‖deriv F z / F z‖ ≤ 48 * (M + A) / δ ^ 2 := by
  have hr : 0 ≤ 2 - β - δ := by linarith
  have hrR : 2 - β - δ < 2 - β - δ / 2 := by linarith
  have hA : 0 ≤ A := (norm_nonneg m).trans hmA
  have hMA : 0 ≤ M + A := by positivity
  have hb := norm_logDeriv_le_of_exp_bound hr hrR hM hF h0 hm hmA hbound hz
  calc
    ‖deriv F z / F z‖ ≤
        8 * (2 - β - δ / 2) * (M + A) /
          ((2 - β - δ / 2) - (2 - β - δ)) ^ 2 := hb
    _ = 32 * (2 - β - δ / 2) * (M + A) / δ ^ 2 := by
      have hgap : (2 - β - δ / 2) - (2 - β - δ) = δ / 2 := by ring
      rw [hgap]
      field_simp [ne_of_gt hδ]
      ring
    _ ≤ 48 * (M + A) / δ ^ 2 := by
      apply (div_le_div_iff_of_pos_right (show 0 < δ ^ 2 by positivity)).mpr
      exact mul_le_mul_of_nonneg_right (by linarith :
        32 * (2 - β - δ / 2) ≤ 48) hMA

#print axioms differentiableOn_of_exp_eq
#print axioms exists_holomorphic_log
#print axioms exists_holomorphic_log_normalized
#print axioms logarithmic_derivative_eq
#print axioms borel_caratheodory_closedBall
#print axioms norm_deriv_le_of_re_le
#print axioms norm_logDeriv_le_of_exp_bound
#print axioms norm_logDeriv_le_of_rpow_bound
#print axioms norm_logDeriv_le_on_bufferedDisk

end PrimeCancellationLogDerivative
