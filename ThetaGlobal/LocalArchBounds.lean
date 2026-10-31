import HeckeSkeleton.ThetaLocal.ArchimedeanMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Power bounds for the actual high K-type Bessel profiles

The proof uses the already proved Mellin convergence and the actual
Schlafli integral defining `KThird`.  For `a = archWeight m + σ > 0`,
monotonicity gives

`KThird (c * sqrt t) * integral (u^(a-1), 0 < u ≤ t)`
`  ≤ integral (u^(a-1) * KThird (c * sqrt u), 0 < u)`.

The elementary power integral on the left is `t^a / a`.  The resulting
constant therefore controls the whole positive axis without an additional
asymptotic assumption.  The radial twist disappears on taking the norm.

-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace ThetaGlobal.LocalArchBounds

open MeasureTheory Set
open HeckeSkeleton.ThetaLocal DedekindZetaZeroFree

/-- The radial twist has absolute value one on the positive axis. -/
theorem norm_archDirectProfile (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ t : ℝ) (ht : 0 < t) :
    ‖archDirectProfile c m τ t‖ =
      t ^ archWeight m * KThird (c * Real.sqrt t) := by
  rw [archDirectProfile_eq c m τ t ht, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, archExponent_re,
    Complex.norm_of_nonneg
      (KThird_pos _ (mul_pos hc (Real.sqrt_pos.mpr ht))).le]

/-- The local Schlafli proof of the monotonicity also used in `BesselSheets`.
Keeping this elementary proof here avoids importing the global sheet source
bundles into a local analytic estimate. -/
private theorem bessel_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    KThird b ≤ KThird a := by
  rw [KThird_eq_integral _ (ha.trans_le hab), KThird_eq_integral _ ha]
  apply integral_mono
    (thirdBesselSchlafliIntegrand_integrable b (ha.trans_le hab))
    (thirdBesselSchlafliIntegrand_integrable a ha)
  intro u
  unfold thirdBesselSchlafliIntegrand
  apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
  apply Real.exp_le_exp.mpr
  nlinarith [Real.cosh_pos u]

private theorem weighted_bessel_integrable (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    IntegrableOn (fun t : ℝ =>
      t ^ (archWeight m + σ - 1) * KThird (c * Real.sqrt t)) (Ioi 0) := by
  have hs : (1 / 6 : ℝ) - archWeight m < (σ : ℂ).re := by
    change (1 / 6 : ℝ) - archWeight m < σ
    linarith [archWeight_ge_half m]
  have hm : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((σ : ℂ) - 1) * archDirectProfile c m τ t) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      (arch_direct_hasMellin c hc m τ (σ : ℂ) hs).1
  refine hm.norm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    norm_archDirectProfile c hc m τ t ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [← mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

private theorem weighted_bessel_bound (c : ℝ) (hc : 0 < c)
    (a : ℝ) (ha : 0 < a)
    (hi : IntegrableOn (fun u : ℝ =>
      u ^ (a - 1) * KThird (c * Real.sqrt u)) (Ioi 0))
    (t : ℝ) (ht : 0 < t) :
    t ^ a * KThird (c * Real.sqrt t) ≤
      a * ∫ u : ℝ in Ioi 0, u ^ (a - 1) * KThird (c * Real.sqrt u) := by
  have hp : IntervalIntegrable (fun u : ℝ => u ^ (a - 1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hsub : IntegrableOn (fun u : ℝ =>
      u ^ (a - 1) * KThird (c * Real.sqrt u)) (Ioc 0 t) :=
    hi.mono_set (fun _ hu => hu.1)
  have hmono :
      (∫ u : ℝ in Ioc 0 t, u ^ (a - 1) * KThird (c * Real.sqrt t)) ≤
        ∫ u : ℝ in Ioc 0 t, u ^ (a - 1) * KThird (c * Real.sqrt u) := by
    apply setIntegral_mono_on (hp.1.mul_const _) hsub measurableSet_Ioc
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.1.le _)
    exact bessel_antitone (mul_pos hc (Real.sqrt_pos.mpr hu.1))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu.2) hc.le)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun u : ℝ => u ^ (a - 1) * KThird (c * Real.sqrt u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _)
      (KThird_pos _ (mul_pos hc (Real.sqrt_pos.mpr hu))).le
  have hfull :
      (∫ u : ℝ in Ioc 0 t, u ^ (a - 1) * KThird (c * Real.sqrt u)) ≤
        ∫ u : ℝ in Ioi 0, u ^ (a - 1) * KThird (c * Real.sqrt u) :=
    setIntegral_mono_set hi hnonneg (Filter.Eventually.of_forall (fun _ hu => hu.1))
  have hpow : (∫ u : ℝ in Ioc 0 t, u ^ (a - 1)) = t ^ a / a := by
    rw [← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_rpow (Or.inl (by linarith : -1 < a - 1))]
    simp only [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]
  have hdiv : (t ^ a * KThird (c * Real.sqrt t)) / a ≤
      ∫ u : ℝ in Ioi 0, u ^ (a - 1) * KThird (c * Real.sqrt u) := by
    have h := hmono.trans hfull
    rw [integral_mul_const, hpow] at h
    simpa only [div_mul_eq_mul_div] using h
  exact ((div_le_iff₀ ha).mp hdiv).trans_eq (mul_comm _ _)

/-- A power bound valid for every positive argument of the genuine direct
profile and every exponent in the global convergence half-plane. -/
theorem archDirectProfile_bound (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      ‖archDirectProfile c m τ t‖ ≤ B * t ^ (-σ) := by
  let a : ℝ := archWeight m + σ
  let M : ℝ := ∫ u : ℝ in Ioi 0,
    u ^ (a - 1) * KThird (c * Real.sqrt u)
  have ha : 0 < a := by
    dsimp only [a]
    linarith [archWeight_ge_half m]
  have hi : IntegrableOn (fun u : ℝ =>
      u ^ (a - 1) * KThird (c * Real.sqrt u)) (Ioi 0) :=
    weighted_bessel_integrable c hc m τ σ hσ
  have hM : 0 ≤ M := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _)
      (KThird_pos _ (mul_pos hc (Real.sqrt_pos.mpr hu))).le
  refine ⟨a * M, mul_nonneg ha.le hM, ?_⟩
  intro t ht
  have hb : t ^ a * KThird (c * Real.sqrt t) ≤ a * M :=
    weighted_bessel_bound c hc a ha hi t ht
  have hexp : a + -σ = archWeight m := by
    dsimp only [a]
    ring
  rw [norm_archDirectProfile c hc m τ t ht]
  calc
    t ^ archWeight m * KThird (c * Real.sqrt t) =
        t ^ (a + -σ) * KThird (c * Real.sqrt t) := by rw [hexp]
    _ = (t ^ a * KThird (c * Real.sqrt t)) * t ^ (-σ) := by
      rw [Real.rpow_add ht]
      ring
    _ ≤ (a * M) * t ^ (-σ) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ht.le _)

/-- Reflection changes only the radial twist, so it satisfies the same
power-bound statement without any new local assumption. -/
theorem archReflectedProfile_bound (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t →
      ‖archReflectedProfile c m τ t‖ ≤ B * t ^ (-σ) :=
  archDirectProfile_bound c hc m (-τ) σ hσ

end ThetaGlobal.LocalArchBounds

#print axioms ThetaGlobal.LocalArchBounds.archDirectProfile_bound
#print axioms ThetaGlobal.LocalArchBounds.archReflectedProfile_bound
