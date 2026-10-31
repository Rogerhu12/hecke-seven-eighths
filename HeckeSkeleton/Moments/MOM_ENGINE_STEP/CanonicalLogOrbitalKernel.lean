import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExponentialTiltSchwartz
import HeckeSkeleton.SmallRadius.SmallRadiusUniformPointBound
import HeckeGeneral.Analysis.SUnitProfileFunctional

/-!
# A common Schwartz kernel on the complete log-radius axis

The genuine orbital profile is multiplied by a fixed small positive
Mellin tilt.  Two proved positive-Mellin estimates, with weights on
either side of that tilt, give rapid decay at both ends of the real
axis.  Differentiation is the actual shifted Euler operator on the
original test.  This constructs a continuous linear Schwartz operator;
no translated-profile chart or bound on a transformed source is an
input.

The radius identity at the end applies to every positive row norm.
There is no row-dependent cutoff or row-dependent kernel.
-/

noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Analysis.SmallRadiusOrbitalFTCDraft
open HeckeGeneral.Analysis.SmallRadiusUniformPointDraft

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Differentiation after a Mellin tilt remains a genuine continuous
linear operator on the original Schwartz space. -/
def shiftedEulerCLM (δ : ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  δ • ContinuousLinearMap.id ℝ _ + traceSchwartzEulerCLM K

def shiftedEulerIterCLM (δ : ℝ) : ℕ → 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ)
  | 0 => ContinuousLinearMap.id ℝ _
  | n + 1 => (shiftedEulerCLM K δ).comp (shiftedEulerIterCLM δ n)

@[simp] theorem shiftedEulerIterCLM_zero (δ : ℝ) (φ : 𝓢(V, ℂ)) :
    shiftedEulerIterCLM K δ 0 φ = φ := rfl

@[simp] theorem shiftedEulerIterCLM_succ (δ : ℝ) (n : ℕ) (φ : 𝓢(V, ℂ)) :
    shiftedEulerIterCLM K δ (n + 1) φ =
      shiftedEulerCLM K δ (shiftedEulerIterCLM K δ n φ) := rfl

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)
variable (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- The actual Haar orbital profile, with its positive Mellin tilt. -/
def profile (δ : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) : ℂ :=
  Real.exp (δ * t) • sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)

include Γ in
theorem orbital_real_smul (c : ℝ) (φ : 𝓢(V, ℂ)) (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S (c • φ) ψ) r =
      c • sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r := by
  have h := ((sUnitProfileCLM K S Γ ψ hψ hψsupport r).restrictScalars ℝ).map_smul c φ
  change sUnitProfileCLM K S Γ ψ hψ hψsupport r (c • φ) =
    c • sUnitProfileCLM K S Γ ψ hψ hψsupport r φ at h
  simpa only [sUnitProfileCLM_apply] using h

include Γ in
theorem profile_add (δ : ℝ) (φ η : 𝓢(V, ℂ)) (t : ℝ) :
    profile K S ψ δ (φ + η) t =
      profile K S ψ δ φ t + profile K S ψ δ η t := by
  simp only [profile, sUnitOrbitalProfile_tensor_add K S Γ ψ hψ hψsupport,
    smul_add]

include Γ in
theorem profile_real_smul (δ c : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) :
    profile K S ψ δ (c • φ) t = c • profile K S ψ δ φ t := by
  unfold profile
  rw [orbital_real_smul K S Γ ψ hψ hψsupport]
  exact smul_comm _ _ _

include Γ in
theorem orbital_shiftedEuler (δ : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) :
    sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (shiftedEulerCLM K δ φ) ψ) (sUnitExpRadius t) =
      δ • sUnitOrbitalProfile K S
          (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t) +
        sUnitOrbitalProfile K S
          (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ)
          (sUnitExpRadius t) := by
  change sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S (δ • φ + traceSchwartzEulerCLM K φ) ψ)
      (sUnitExpRadius t) = _
  rw [sUnitOrbitalProfile_tensor_add K S Γ ψ hψ hψsupport,
    orbital_real_smul K S Γ ψ hψ hψsupport]

include Γ in
theorem hasDerivAt_profile (δ : ℝ) (φ : 𝓢(V, ℂ)) (t : ℝ) :
    HasDerivAt (profile K S ψ δ φ)
      (profile K S ψ δ (shiftedEulerCLM K δ φ) t) t := by
  have hd := (((hasDerivAt_id t).const_mul δ).exp).smul
    (hasDerivAt_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport t)
  apply hd.congr_deriv
  unfold profile
  rw [orbital_shiftedEuler K S Γ ψ hψ hψsupport]
  simp only [mul_one, smul_add, smul_smul]
  exact add_comm _ _

include Γ in
theorem iteratedDeriv_profile (δ : ℝ) (φ : 𝓢(V, ℂ)) (n : ℕ) :
    iteratedDeriv n (profile K S ψ δ φ) =
      profile K S ψ δ (shiftedEulerIterCLM K δ n φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hasDerivAt_profile K S Γ ψ hψ hψsupport δ
        (shiftedEulerIterCLM K δ n φ) t).deriv

include Γ in
theorem contDiff_profile (δ : ℝ) (φ : 𝓢(V, ℂ)) :
    ContDiff ℝ ∞ (profile K S ψ δ φ) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul
    (contDiff_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport)

section Decay

variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]

include Γ in
/-- The actual positive-Mellin estimate is composed with a fixed shifted
Euler iterate.  All original seminorm indices precede the free test. -/
theorem exists_weighted_shiftedEuler_bound (δ σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(V, ℂ), ∀ t : ℝ,
      Real.exp (σ * t) *
        ‖sUnitOrbitalProfile K S
          (sLocalTensorTestFunction K S (shiftedEulerIterCLM K δ n φ) ψ)
          (sUnitExpRadius t)‖ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s₀, C₀, hC₀, hpoint⟩ :=
    exists_uniform_weighted_logEuler_point_bound K S Γ ψ hψ hψsupport σ hσ hσ1 0
  let T := shiftedEulerIterCLM K δ n
  let q : Seminorm ℝ 𝓢(V, ℂ) :=
    (s₀.sup (schwartzSeminormFamily ℝ V ℂ)).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup (fun i _ => hp.continuous_seminorm i)).comp T.continuous
  obtain ⟨s, D, hD, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hD
  refine ⟨s, C₀ * (D : ℝ), mul_pos hC₀ hDpos, fun φ t => ?_⟩
  have hsemi : s₀.sup (schwartzSeminormFamily ℝ V ℂ) (T φ) ≤
      (D : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    Seminorm.le_def.mp hbound φ
  have hraw := hpoint (T φ) 0 le_rfl t
  simp only [sUnitEulerLogProfile, traceSchwartzEulerIterCLM_zero] at hraw
  exact (hraw.trans (mul_le_mul_of_nonneg_left hsemi hC₀.le)).trans_eq
    (mul_assoc _ _ _).symm

include Γ in
/-- Every target Schwartz derivative and polynomial weight is uniformly
controlled by finitely many original seminorms.  The fixed tilt can be
arbitrarily small; the bounds hold on the complete log-radius axis. -/
theorem exists_profile_schwartz_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(V, ℂ), ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (profile K S ψ δ φ) t‖ ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s₋, C₋, hC₋, hminus⟩ := exists_weighted_shiftedEuler_bound
    K S Γ ψ hψ hψsupport δ (δ - δ / 2) (by linarith) (by linarith) n
  obtain ⟨s₊, C₊, hC₊, hplus⟩ := exists_weighted_shiftedEuler_bound
    K S Γ ψ hψ hψsupport δ (δ + δ / 2) (by linarith) (by linarith) n
  let s := s₋ ∪ s₊
  have hm (φ : 𝓢(V, ℂ)) :
      s₋.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) φ
  have hp (φ : 𝓢(V, ℂ)) :
      s₊.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) φ
  let C : ℝ := ((k.factorial : ℝ) / (δ / 2) ^ k) * (C₋ + C₊)
  refine ⟨s, C, by dsimp only [C]; positivity, fun φ t => ?_⟩
  have hbminus : Real.exp ((δ - δ / 2) * t) *
      ‖sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (shiftedEulerIterCLM K δ n φ) ψ)
        (sUnitExpRadius t)‖ ≤ (C₋ + C₊) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    (hminus φ t).trans (mul_le_mul (le_add_of_nonneg_right hC₊.le) (hm φ)
      (apply_nonneg _ _) (add_nonneg hC₋.le hC₊.le))
  have hbplus : Real.exp ((δ + δ / 2) * t) *
      ‖sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (shiftedEulerIterCLM K δ n φ) ψ)
        (sUnitExpRadius t)‖ ≤ (C₋ + C₊) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    (hplus φ t).trans (mul_le_mul (le_add_of_nonneg_left hC₋.le) (hp φ)
      (apply_nonneg _ _) (add_nonneg hC₋.le hC₊.le))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_profile K S Γ ψ hψ hψsupport]
  exact (ExponentialTilt.polynomial_weight_le k (by linarith : 0 < δ / 2) t _
    hbminus hbplus).trans_eq (mul_assoc _ _ _).symm

/-- The constructed log-radius transport, as a genuine continuous real
linear map between Schwartz spaces. -/
def orbitalCLM (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    𝓢(V, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℝ) (profile K S ψ δ)
    (profile_add K S Γ ψ hψ hψsupport δ)
    (fun c φ t => profile_real_smul K S Γ ψ hψ hψsupport δ c φ t)
    (contDiff_profile K S Γ ψ hψ hψsupport δ) (by
      rintro ⟨k, n⟩
      obtain ⟨s, C, hC, hbound⟩ :=
        exists_profile_schwartz_bound K S Γ ψ hψ hψsupport δ hδ hδ1 k n
      exact ⟨s, C, hC.le, hbound⟩)

@[simp] theorem orbitalCLM_apply (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (φ : 𝓢(V, ℂ)) (t : ℝ) :
    orbitalCLM K S Γ ψ hψ hψsupport δ hδ hδ1 φ t = profile K S ψ δ φ t := rfl

/-- The first transform uses the actual trace Fourier operator, including
its original conjugation and Jacobian, before the common log kernel. -/
def fourierCLM (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    𝓢(V, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (orbitalCLM K S Γ ψ hψ hψsupport δ hδ hδ1).comp
    ((traceSchwartzFourierCLM K).restrictScalars ℝ)

@[simp] theorem fourierCLM_apply (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (φ : 𝓢(V, ℂ)) (t : ℝ) :
    fourierCLM K S Γ ψ hψ hψsupport δ hδ hδ1 φ t =
      profile K S ψ δ (traceSchwartzFourier K φ) t := rfl

/-- Any finite family of output seminorms has a common original source
bound.  Its constants precede the test, all rows and all columns. -/
theorem fourier_finite_seminorm_bound
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : 𝓢(V, ℂ),
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (fourierCLM K S Γ ψ hψ hψsupport δ hδ hδ1 φ) ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  let T := fourierCLM K S Γ ψ hψ hψsupport δ hδ hδ1
  let q : Seminorm ℝ 𝓢(V, ℂ) :=
    (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ V ℂ) q hq
  refine ⟨s, (C : ℝ), by exact_mod_cast pos_iff_ne_zero.mpr hC, fun φ => ?_⟩
  exact Seminorm.le_def.mp hbound φ

/-- Exact evaluation at every positive radius.  The small Mellin factor
is explicit and is retained by the arithmetic source construction. -/
theorem orbital_at_radius (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (φ : 𝓢(V, ℂ)) (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r =
      r.val ^ (-δ) • orbitalCLM K S Γ ψ hψ hψsupport δ hδ hδ1 φ (Real.log r.val) := by
  rw [orbitalCLM_apply, profile]
  have hr : sUnitExpRadius (Real.log r.val) = r := by
    apply Subtype.ext
    exact Real.exp_log r.property
  rw [hr, smul_smul, Real.rpow_def_of_pos r.property, ← Real.exp_add]
  rw [show Real.log r.val * -δ + δ * Real.log r.val = 0 by ring,
    Real.exp_zero, one_smul]

/-- The exact translated common kernel for one row radius and two
column norms.  Every positive row radius is covered by the same kernel. -/
theorem orbital_at_quotient (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (φ : 𝓢(V, ℂ)) (ρ a b : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨ρ / (a * b), div_pos hρ (mul_pos ha hb)⟩ =
      (ρ ^ (-δ) * a ^ δ * b ^ δ) •
        orbitalCLM K S Γ ψ hψ hψsupport δ hδ hδ1 φ
          (Real.log ρ - Real.log a - Real.log b) := by
  rw [orbitalCLM_apply, profile]
  have hr : sUnitExpRadius (Real.log ρ - Real.log a - Real.log b) =
      ⟨ρ / (a * b), div_pos hρ (mul_pos ha hb)⟩ := by
    apply Subtype.ext
    simp only [sUnitExpRadius, Real.exp_sub, Real.exp_log hρ, Real.exp_log ha,
      Real.exp_log hb, div_div]
  rw [hr, smul_smul, Real.rpow_def_of_pos hρ, Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos hb, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  rw [show ((Real.log ρ * -δ + Real.log a * δ) + Real.log b * δ) +
      δ * (Real.log ρ - Real.log a - Real.log b) = 0 by ring,
    Real.exp_zero, one_smul]

end Decay

end HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital.orbitalCLM
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital.fourierCLM
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital.fourier_finite_seminorm_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogOrbital.orbital_at_quotient
