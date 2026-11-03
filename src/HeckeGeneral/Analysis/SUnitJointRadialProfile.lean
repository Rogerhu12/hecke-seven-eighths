import HeckeGeneral.Analysis.SUnitProfileEuler
import HeckeGeneral.Analysis.SUnitFourierEulerDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The genuine joint radial orbital kernel. Its input is the trace Fourier
Schwartz transform, and its value still includes the norm-one Haar integral.
The two log-radius coordinates act through log R - t - u. Differentiation uses
the proved Euler derivative of that integral, not an assumed interchange. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "T" => sLocalNormOneGroup K S
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- Log-radius profile of the actual j-th Euler transform after trace Fourier. -/
def sUnitFourierLogEulerProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (j : ℕ) (v : ℝ) : ℂ :=
  sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S
      (traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ)) ψ)
    (sUnitExpRadius v)

/-- This is an orbital kernel, including its Haar integral, rather than a
point evaluation of a Fourier function on the archimedean vector space. -/
def sUnitJointRadialProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) (p : ℝ × ℝ) : ℂ :=
  sUnitFourierLogEulerProfile K S φ ψ j (Real.log R.val - p.1 - p.2)

/-- The fixed linear part of the joint log-radius map. -/
def sUnitJointLogRadiusCLM : (ℝ × ℝ) →L[ℝ] ℝ :=
  -ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem sUnitJointLogRadiusCLM_apply (p : ℝ × ℝ) :
    sUnitJointLogRadiusCLM p = -p.1 - p.2 := rfl

theorem sUnitJoint_exp_radius (R : {r : ℝ // 0 < r}) (t u : ℝ) :
    Real.exp (Real.log R.val - t - u) = R.val / (Real.exp t * Real.exp u) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log R.property, div_div]

/-- Positive scalar norms may be substituted without choosing a logarithm
branch or changing the common norm-one quotient. -/
theorem sUnitJointRadialProfile_at_logs (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (R x y : {r : ℝ // 0 < r}) (j : ℕ) :
    sUnitJointRadialProfile K S φ ψ R j (Real.log x.val, Real.log y.val) =
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S
          (traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ)) ψ)
        ⟨R.val / (x.val * y.val), div_pos R.property (mul_pos x.property y.property)⟩ := by
  unfold sUnitJointRadialProfile sUnitFourierLogEulerProfile
  congr 1
  apply Subtype.ext
  simpa only [sUnitExpRadius, Real.exp_log x.property, Real.exp_log y.property] using
    sUnitJoint_exp_radius R (Real.log x.val) (Real.log y.val)

include Γ in
theorem contDiff_sUnitJointRadialProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) :
    ContDiff ℝ ∞ (sUnitJointRadialProfile K S φ ψ R j) :=
  (contDiff_sUnitOrbitalProfile_eulerIter_exp K S Γ
    (traceSchwartzFourier K φ) ψ hψ hψsupport j).comp
      ((contDiff_const.sub contDiff_fst).sub contDiff_snd)

include Γ in
theorem hasDerivAt_sUnitJointRadialProfile_fst (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (v, u))
      (-sUnitJointRadialProfile K S φ ψ R (j + 1) (t, u)) t := by
  have hd := hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ
    (traceSchwartzFourier K φ) ψ hψ hψsupport j (Real.log R.val - t - u)
  simpa only [Function.comp_def, sUnitJointRadialProfile, sUnitFourierLogEulerProfile,
    Pi.sub_apply, id_eq, zero_sub, sub_zero, neg_one_smul] using
    hd.scomp t (((hasDerivAt_const t (Real.log R.val)).sub (hasDerivAt_id t)).sub_const u)

include Γ in
theorem hasDerivAt_sUnitJointRadialProfile_snd (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j : ℕ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (t, v))
      (-sUnitJointRadialProfile K S φ ψ R (j + 1) (t, u)) u := by
  have hd := hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ
    (traceSchwartzFourier K φ) ψ hψ hψsupport j (Real.log R.val - t - u)
  simpa only [Function.comp_def, sUnitJointRadialProfile, sUnitFourierLogEulerProfile,
    zero_sub, neg_one_smul] using
    hd.scomp u ((hasDerivAt_const u (Real.log R.val - t)).sub (hasDerivAt_id u))

include Γ in
theorem iteratedDeriv_sUnitJointRadialProfile_fst (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j m : ℕ) (t u : ℝ) :
    iteratedDeriv m (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (v, u)) t =
      (-1 : ℂ) ^ m * sUnitJointRadialProfile K S φ ψ R (j + m) (t, u) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ']
      have hd : deriv (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (v, u)) =
          fun v => -sUnitJointRadialProfile K S φ ψ R (j + 1) (v, u) := by
        funext v
        exact (hasDerivAt_sUnitJointRadialProfile_fst K S Γ φ ψ hψ hψsupport R j v u).deriv
      rw [hd, iteratedDeriv_fun_neg, ih (j + 1)]
      rw [show j + 1 + m = j + (m + 1) by omega, pow_succ]
      ring

include Γ in
theorem iteratedDeriv_sUnitJointRadialProfile_snd (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (j n : ℕ) (t u : ℝ) :
    iteratedDeriv n (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (t, v)) u =
      (-1 : ℂ) ^ n * sUnitJointRadialProfile K S φ ψ R (j + n) (t, u) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hd : deriv (fun v : ℝ => sUnitJointRadialProfile K S φ ψ R j (t, v)) =
          fun v => -sUnitJointRadialProfile K S φ ψ R (j + 1) (t, v) := by
        funext v
        exact (hasDerivAt_sUnitJointRadialProfile_snd K S Γ φ ψ hψ hψsupport R j t v).deriv
      rw [hd, iteratedDeriv_fun_neg, ih (j + 1)]
      rw [show j + 1 + n = j + (n + 1) by omega, pow_succ]
      ring

include Γ in
/-- Every mixed log-radius derivative is the actual Euler profile at the sum
of the two orders, including when either derivative order is zero. -/
theorem mixed_iteratedDeriv_sUnitJointRadialProfile (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (m n : ℕ) (t u : ℝ) :
    iteratedDeriv m (fun v : ℝ =>
      iteratedDeriv n (fun w : ℝ => sUnitJointRadialProfile K S φ ψ R 0 (v, w)) u) t =
        (-1 : ℂ) ^ (m + n) * sUnitJointRadialProfile K S φ ψ R (m + n) (t, u) := by
  have hn : (fun v : ℝ =>
      iteratedDeriv n (fun w : ℝ => sUnitJointRadialProfile K S φ ψ R 0 (v, w)) u) =
      (fun v => (-1 : ℂ) ^ n * sUnitJointRadialProfile K S φ ψ R n (v, u)) := by
    funext v
    simpa only [zero_add] using
      iteratedDeriv_sUnitJointRadialProfile_snd K S Γ φ ψ hψ hψsupport R 0 n v u
  rw [hn, iteratedDeriv_const_mul_field,
    iteratedDeriv_sUnitJointRadialProfile_fst K S Γ φ ψ hψ hψsupport R n m t u]
  rw [← mul_assoc, ← pow_add, Nat.add_comm n m]

include Γ in
private theorem iteratedDeriv_sUnitFourierLogEulerProfile_shift (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (j n : ℕ) (c t : ℝ) :
    iteratedDeriv n (fun v : ℝ => sUnitFourierLogEulerProfile K S φ ψ j (c + v)) t =
      sUnitFourierLogEulerProfile K S φ ψ (j + n) (c + t) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hd : deriv (fun v : ℝ => sUnitFourierLogEulerProfile K S φ ψ j (c + v)) =
          fun v => sUnitFourierLogEulerProfile K S φ ψ (j + 1) (c + v) := by
        funext v
        have h := hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ
          (traceSchwartzFourier K φ) ψ hψ hψsupport j (c + v)
        have hh := h.scomp v ((hasDerivAt_const v c).add (hasDerivAt_id v))
        simpa only [Function.comp_def, sUnitFourierLogEulerProfile, zero_add, one_smul]
          using hh.deriv
      rw [hd, ih (j + 1), show j + 1 + n = j + (n + 1) by omega]

include Γ in
/-- The full multilinear derivative evaluates the actual Euler orbital profile,
with one joint log-radius linear factor for each input direction. -/
theorem iteratedFDeriv_sUnitJointRadialProfile_apply (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (n : ℕ) (p : ℝ × ℝ) (v : Fin n → ℝ × ℝ) :
    iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) p v =
      (∏ i, (- (v i).1 - (v i).2)) • sUnitJointRadialProfile K S φ ψ R n p := by
  let F : ℝ → ℂ := fun t =>
    sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val + t)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_sUnitOrbitalProfile_eulerIter_exp K S Γ
      (traceSchwartzFourier K φ) ψ hψ hψsupport 0).comp
        (contDiff_const.add contDiff_id)
  have heq : sUnitJointRadialProfile K S φ ψ R 0 = F ∘ sUnitJointLogRadiusCLM := by
    funext x
    change sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val - x.1 - x.2) =
      sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val + (-x.1 - x.2))
    congr 1 <;> ring
  rw [heq, sUnitJointLogRadiusCLM.iteratedFDeriv_comp_right hF p (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  have hd := iteratedDeriv_sUnitFourierLogEulerProfile_shift K S Γ φ ψ
    hψ hψsupport 0 n (Real.log R.val) (sUnitJointLogRadiusCLM p)
  change iteratedDeriv n F (sUnitJointLogRadiusCLM p) = _ at hd
  rw [hd]
  simp only [zero_add, sUnitJointLogRadiusCLM_apply, sUnitJointRadialProfile,
    sub_eq_add_neg, add_assoc]

include Γ in
/-- A bound on the actual full multilinear derivative, obtained by composition
with the fixed joint linear map, rather than just estimates on formal partials. -/
theorem norm_iteratedFDeriv_sUnitJointRadialProfile_le (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (R : {r : ℝ // 0 < r}) (n : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) p‖ ≤
      ‖sUnitJointRadialProfile K S φ ψ R n p‖ * ‖sUnitJointLogRadiusCLM‖ ^ n := by
  let F : ℝ → ℂ := fun v =>
    sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val + v)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_sUnitOrbitalProfile_eulerIter_exp K S Γ
      (traceSchwartzFourier K φ) ψ hψ hψsupport 0).comp
        (contDiff_const.add contDiff_id)
  have heq : sUnitJointRadialProfile K S φ ψ R 0 = F ∘ sUnitJointLogRadiusCLM := by
    funext x
    change sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val - x.1 - x.2) =
      sUnitFourierLogEulerProfile K S φ ψ 0 (Real.log R.val + (-x.1 - x.2))
    congr 1 <;> ring
  rw [heq, sUnitJointLogRadiusCLM.iteratedFDeriv_comp_right hF p (by simp)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n F (sUnitJointLogRadiusCLM p))
    (fun _ : Fin n => sUnitJointLogRadiusCLM)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
  have hd := iteratedDeriv_sUnitFourierLogEulerProfile_shift K S Γ φ ψ
    hψ hψsupport 0 n (Real.log R.val) (sUnitJointLogRadiusCLM p)
  change iteratedDeriv n F (sUnitJointLogRadiusCLM p) = _ at hd
  rw [hd] at hb
  simpa only [zero_add, sUnitJointRadialProfile, sUnitJointLogRadiusCLM_apply,
    sub_eq_add_neg, add_assoc] using hb

local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- The finite-order joint derivative bound uses one finite set of original
Schwartz seminorms, independent of φ, R, the evaluation point, and the order.
Its region is exactly the large-profile-radius region. -/
theorem exists_sUnitJointRadialProfile_iteratedFDeriv_power_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, ∀ p : ℝ × ℝ,
      1 ≤ Real.exp (Real.log R.val - p.1 - p.2) → ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-B) := by
  obtain ⟨s, C, hC, hb⟩ := exists_sUnitFourierEulerProfile_power_decay
    K S Γ ψ hψ hψsupport B M hM hOrder J
  let A : ℝ := max 1 ‖sUnitJointLogRadiusCLM‖
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨s, C * A ^ J, mul_nonneg hC (pow_nonneg (zero_le_one.trans hA) _),
    fun φ R p hp n hn => ?_⟩
  have hscale : ‖sUnitJointLogRadiusCLM‖ ^ n ≤ A ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hA hn)
  have hprof := hb φ (sUnitExpRadius (Real.log R.val - p.1 - p.2)) hp n hn
  change ‖sUnitJointRadialProfile K S φ ψ R n p‖ ≤
    C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-B) at hprof
  calc
    _ ≤ ‖sUnitJointRadialProfile K S φ ψ R n p‖ * ‖sUnitJointLogRadiusCLM‖ ^ n :=
      norm_iteratedFDeriv_sUnitJointRadialProfile_le K S Γ φ ψ hψ hψsupport R n p
    _ ≤ (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-B)) * A ^ J :=
      mul_le_mul hprof hscale (pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
          (Real.rpow_nonneg (Real.exp_pos _).le _))
    _ = (C * A ^ J) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (Real.exp (Real.log R.val - p.1 - p.2)) ^ (-B) := by ring

end HeckeGeneral.Analysis
