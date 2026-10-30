import HeckeGeneral.Analysis.TraceSchwartzEuler
import HeckeGeneral.Analysis.SUnitSchwartzDecay
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual Euler inputs for orbital differentiation: pointwise derivatives,
joint continuity and uniform L1 bounds on compact log-radius intervals.
The profile derivative is obtained by FTC and Fubini, without an assumed
pointwise dominating function. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical nonZeroDivisors ContDiff Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "D" => (Module.finrank ℚ K : ℝ)
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def sUnitExpRadius (t : ℝ) : {r : ℝ // 0 < r} := ⟨Real.exp t, Real.exp_pos t⟩

theorem continuous_sUnitExpRadius : Continuous sUnitExpRadius :=
  Real.continuous_exp.subtype_mk _

/-- The finite coordinates are unchanged by actual positive norm dilation. -/
theorem sLocalSchwartzSlice_exp_eq (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (t : ℝ) (x : T) :
    sLocalSchwartzSlice K S φ ψ (sUnitExpRadius t) x =
      φ (Real.exp (t / D) •
        (traceToMixed K).symm (((x : G).1 : mixedEmbedding.mixedSpace K))) *
      ψ (fun v => ((x : G).2 v).val) := by
  simp [sLocalSchwartzSlice, sLocalTensorTestFunction, sLocalNormSection,
    sUnitExpRadius, realScaleMixedUnit_val, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, traceNormSection_exp_scale]

/-- The literal slice has the Euler slice as its log-radius derivative. -/
theorem hasDerivAt_sLocalSchwartzSlice_exp (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (x : T) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sLocalSchwartzSlice K S φ ψ (sUnitExpRadius u) x)
      (sLocalSchwartzSlice K S (traceSchwartzEulerCLM K φ) ψ (sUnitExpRadius t) x) t := by
  simp_rw [sLocalSchwartzSlice_exp_eq]
  exact (hasDerivAt_traceSchwartz_normDilation K φ
    ((traceToMixed K).symm (((x : G).1 : mixedEmbedding.mixedSpace K))) t).mul_const _

/-- Joint continuity is proved for the actual slice and the actual norm-one group. -/
theorem continuous_sLocalSchwartzSlice_exp (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (hψ : Continuous ψ) :
    Continuous (fun p : ℝ × T =>
      sLocalSchwartzSlice K S φ ψ (sUnitExpRadius p.1) p.2) := by
  exact (continuous_sLocalTensorTestFunction K S φ ψ hψ).comp
    (((continuous_sLocalNormSection K S).comp
      (continuous_sUnitExpRadius.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd))

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

include Γ in
/-- The compact-interval L1 constant is independent of the Schwartz test.
The same theorem applies to φ, Eφ and every actual iterated Euler transform. -/
theorem exists_sLocalSchwartzSlice_exp_interval_integral_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (M : ℕ) (hM : Module.finrank ℤ L < M) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ, ∀ t ∈ Set.Icc a b,
      (∫ x : T, ‖sLocalSchwartzSlice K S φ ψ (sUnitExpRadius t) x‖
        ∂sUnitHaarMeasure K S) ≤ C * SchwartzMap.seminorm ℂ M 0 φ := by
  obtain ⟨C, hC, hbound⟩ := exists_sLocalSchwartzSlice_radial_integral_bound
    K S Γ ψ hψ hψsupport M hM
  let f : ℝ → ℝ := fun t => ((Real.exp (t / D))⁻¹) ^ M
  have hf : Continuous f := by
    exact ((Real.continuous_exp.comp (continuous_id.div_const D)).inv₀
      (fun t => (Real.exp_pos (t / D)).ne')).pow M
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.continuousOn
  refine ⟨C * max B 0, mul_nonneg hC (le_max_right _ _), fun φ t ht => ?_⟩
  have hBt : f t ≤ max B 0 :=
    (hB (Set.mem_image_of_mem f ht)).trans (le_max_left _ _)
  have hraw := hbound φ (sUnitExpRadius t)
  change (∫ x : T, ‖sLocalSchwartzSlice K S φ ψ (sUnitExpRadius t) x‖
      ∂sUnitHaarMeasure K S) ≤
    C * SchwartzMap.seminorm ℂ M 0 φ * (((Real.exp t) ^ D⁻¹)⁻¹) ^ M at hraw
  rw [traceNormSection_exp_scale] at hraw
  calc
    _ ≤ C * SchwartzMap.seminorm ℂ M 0 φ * f t := hraw
    _ ≤ C * SchwartzMap.seminorm ℂ M 0 φ * max B 0 :=
      mul_le_mul_of_nonneg_left hBt
        (mul_nonneg hC (apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ))
    _ = _ := by ring

include Γ in
theorem integrable_sLocalSchwartzEulerSlice_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (j : ℕ) (t : ℝ) :
    Integrable (sLocalSchwartzSlice K S (traceSchwartzEulerIterCLM K j φ) ψ
      (sUnitExpRadius t)) (sUnitHaarMeasure K S) :=
  integrable_sLocalSchwartzSlice K S Γ (traceSchwartzEulerIterCLM K j φ)
    ψ hψ hψsupport (sUnitExpRadius t)

include Γ in
/-- Actual compact log-radius product integrability, derived from the radial
Schwartz estimate. No product-integrability input is required. -/
theorem integrable_sLocalSchwartzSlice_exp_prod
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (a b : ℝ) :
    Integrable (fun p : ℝ × T =>
      sLocalSchwartzSlice K S φ ψ (sUnitExpRadius p.1) p.2)
      ((volume.restrict (Set.Icc a b)).prod (sUnitHaarMeasure K S)) := by
  let M := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hbound⟩ :=
    exists_sLocalSchwartzSlice_exp_interval_integral_bound K S Γ ψ hψ hψsupport
      M (Nat.lt_succ_self _) a b
  have hmeas := (continuous_sLocalSchwartzSlice_exp K S φ ψ hψ).aestronglyMeasurable
    (μ := (volume.restrict (Set.Icc a b)).prod (sUnitHaarMeasure K S))
  apply (integrable_prod_iff hmeas).2
  refine ⟨Filter.Eventually.of_forall (fun t =>
    integrable_sLocalSchwartzSlice K S Γ φ ψ hψ hψsupport (sUnitExpRadius t)), ?_⟩
  apply (integrable_const (C * SchwartzMap.seminorm ℂ M 0 φ)).mono'
    hmeas.norm.integral_prod_right'
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  exact hbound φ t ht

include Γ in
/-- The genuine profile increment is the integral of its Euler profile.
The interchange follows from the proved product integrability. -/
theorem sUnitOrbitalProfile_exp_sub_eq_integral_euler
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (a b : ℝ) (hab : a ≤ b) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius b) -
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius a) =
      ∫ t in Set.Icc a b,
        sUnitOrbitalProfile K S
          (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ)
          (sUnitExpRadius t) := by
  have hftc (x : T) :
      (∫ t in Set.Icc a b,
        sLocalSchwartzSlice K S (traceSchwartzEulerCLM K φ) ψ (sUnitExpRadius t) x) =
      sLocalSchwartzSlice K S φ ψ (sUnitExpRadius b) x -
        sLocalSchwartzSlice K S φ ψ (sUnitExpRadius a) x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_sLocalSchwartzSlice_exp K S φ ψ x t)
    exact ((continuous_sLocalSchwartzSlice_exp K S (traceSchwartzEulerCLM K φ) ψ hψ).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hprod := integrable_sLocalSchwartzSlice_exp_prod K S Γ
    (traceSchwartzEulerCLM K φ) ψ hψ hψsupport a b
  change (∫ x : T, sLocalSchwartzSlice K S φ ψ (sUnitExpRadius b) x
      ∂sUnitHaarMeasure K S) -
    (∫ x : T, sLocalSchwartzSlice K S φ ψ (sUnitExpRadius a) x
      ∂sUnitHaarMeasure K S) =
    ∫ t in Set.Icc a b, ∫ x : T,
      sLocalSchwartzSlice K S (traceSchwartzEulerCLM K φ) ψ (sUnitExpRadius t) x
      ∂sUnitHaarMeasure K S
  rw [← integral_sub
    (integrable_sLocalSchwartzSlice K S Γ φ ψ hψ hψsupport (sUnitExpRadius b))
    (integrable_sLocalSchwartzSlice K S Γ φ ψ hψ hψsupport (sUnitExpRadius a)),
    integral_integral_swap hprod]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hftc x).symm))

include Γ in
/-- Continuity of the actual profile follows from its FTC increment and
local integrability of the Euler profile, rather than being assumed. -/
theorem continuous_sUnitOrbitalProfile_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) :
    Continuous (fun t : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)) := by
  let P : ℝ → ℂ := fun t => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)
  let Q : ℝ → ℂ := fun t => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ) (sUnitExpRadius t)
  change Continuous P
  rw [continuous_iff_continuousAt]
  intro t
  have hQ : IntegrableOn Q (Set.Icc (t - 1) (t + 1)) := by
    exact (integrable_sLocalSchwartzSlice_exp_prod K S Γ
      (traceSchwartzEulerCLM K φ) ψ hψ hψsupport (t - 1) (t + 1)).integral_prod_left
  have hprim := (intervalIntegral.continuousOn_primitive_Icc hQ).add
    (continuousOn_const (c := P (t - 1)))
  have hP : ContinuousOn P (Set.Icc (t - 1) (t + 1)) := by
    apply hprim.congr
    intro u hu
    exact sub_eq_iff_eq_add.mp
      (sUnitOrbitalProfile_exp_sub_eq_integral_euler K S Γ φ ψ hψ hψsupport
        (t - 1) u hu.1)
  exact hP.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

include Γ in
/-- Differentiation of the genuine orbital profile in log radius. All
continuity and integral-interchange requirements have been proved above. -/
theorem hasDerivAt_sUnitOrbitalProfile_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius u))
      (sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ)
        (sUnitExpRadius t)) t := by
  let P : ℝ → ℂ := fun u => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius u)
  let Q : ℝ → ℂ := fun u => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ) (sUnitExpRadius u)
  have hQ : Continuous Q := continuous_sUnitOrbitalProfile_exp K S Γ
    (traceSchwartzEulerCLM K φ) ψ hψ hψsupport
  have hderiv := ((hQ.integral_hasStrictDerivAt (t - 1) t).hasDerivAt).add_const
    (P (t - 1))
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show t - 1 < t by linarith)
    (show t < t + 1 by linarith)] with u hu
  change P u = (∫ s in (t - 1)..u, Q s) + P (t - 1)
  rw [intervalIntegral.integral_of_le hu.1, ← integral_Icc_eq_integral_Ioc]
  exact sub_eq_iff_eq_add.mp
    (sUnitOrbitalProfile_exp_sub_eq_integral_euler K S Γ φ ψ hψ hψsupport
      (t - 1) u hu.1)

include Γ in
theorem deriv_sUnitOrbitalProfile_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (t : ℝ) :
    deriv (fun u : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius u)) t =
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ)
        (sUnitExpRadius t) :=
  (hasDerivAt_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport t).deriv

include Γ in
/-- The same actual derivative identity for every iterated Euler input. -/
theorem hasDerivAt_sUnitOrbitalProfile_eulerIter_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j φ) ψ)
      (sUnitExpRadius u))
      (sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K (j + 1) φ) ψ)
        (sUnitExpRadius t)) t := by
  simpa only [traceSchwartzEulerIterCLM_succ] using
    hasDerivAt_sUnitOrbitalProfile_exp K S Γ (traceSchwartzEulerIterCLM K j φ)
      ψ hψ hψsupport t

include Γ in
/-- Every finite differentiability order is obtained from the actual Euler
derivative recursion. The induction ranges over all Schwartz inputs. -/
theorem contDiff_nat_sUnitOrbitalProfile_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (n : ℕ) :
    ContDiff ℝ n (fun t : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)) := by
  induction n generalizing φ with
  | zero =>
      exact contDiff_zero.mpr
        (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport)
  | succ n ih =>
      change ContDiff ℝ ((n : ℕ∞ω) + 1) _
      apply contDiff_succ_iff_deriv.mpr
      refine ⟨fun t => (hasDerivAt_sUnitOrbitalProfile_exp K S Γ
        φ ψ hψ hψsupport t).differentiableAt, by simp, ?_⟩
      have hderiv :
          deriv (fun t : ℝ => sUnitOrbitalProfile K S
            (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)) =
          (fun t : ℝ => sUnitOrbitalProfile K S
            (sLocalTensorTestFunction K S (traceSchwartzEulerCLM K φ) ψ)
            (sUnitExpRadius t)) := by
        funext t
        exact deriv_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport t
      rw [hderiv]
      exact ih (traceSchwartzEulerCLM K φ)

include Γ in
/-- The actual log-radius orbital profile is smooth. Here `∞` is the
mathlib smooth differentiability order, rather than the analytic order `ω`. -/
theorem contDiff_sUnitOrbitalProfile_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun t : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport n

include Γ in
theorem contDiff_sUnitOrbitalProfile_eulerIter_exp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (j : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => sUnitOrbitalProfile K S
      (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j φ) ψ)
      (sUnitExpRadius t)) :=
  contDiff_sUnitOrbitalProfile_exp K S Γ (traceSchwartzEulerIterCLM K j φ)
    ψ hψ hψsupport

end HeckeGeneral.Analysis
