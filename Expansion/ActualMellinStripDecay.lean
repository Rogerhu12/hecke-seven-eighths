import Expansion.PhysicalPositiveMellinInversion
import HeckeSkeleton.HighBinSupport.LogFourierDecay

/-!
# Uniform rapid decay of the actual additive Mellin transform

The two positive endpoint moments dominate every exponential weight in a
fixed compact positive strip.  Iterated differentiation of the actual
weighted orbital profile gives uniform L1 derivative norms.  Fourier
integration by parts therefore selects its constant before the real part
and imaginary height.  No vertical-decay or contour bound is an input.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open Set MeasureTheory Complex
open HighBinBoundary
open scoped Classical ContDiff Topology

theorem exponential_weight_le_endpoints {lower upper sigma : ℝ}
    (hlo : lower ≤ sigma) (hhi : sigma ≤ upper) (v : ℝ) :
    Real.exp (sigma * v) ≤ Real.exp (lower * v) + Real.exp (upper * v) := by
  by_cases hv : 0 ≤ v
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hv)).trans
      (le_add_of_nonneg_left (Real.exp_nonneg _))
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo (le_of_not_ge hv))).trans
      (le_add_of_nonneg_right (Real.exp_nonneg _))

/-- Uniform logarithmic Fourier decay follows from the actual L1 moments
of the Euler-derivative family at the two endpoints. -/
theorem uniform_logFourier_weightedProfile_bound
    (P : ℕ → ℝ → ℂ) (hc : ∀ j, ContDiff ℝ ∞ (P j))
    (hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v)
    {lower upper : ℝ} (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hlo : ∀ j, Integrable (fun v => Real.exp (lower * v) * ‖P j v‖))
    (hhi : ∀ j, Integrable (fun v => Real.exp (upper * v) * ‖P j v‖))
    (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ sigma ∈ Icc lower upper, ∀ t : ℝ,
      (1 + |t|) ^ n * ‖LogFourier.transform (LogFourier.weightedProfile P sigma 0) t‖ ≤ D := by
  have hupper : 0 ≤ upper := hlower.le.trans hlu
  have hi (sigma : ℝ) (hsigma : sigma ∈ Icc lower upper) (j : ℕ) :
      Integrable (fun v => Real.exp (sigma * v) * ‖P j v‖) := by
    have hm : AEStronglyMeasurable (fun v : ℝ => Real.exp (sigma * v) * ‖P j v‖) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (hc j).continuous.norm).aestronglyMeasurable
    apply ((hlo j).add (hhi j)).mono' hm
    filter_upwards [] with v
    rw [Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_right
      (exponential_weight_le_endpoints hsigma.1 hsigma.2 v) (norm_nonneg _)).trans_eq
        (by simp only [Pi.add_apply, add_mul])
  have hiter (sigma : ℝ) (hsigma : sigma ∈ Icc lower upper) (m j : ℕ) :
      Integrable (iteratedDeriv m (LogFourier.weightedProfile P sigma j)) :=
    LogFourier.weightedProfile_iteratedDeriv_integrable P sigma hc hd (hi sigma hsigma) m j
  have huniform : ∀ m j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ sigma ∈ Icc lower upper,
      (∫ v : ℝ, ‖iteratedDeriv m (LogFourier.weightedProfile P sigma j) v‖) ≤ D := by
    intro m
    induction m with
    | zero =>
        intro j
        let D : ℝ := (∫ v : ℝ, Real.exp (lower * v) * ‖P j v‖) +
          ∫ v : ℝ, Real.exp (upper * v) * ‖P j v‖
        refine ⟨D, by dsimp [D]; positivity, ?_⟩
        intro sigma hsigma
        simp only [iteratedDeriv_zero]
        calc
          (∫ v : ℝ, ‖LogFourier.weightedProfile P sigma j v‖) ≤
              ∫ v : ℝ, Real.exp (lower * v) * ‖P j v‖ +
                Real.exp (upper * v) * ‖P j v‖ := by
            apply integral_mono_ae (hiter sigma hsigma 0 j).norm ((hlo j).add (hhi j))
            filter_upwards [] with v
            simp only [iteratedDeriv_zero, Pi.add_apply, LogFourier.weightedProfile,
              norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact (mul_le_mul_of_nonneg_right
              (exponential_weight_le_endpoints hsigma.1 hsigma.2 v) (norm_nonneg _)).trans_eq
                (by ring)
          _ = D := integral_add (hlo j) (hhi j)
    | succ m ih =>
        intro j
        obtain ⟨D0, hD0, hb0⟩ := ih j
        obtain ⟨D1, hD1, hb1⟩ := ih (j + 1)
        refine ⟨upper * D0 + D1, by positivity, ?_⟩
        intro sigma hsigma
        have hcm : ContDiff ℝ ∞
            (fun v : ℝ => (sigma : ℂ) * LogFourier.weightedProfile P sigma j v) :=
          contDiff_const.mul (LogFourier.weightedProfile_smooth P sigma hc j)
        have heq : iteratedDeriv (m + 1) (LogFourier.weightedProfile P sigma j) =
            fun v => (sigma : ℂ) * iteratedDeriv m (LogFourier.weightedProfile P sigma j) v +
              iteratedDeriv m (LogFourier.weightedProfile P sigma (j + 1)) v := by
          rw [iteratedDeriv_succ', LogFourier.weightedProfile_deriv P sigma hd j]
          funext v
          rw [iteratedDeriv_fun_add (hcm.of_le (by simp)).contDiffAt
            ((LogFourier.weightedProfile_smooth P sigma hc (j + 1)).of_le (by simp)).contDiffAt,
            iteratedDeriv_const_mul_field]
        have hsigma0 : 0 ≤ sigma := hlower.le.trans hsigma.1
        have hsigmaNorm : ‖(sigma : ℂ)‖ ≤ upper := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsigma0] using hsigma.2
        calc
          (∫ v : ℝ, ‖iteratedDeriv (m + 1) (LogFourier.weightedProfile P sigma j) v‖) ≤
              ∫ v : ℝ, upper * ‖iteratedDeriv m (LogFourier.weightedProfile P sigma j) v‖ +
                ‖iteratedDeriv m (LogFourier.weightedProfile P sigma (j + 1)) v‖ := by
            apply integral_mono_ae (hiter sigma hsigma (m + 1) j).norm
              (((hiter sigma hsigma m j).norm.const_mul upper).add
                (hiter sigma hsigma m (j + 1)).norm)
            filter_upwards [] with v
            rw [heq]
            exact (norm_add_le _ _).trans (add_le_add
              (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hsigmaNorm (norm_nonneg _)) le_rfl)
          _ = upper * (∫ v : ℝ, ‖iteratedDeriv m (LogFourier.weightedProfile P sigma j) v‖) +
              ∫ v : ℝ, ‖iteratedDeriv m (LogFourier.weightedProfile P sigma (j + 1)) v‖ := by
            rw [integral_add ((hiter sigma hsigma m j).norm.const_mul upper)
              (hiter sigma hsigma m (j + 1)).norm, integral_const_mul]
          _ ≤ upper * D0 + D1 :=
            add_le_add (mul_le_mul_of_nonneg_left (hb0 sigma hsigma) hupper) (hb1 sigma hsigma)
  obtain ⟨D0, hD0, hb0⟩ := huniform 0 0
  obtain ⟨Dn, hDn, hbn⟩ := huniform n 0
  refine ⟨2 ^ n * (D0 + Dn) + 1, by positivity, ?_⟩
  intro sigma hsigma t
  have hb := LogFourier.weighted_transform_bound (LogFourier.weightedProfile P sigma 0)
    (LogFourier.weightedProfile_smooth P sigma hc 0) (fun m => hiter sigma hsigma m 0) n t
  have hb0' : (∫ v : ℝ, ‖LogFourier.weightedProfile P sigma 0 v‖) ≤ D0 := by
    simpa only [iteratedDeriv_zero] using hb0 sigma hsigma
  have hco := mul_le_mul_of_nonneg_left (add_le_add hb0' (hbn sigma hsigma))
    (by positivity : (0 : ℝ) ≤ 2 ^ n)
  exact hb.trans (hco.trans (by linarith))

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualOrbitalPositiveMomentDraft
open Expansion.PhysicalPositiveMellin

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

section Orbital

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Gamma : Subgroup (S.unit K)) [Gamma.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → (Subtype.val v).adicCompletion K)

include Gamma in
/-- Actual orbital decay is uniform on the entire chosen positive strip. -/
theorem exists_actual_orbitalMellin_strip_rapid_bound
    (phi : SchwartzMap V ℂ) (test : A → ℂ)
    (htest : Continuous test) (hsupport : HasCompactSupport test)
    (lower upper : ℝ) (hlower : 0 < lower) (hlu : lower ≤ upper) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ sigma ∈ Icc lower upper, ∀ t : ℝ,
      (1 + |t|) ^ n * ‖ActualOrbital.orbitalMellin K S phi test
        ((sigma : ℂ) + t * I)‖ ≤ D := by
  let P : ℕ → ℝ → ℂ := fun j v => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j phi) test) (sUnitExpRadius v)
  have hc : ∀ j, ContDiff ℝ ∞ (P j) := fun j =>
    contDiff_sUnitOrbitalProfile_eulerIter_exp K S Gamma phi test htest hsupport j
  have hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v := fun j v =>
    hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Gamma phi test htest hsupport j v
  have hlo : ∀ j, Integrable (fun v => Real.exp (lower * v) * ‖P j v‖) := fun j =>
    integrable_weightedLogOrbitalNorm_positive K S Gamma (traceSchwartzEulerIterCLM K j phi)
      test htest hsupport hlower
  have hhi : ∀ j, Integrable (fun v => Real.exp (upper * v) * ‖P j v‖) := fun j =>
    integrable_weightedLogOrbitalNorm_positive K S Gamma (traceSchwartzEulerIterCLM K j phi)
      test htest hsupport (hlower.trans_le hlu)
  obtain ⟨D, hD, hb⟩ := uniform_logFourier_weightedProfile_bound P hc hd
    hlower hlu hlo hhi n
  refine ⟨D, hD, ?_⟩
  intro sigma hsigma t
  rw [ActualOrbital.orbitalMellin_eq_transform]
  have hprofile : LogFourier.weightedProfile P sigma 0 =
      fun v : ℝ => (Real.exp (sigma * v) : ℂ) *
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S phi test)
          (sUnitExpRadius v) := by
    funext v
    simp only [LogFourier.weightedProfile, P, traceSchwartzEulerIterCLM_zero]
  simpa only [hprofile] using hb sigma hsigma t

end Orbital

section Physical

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (mu : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (mu v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

open Expansion.PhysicalFourierNormalization

include nu in
/-- The literal physical additive Mellin transform has arbitrary rapid
decay with a constant chosen before both coordinates of the strip. -/
theorem exists_actual_additiveMellin_strip_rapid_bound
    (W : AdditiveProbeTest K Sset) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ sigma ∈ Icc lower upper, ∀ t : ℝ,
      (1 + |t|) ^ n * ‖additiveMellin K Sset (fun v => mu v.val) W
        ((sigma : ℂ) + t * I)‖ ≤ D := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S nu mu
    (finiteExtension K S W) (finiteExtension_locallyConstant K S W)
    (finiteExtension_compactSupport K S W)
  simp_rw [physical_additiveMellin_eq_orbital]
  exact exists_actual_orbitalMellin_strip_rapid_bound K Sset (⊤ : Subgroup ((Sset).unit K))
    (traceSchwartzFourier K W.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S mu (finiteExtension K S W))
    hft.1.continuous hft.2 lower upper hlower hlu n

end Physical

end Expansion.Project

#print axioms Expansion.Project.uniform_logFourier_weightedProfile_bound
#print axioms Expansion.Project.exists_actual_additiveMellin_strip_rapid_bound
