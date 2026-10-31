import Expansion.PhysicalFourierNormalization
import HeckeSkeleton.ExpansionModels.LargeRowMellin
import HeckeSkeleton.HighBinSupport.ActualOrbitalRapidDecay
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Genuine additive Mellin inversion on every positive line

Extra Schwartz decay supplies every positive radial moment, including the
initial line Re(z)=3.  The original orbital Euler derivatives then give
arbitrary vertical decay.  Mellin inversion follows from these proved
absolute integrals and continuity of the actual orbital profile.

No inverse-transform identity, spectral integrability, or rapid-decay
bound is a hypothesis.  The Haar measure, Fourier tensor and additive
Mellin transform are the literal physical definitions throughout.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalPositiveMellin

open NumberField IsDedekindDomain MeasureTheory Complex
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft
open HeckeGeneral.Analysis.ActualOrbitalPositiveMomentDraft
open HeckeGeneral.Analysis.SmallPositiveFiniteMomentDraft
open HeckeSkeleton.Expansion.LargeRows
open HighBinBoundary
open scoped Classical BigOperators ContDiff FourierTransform Topology

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

section Orbital

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

local instance : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
local instance : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
local instance (v : S) : MeasurableSpace (v.val.adicCompletion K)ˣ := borel _
local instance (v : S) : BorelSpace (v.val.adicCompletion K)ˣ := ⟨rfl⟩

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)

/-- The literal radial absolute integral exists for every positive exponent. -/
theorem integrable_weightedTensorAbsolute_positive (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (weightedTensorAbsolute K S φ ψ σ) (sLocalRadialMeasure K S) := by
  by_cases hσ1 : σ ≤ 1
  · obtain ⟨s, C, hC, hb⟩ :=
      exists_radial_positive_moment_bound K S ψ hψ hψsupport σ hσ hσ1
    exact (hb φ).1
  have harch := integrable_mixed_large_positive_moment K φ (le_of_not_ge hσ1)
  obtain ⟨Cf, hCf, hfin, hbound⟩ :=
    exists_finite_compactSupport_weightedL1_bound K S ψ hψ hψsupport σ hσ
  have hprod : Integrable (weightedTensorAbsolute K S φ ψ σ)
      (sLocalProductMultiplicativeHaar K S) :=
    (harch.mul_prod hfin).congr (Filter.Eventually.of_forall fun x =>
      (weightedTensorAbsolute_eq_product K S φ ψ σ x).symm)
  rw [radialMeasure_eq_positiveScalar_productHaar K S]
  exact hprod.smul_measure_nnreal

include Γ in
theorem integrable_weightedLogOrbitalNorm_positive (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    {σ : ℝ} (hσ : 0 < σ) : Integrable (weightedLogOrbitalNorm K S φ ψ σ) :=
  (weightedLogOrbitalNorm_integrable_of_radial K S Γ φ ψ hψ hψsupport σ
    (integrable_weightedTensorAbsolute_positive K S φ ψ hψ hψsupport hσ)).1

include Γ in
/-- Every orbital Euler derivative has its own proved positive absolute
moment.  Thus Fourier integration by parts applies at any positive sigma. -/
theorem exists_orbitalMellin_rapid_bound_positive (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      (1 + |t|) ^ n * ‖ActualOrbital.orbitalMellin K S φ ψ ((σ : ℂ) + t * I)‖ ≤ D := by
  let P : ℕ → ℝ → ℂ := fun j v => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j φ) ψ) (sUnitExpRadius v)
  have hc : ∀ j, ContDiff ℝ ∞ (P j) := fun j =>
    contDiff_sUnitOrbitalProfile_eulerIter_exp K S Γ φ ψ hψ hψsupport j
  have hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v := fun j v =>
    hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ φ ψ hψ hψsupport j v
  have hi : ∀ j, Integrable (fun v => Real.exp (σ * v) * ‖P j v‖) := fun j =>
    integrable_weightedLogOrbitalNorm_positive K S Γ (traceSchwartzEulerIterCLM K j φ)
      ψ hψ hψsupport hσ
  obtain ⟨D, hD, hb⟩ := LogFourier.exists_rapid_transform_bound (LogFourier.weightedProfile P σ 0)
    (LogFourier.weightedProfile_smooth P σ hc 0)
    (fun n => LogFourier.weightedProfile_iteratedDeriv_integrable P σ hc hd hi n 0) n
  refine ⟨D, hD, fun t => ?_⟩
  rw [ActualOrbital.orbitalMellin_eq_transform]
  have hprofile : LogFourier.weightedProfile P σ 0 =
      (fun v : ℝ => (Real.exp (σ * v) : ℂ) *
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius v)) := by
    funext v
    simp only [LogFourier.weightedProfile, P, traceSchwartzEulerIterCLM_zero]
  rw [hprofile] at hb
  exact hb t

include Γ in
theorem continuous_orbitalMellin_positive_line (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => ActualOrbital.orbitalMellin K S φ ψ ((σ : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun v => (Real.exp (σ * v) : ℂ) *
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius v)
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport)
  have hnorm : (fun v => ‖f v‖) = weightedLogOrbitalNorm K S φ ψ σ := by
    funext v
    simp only [f, weightedLogOrbitalNorm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hfnorm : Integrable (fun v => ‖f v‖) := by
    rw [hnorm]
    exact integrable_weightedLogOrbitalNorm_positive K S Γ φ ψ hψ hψsupport hσ
  have hf : Integrable f := (integrable_norm_iff hfc.aestronglyMeasurable).mp hfnorm
  have hfour : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  simp_rw [ActualOrbital.orbitalMellin_eq_transform]
  change Continuous (fun t : ℝ => (𝓕 f) (-t / (2 * Real.pi)))
  exact hfour.comp (continuous_id.neg.div_const _)

include Γ in
theorem verticalIntegrable_orbitalMellin_positive (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (ActualOrbital.orbitalMellin K S φ ψ) σ := by
  obtain ⟨D, hD, hb⟩ :=
    exists_orbitalMellin_rapid_bound_positive K S Γ φ ψ hψ hψsupport σ hσ 2
  have hmodel : Integrable (fun t : ℝ => D / (1 + |t|) ^ 2) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by norm_num)).const_mul D
    convert h using 1
    ext t
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
    rfl
  apply hmodel.mono'
    (continuous_orbitalMellin_positive_line K S Γ φ ψ hψ hψsupport σ hσ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 2)).mpr
    simpa only [mul_comm] using hb t)

/-- A real-domain profile for the ordinary Mellin API.  At every positive
radius this is exactly the original positive-subtype orbital profile. -/
def radialProfile (φ : SchwartzMap V ℂ) (ψ : A → ℂ) (r : ℝ) : ℂ :=
  sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius (Real.log r))

@[simp] theorem radialProfile_exp (φ : SchwartzMap V ℂ) (ψ : A → ℂ) (v : ℝ) :
    radialProfile K S φ ψ (Real.exp v) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius v) := by
  simp only [radialProfile, Real.log_exp]

theorem radialProfile_pos (φ : SchwartzMap V ℂ) (ψ : A → ℂ) {r : ℝ} (hr : 0 < r) :
    radialProfile K S φ ψ r =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) ⟨r, hr⟩ := by
  unfold radialProfile
  congr 1
  apply Subtype.ext
  exact Real.exp_log hr

theorem mellin_radialProfile_eq (φ : SchwartzMap V ℂ) (ψ : A → ℂ) (z : ℂ) :
    mellin (radialProfile K S φ ψ) z = ActualOrbital.orbitalMellin K S φ ψ z := by
  rw [mellin_eq_log_integral]
  unfold ActualOrbital.orbitalMellin
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by rw [radialProfile_exp, mul_comm z]; ring)

include Γ in
theorem mellinConvergent_radialProfile_positive (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    {σ : ℝ} (hσ : 0 < σ) : MellinConvergent (radialProfile K S φ ψ) (σ : ℂ) := by
  rw [mellinConvergent_iff_log_integrable]
  simp only [radialProfile_exp]
  have hc : Continuous (fun v : ℝ => Complex.exp ((σ : ℂ) * v) *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius v)) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).mul
        (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport)
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  convert integrable_weightedLogOrbitalNorm_positive K S Γ φ ψ hψ hψsupport hσ using 1
  funext v
  simp only [weightedLogOrbitalNorm, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

include Γ in
/-- Genuine inverse Mellin identity on every positive line, in particular
the absolute initial line three. -/
theorem orbitalProfile_mellin_inversion (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) :
    mellinInv σ (ActualOrbital.orbitalMellin K S φ ψ) r =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) ⟨r, hr⟩ := by
  have heq : mellin (radialProfile K S φ ψ) = ActualOrbital.orbitalMellin K S φ ψ :=
    funext (mellin_radialProfile_eq K S φ ψ)
  have hconv := mellinConvergent_radialProfile_positive K S Γ φ ψ hψ hψsupport hσ
  have hvertical : Complex.VerticalIntegrable (mellin (radialProfile K S φ ψ)) σ := by
    rw [heq]
    exact verticalIntegrable_orbitalMellin_positive K S Γ φ ψ hψ hψsupport σ hσ
  have hc : ContinuousAt (radialProfile K S φ ψ) r :=
    (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport).continuousAt.comp
      (Real.continuousAt_log hr.ne')
  rw [← heq, mellinInv_mellin_eq σ _ hr hconv hvertical hc]
  exact radialProfile_pos K S φ ψ hr

end Orbital

section Physical

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K Sset)] [BorelSpace (sLocalNormOneGroup K Sset)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

open Expansion.PhysicalFourierNormalization

theorem physical_additiveMellin_eq_orbital (W : AdditiveProbeTest K Sset) (z : ℂ) :
    additiveMellin K Sset (fun v => μv v.val) W z =
      ActualOrbital.orbitalMellin K Sset (traceSchwartzFourier K W.infiniteTest)
        (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S W)) z := by
  rw [additiveMellin_eq_log_integral]
  unfold ActualOrbital.orbitalMellin
  apply integral_congr_ae
  filter_upwards [] with v
  have hp : (Real.exp v : ℂ) ^ z = Complex.exp ((v : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
      ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  rw [hp]
  congr 1
  unfold sUnitOrbitalProfile sUnitOrbitalIntegral
  apply integral_congr_ae
  filter_upwards [] with u
  rw [additiveFourier_eq_tensor]
  congr 1
  exact mul_comm _ _

include ν in
theorem exists_additiveMellin_rapid_bound_positive (W : AdditiveProbeTest K Sset)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      (1 + |t|) ^ n * ‖additiveMellin K Sset (fun v => μv v.val) W ((σ : ℂ) + t * I)‖ ≤ D := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv
    (finiteExtension K S W) (finiteExtension_locallyConstant K S W)
    (finiteExtension_compactSupport K S W)
  simp_rw [physical_additiveMellin_eq_orbital]
  exact exists_orbitalMellin_rapid_bound_positive K Sset (⊤ : Subgroup (Sset.unit K))
    (traceSchwartzFourier K W.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S W))
    hft.1.continuous hft.2 σ hσ n

include ν in
/-- The exact physical Fourier orbital profile is recovered from its
original additive Mellin transform, for every positive sigma. -/
theorem physical_additiveMellin_inversion (W : AdditiveProbeTest K Sset)
    (σ : ℝ) (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) :
    mellinInv σ (additiveMellin K Sset (fun v => μv v.val) W) r =
      sUnitOrbitalProfile K Sset (additiveFourier K Sset (fun v => μv v.val) W) ⟨r, hr⟩ := by
  have hft := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport K S ν μv
    (finiteExtension K S W) (finiteExtension_locallyConstant K S W)
    (finiteExtension_compactSupport K S W)
  have hM : additiveMellin K Sset (fun v => μv v.val) W =
      ActualOrbital.orbitalMellin K Sset (traceSchwartzFourier K W.infiniteTest)
        (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S W)) :=
    funext (physical_additiveMellin_eq_orbital K S μv W)
  rw [hM, additiveFourier_eq_tensor]
  exact orbitalProfile_mellin_inversion K Sset (⊤ : Subgroup (Sset.unit K))
    (traceSchwartzFourier K W.infiniteTest)
    (sIntegerFiniteFourierTestFunction K S μv (finiteExtension K S W))
    hft.1.continuous hft.2 σ hσ hr

end Physical

end Expansion.PhysicalPositiveMellin

#print axioms Expansion.PhysicalPositiveMellin.exists_additiveMellin_rapid_bound_positive
#print axioms Expansion.PhysicalPositiveMellin.physical_additiveMellin_inversion
