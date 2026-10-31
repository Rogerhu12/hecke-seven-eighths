import HeckeSkeleton.ExpansionModels.LargeRowMellin
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Holomorphy of the literal additive Mellin transform

The genuine weighted Fourier moments at two neighboring positive real
parts dominate the logarithmic derivative of the Mellin integrand.  This
proves differentiation under the actual radial Haar integral throughout
Re z > 0.  The original iterated definition of `additiveMellin` is identified
with this integral only after integrability has been proved.

All parameters, local Fourier measures, and Haar comparison scalars are
the original ones.  In particular no contour regularity hypothesis is an
input to the public endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.MellinRegularity

open NumberField IsDedekindDomain MeasureTheory Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.Expansion.LargeRows
open scoped Classical Topology

/-- A logarithmic derivative is absorbed by two neighboring Mellin powers.
The same bound controls both ends of the positive real axis. -/
private theorem rpow_mul_abs_log_le
    {q delta lower upper a : ℝ} (hq : 0 < q) (hdelta : 0 < delta)
    (hlower : lower + delta ≤ a) (hupper : a + delta ≤ upper) :
    q ^ a * |Real.log q| ≤ delta⁻¹ * (q ^ lower + q ^ upper) := by
  by_cases hq1 : 1 ≤ q
  · rw [abs_of_nonneg (Real.log_nonneg hq1)]
    calc
      q ^ a * Real.log q ≤ q ^ a * (q ^ delta / delta) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hq.le hdelta)
          (Real.rpow_nonneg hq.le _)
      _ = delta⁻¹ * q ^ (a + delta) := by rw [Real.rpow_add hq]; ring
      _ ≤ delta⁻¹ * q ^ upper := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 hupper) (inv_nonneg.mpr hdelta.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _)) (inv_nonneg.mpr hdelta.le)
  · have hq1' : q ≤ 1 := le_of_not_ge hq1
    rw [abs_of_nonpos (Real.log_nonpos hq.le hq1')]
    have hlog : -Real.log q ≤ q ^ (-delta) / delta := by
      have hh := Real.neg_rpow_div_le_log hq.le hdelta
      linarith
    calc
      q ^ a * -Real.log q ≤ q ^ a * (q ^ (-delta) / delta) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hq.le _)
      _ = delta⁻¹ * q ^ (a - delta) := by
        rw [sub_eq_add_neg, Real.rpow_add hq]
        ring
      _ ≤ delta⁻¹ * q ^ lower := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hq hq1' (by linarith))
        (inv_nonneg.mpr hdelta.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _)) (inv_nonneg.mpr hdelta.le)

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K Sset

local instance : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
local instance : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
local instance (p : Sset) : MeasurableSpace (p.val.adicCompletion K)ˣ := borel _
local instance (p : Sset) : BorelSpace (p.val.adicCompletion K)ˣ := ⟨rfl⟩

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

include nu

theorem continuous_actual_additiveFourier (test : AdditiveProbeTest K Sset) :
    Continuous (fun x : G => additiveFourier K Sset muS test x) := by
  obtain ⟨hloc, _⟩ :=
    additiveFourierFiniteProfile_locallyConstant_compactSupport K S mu nu test
  simp_rw [additiveFourier_eq_actual_tensor K S mu test]
  exact continuous_sLocalTensorTestFunction K Sset
    (traceSchwartzFourier K test.infiniteTest)
    (additiveFourierFiniteProfile K S mu test) hloc.continuous

private theorem continuous_actual_weightedFourier
    (test : AdditiveProbeTest K Sset) (z : ℂ) :
    Continuous (fun x : G => additiveFourier K Sset muS test x *
      (sLocalProductNorm K Sset x : ℂ) ^ z) := by
  apply (continuous_actual_additiveFourier K S mu nu test).mul
  exact (Complex.continuous_ofReal.comp (continuous_sLocalProductNorm K Sset)).cpow
    continuous_const (fun x =>
      Complex.ofReal_mem_slitPlane.mpr (sLocalProductNorm_pos K Sset x))

/-- The weighted integral defining the actual Mellin transform is genuinely
integrable at every positive real part. -/
theorem integrable_actual_weightedFourier [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun x : G => additiveFourier K Sset muS test x *
      (sLocalProductNorm K Sset x : ℂ) ^ z) (sLocalRadialMeasure K Sset) := by
  obtain ⟨_, _, hh⟩ := exists_actual_additiveMellin_positive_line_bound K S mu nu test hz
  exact (hh z rfl).1

theorem actual_additiveMellin_eq_radialIntegral [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) (z : ℂ) (hz : 0 < z.re) :
    additiveMellin K Sset muS test z =
      ∫ x : G, additiveFourier K Sset muS test x *
        (sLocalProductNorm K Sset x : ℂ) ^ z ∂sLocalRadialMeasure K Sset :=
  additiveMellin_eq_integral_radialMeasure K Sset muS test z
    (integrable_actual_weightedFourier K S mu nu test z hz)

/-- Differentiate the literal transform using neighboring, proved moments;
the derivative is the original logarithmically weighted Fourier integral. -/
theorem hasDerivAt_actual_additiveMellin [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) (z0 : ℂ) (hz0 : 0 < z0.re) :
    HasDerivAt (additiveMellin K Sset muS test)
      (∫ x : G, additiveFourier K Sset muS test x *
        ((sLocalProductNorm K Sset x : ℂ) ^ z0 *
          Complex.log (sLocalProductNorm K Sset x : ℂ))
        ∂sLocalRadialMeasure K Sset) z0 := by
  let delta : ℝ := z0.re / 4
  let lower : ℝ := z0.re / 2
  let upper : ℝ := 3 * z0.re / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hl : 0 < lower := by dsimp [lower]; positivity
  have hu : 0 < upper := by dsimp [upper]; positivity
  let F : ℂ → G → ℂ := fun z x => additiveFourier K Sset muS test x *
    (sLocalProductNorm K Sset x : ℂ) ^ z
  let F' : ℂ → G → ℂ := fun z x => additiveFourier K Sset muS test x *
    ((sLocalProductNorm K Sset x : ℂ) ^ z *
      Complex.log (sLocalProductNorm K Sset x : ℂ))
  let weight : ℝ → G → ℝ := fun a x => ‖additiveFourier K Sset muS test x‖ *
    sLocalProductNorm K Sset x ^ a
  let bound : G → ℝ := fun x => delta⁻¹ * (weight lower x + weight upper x)
  have hw (a : ℝ) (ha : 0 < a) : Integrable (weight a) (sLocalRadialMeasure K Sset) := by
    have hh := (integrable_actual_weightedFourier K S mu nu test (a : ℂ) ha).norm
    convert hh using 1
    funext x
    dsimp only [weight]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (sLocalProductNorm_pos K Sset x)]
    rfl
  have hbound_int : Integrable bound (sLocalRadialMeasure K Sset) :=
    ((hw lower hl).add (hw upper hu)).const_mul delta⁻¹
  have hbase : Continuous (fun x : G => (sLocalProductNorm K Sset x : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sLocalProductNorm K Sset)
  have hlog : Continuous (fun x : G => Complex.log (sLocalProductNorm K Sset x : ℂ)) :=
    hbase.clog (fun x => Complex.ofReal_mem_slitPlane.mpr (sLocalProductNorm_pos K Sset x))
  have hF'_meas : AEStronglyMeasurable (F' z0) (sLocalRadialMeasure K Sset) := by
    have hc := (continuous_actual_weightedFourier K S mu nu test z0).mul hlog
    simpa only [F', mul_assoc] using hc.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂sLocalRadialMeasure K Sset,
      ∀ z ∈ Metric.ball z0 delta, ‖F' z x‖ ≤ bound x := by
    filter_upwards [] with x
    intro z hz
    have hdist : ‖z - z0‖ < delta := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hre : |z.re - z0.re| < delta := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - z0)).trans_lt hdist
    have hlow : lower + delta ≤ z.re := by
      dsimp only [lower, delta] at *
      linarith [(abs_lt.mp hre).1]
    have hupp : z.re + delta ≤ upper := by
      dsimp only [upper, delta] at *
      linarith [(abs_lt.mp hre).2]
    have hq := sLocalProductNorm_pos K Sset x
    dsimp only [F', bound, weight]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq,
      ← Complex.ofReal_log hq.le, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖additiveFourier K Sset muS test x‖ *
          (delta⁻¹ * (sLocalProductNorm K Sset x ^ lower +
            sLocalProductNorm K Sset x ^ upper)) :=
        mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le hq hd hlow hupp) (norm_nonneg _)
      _ = _ := by ring
  have hdiff : ∀ᵐ x ∂sLocalRadialMeasure K Sset,
      ∀ z ∈ Metric.ball z0 delta, HasDerivAt (fun v => F v x) (F' z x) z := by
    filter_upwards [] with x
    intro z _
    exact (Complex.hasStrictDerivAt_const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (sLocalProductNorm_pos K Sset x).ne'))).hasDerivAt.const_mul _
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (Metric.ball_mem_nhds z0 hd)
    (Filter.Eventually.of_forall fun z =>
      (continuous_actual_weightedFourier K S mu nu test z).aestronglyMeasurable)
    (integrable_actual_weightedFourier K S mu nu test z0 hz0)
    hF'_meas hbound hbound_int hdiff
  apply hderiv.congr_of_eventuallyEq
  have hn : {z : ℂ | 0 < z.re} ∈ 𝓝 z0 :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz0
  filter_upwards [hn] with z hz
  exact actual_additiveMellin_eq_radialIntegral K S mu nu test z hz

/-- Holomorphy on the complete original positive half-plane. -/
theorem analyticOnNhd_actual_additiveMellin [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) :
    AnalyticOnNhd ℂ (additiveMellin K Sset muS test) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  exact (hasDerivAt_actual_additiveMellin K S mu nu test z hz).differentiableAt.differentiableWithinAt

theorem continuous_actual_additiveMellin_line [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t : ℝ => additiveMellin K Sset muS test
      ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ha := analyticOnNhd_actual_additiveMellin K S mu nu test
    ((sigma : ℂ) + (t : ℂ) * Complex.I) (by simpa using hsigma)
  exact ha.continuousAt.comp (by fun_prop)

end HeckeSkeleton.Expansion.MellinRegularity

#print axioms HeckeSkeleton.Expansion.MellinRegularity.integrable_actual_weightedFourier
#print axioms HeckeSkeleton.Expansion.MellinRegularity.hasDerivAt_actual_additiveMellin
#print axioms HeckeSkeleton.Expansion.MellinRegularity.analyticOnNhd_actual_additiveMellin
#print axioms HeckeSkeleton.Expansion.MellinRegularity.continuous_actual_additiveMellin_line
