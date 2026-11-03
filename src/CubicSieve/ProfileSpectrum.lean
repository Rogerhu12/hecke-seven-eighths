import CubicSieve.Profile
import CubicSieve.ProfileGaussian

/-! Actual Mellin inversion of the chosen common dual profile. The proof uses
the proved sheet Haar disintegration, Fourier-Mellin integrability and rapid
vertical decay separately; no trace-compatibility hypothesis is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance profilespectrumLocalInstance1 : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance profilespectrumLocalInstance2 : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩
local instance profilespectrumLocalInstance3 : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance profilespectrumLocalInstance4 : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩
local instance profilespectrumLocalInstance5 : MeasurableSpace A.G1 := borel _
local instance profilespectrumLocalInstance6 : BorelSpace A.G1 := ⟨rfl⟩

def spectrumMeasure : Measure (SLocalProduct K A.Sf)ˣ :=
  Measure.map (fun p : ℝ × A.G1 => ProbeSheet.sheetPoint A p.1 p.2)
    (ProbeSheet.radialMeasure.prod (HeckeAxiom.ProbeTestChoice.normOneMeasure A))

theorem spectrumMeasure_isHaar : (spectrumMeasure A).IsHaarMeasure := by
  letI := HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A
  exact ProbeSheet.sheet_map_isHaar A _

def canonicalMellin (z : ℂ) : ℂ :=
  ProbeWeight.fourierMellin K A.Sf (canonicalCharacters A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (spectrumMeasure A) (originalTest A) z

def rawEnvelope (r : ℝ) : ℂ :=
  ProbeSheet.envelope A (canonicalCharacters A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) (originalTest A) r

theorem rawEnvelope_eq_dualProfile (r : ℝ) (hr : 0 < r) :
    rawEnvelope A r = dualProfile A ⟨r, hr⟩ :=
  normOne_sheet_integral A (canonicalFourier A) r hr

theorem canonical_sheet_mellin (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun r : ℝ => rawEnvelope A r * (r : ℂ) ^ z / (r : ℂ)) (Set.Ioi 0) ∧
    (∫ r in Set.Ioi (0 : ℝ), rawEnvelope A r * (r : ℂ) ^ z / (r : ℂ)) =
      canonicalMellin A z := by
  letI := HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A
  have hi := ProbeSheetFourierMellinBounds.fourier_mellin_integrable A
    (canonicalCharacters A) (canonicalCharacters_continuous A) (canonicalCharacters_ne_one A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (spectrumMeasure A)
    (canonicalAdditiveMeasure_isHaar A) (spectrumMeasure_isHaar A)
    (originalTest A) (originalTest_annular A) (originalTest_compact_unit_support A).1
    (originalTest_compact_unit_support A).2 z hz
  exact ProbeSheet.sheet_mellin_of_integrable A (spectrumMeasure A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) rfl
    (fun y => canonicalFourier A y.val) z hi

theorem canonical_envelope_continuous : ContinuousOn (rawEnvelope A) (Set.Ioi 0) :=
  ProbeSheetFourierMellinBounds.positive_sheet_continuous A
    (canonicalCharacters A) (canonicalCharacters_continuous A) (canonicalCharacters_ne_one A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) (canonicalAdditiveMeasure_isHaar A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A) (originalTest A)
    (originalTest_annular A) (originalTest_compact_unit_support A).1
    (originalTest_compact_unit_support A).2

theorem canonical_envelope_power (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ r > 0, ‖rawEnvelope A r‖ ≤ C * r ^ (-σ) := by
  obtain ⟨C, _, hbound⟩ := ProbeSheetFourierMellinBounds.sheet_log_derivative_bounds A
    (canonicalCharacters A) (canonicalCharacters_continuous A) (canonicalCharacters_ne_one A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) (canonicalAdditiveMeasure_isHaar A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A)
    (Classical.arbitrary (InfinitePlace K)) (originalTest A) (originalTest_annular A)
    (originalTest_compact_unit_support A).1 (originalTest_compact_unit_support A).2 σ 0 hσ
  refine ⟨C, fun r hr => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  have hb := (hbound r hr).2
  change (∫ t : A.G1, ‖ProbeSheet.logDerivative A
      (Classical.arbitrary (InfinitePlace K)) 0 (canonicalFourier A)
        (ProbeSheet.sheetPoint A r t).val‖
      ∂HeckeAxiom.ProbeTestChoice.normOneMeasure A) ≤ C * r ^ (-σ) at hb
  simpa only [ProbeSheet.logDerivative_zero, canonicalFourier] using hb

theorem canonical_mellin_rapid (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖canonicalMellin A ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B) :=
  ProbeSheetFourierMellinBounds.fourier_mellin_rapid_on_strip A
    (canonicalCharacters A) (canonicalCharacters_continuous A) (canonicalCharacters_ne_one A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (spectrumMeasure A)
    (canonicalAdditiveMeasure_isHaar A) (spectrumMeasure_isHaar A)
    (originalTest A) (originalTest_annular A) (originalTest_compact_unit_support A).1
    (originalTest_compact_unit_support A).2 a b B ha hab hB

theorem canonical_mellin_holomorphic : DifferentiableOn ℂ (canonicalMellin A) {z | 0 < z.re} :=
  ProbeSheet.MellinProof.positive_profile_mellin_holomorphic (rawEnvelope A) (canonicalMellin A)
    (canonical_envelope_continuous A) (fun z hz => (canonical_sheet_mellin A z hz).2)
    (canonical_envelope_power A)

theorem canonical_mellin_inversion (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Integrable (fun τ : ℝ => canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (r : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) ∧
    dualProfile A ⟨r, hr⟩ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ : ℝ, canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
        (r : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I) := by
  obtain ⟨hi, heq⟩ := ProbeSheet.MellinProof.positive_profile_mellin_inversion
    (rawEnvelope A) (canonicalMellin A) (fun z hz => (canonical_sheet_mellin A z hz).1)
    (fun z hz => (canonical_sheet_mellin A z hz).2) (canonical_mellin_holomorphic A)
    (canonical_mellin_rapid A) (canonical_envelope_continuous A) c r hc hr
  exact ⟨hi, (rawEnvelope_eq_dualProfile A r hr) ▸ heq⟩

def lineExponent (c τ : ℝ) : ℂ := (c : ℂ) + (τ : ℂ) * Complex.I

def spectralDensity (c τ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * canonicalMellin A (lineExponent c τ)

theorem spectralDensity_integrable (c : ℝ) (hc : 0 < c) : Integrable (spectralDensity A c) := by
  have hline : Continuous (fun τ : ℝ => canonicalMellin A (lineExponent c τ)) := by
    apply (canonical_mellin_holomorphic A).continuousOn.comp_continuous (by
      unfold lineExponent
      fun_prop)
    intro τ
    simpa [lineExponent] using hc
  obtain ⟨C, _, hC⟩ := canonical_mellin_rapid A c c 2 hc le_rfl (by norm_num)
  exact (ProbeSheet.MellinProof.vertical_integrable_of_quadratic_decay (canonicalMellin A)
    c C hline.aestronglyMeasurable (hC c ⟨le_rfl, le_rfl⟩)).const_mul _

end CubicSieve.Profile

namespace CubicSieve.Profile.Gaussian

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance profilespectrumLocalInstance7 : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance profilespectrumLocalInstance8 : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩
local instance profilespectrumLocalInstance9 : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance profilespectrumLocalInstance10 : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩
local instance profilespectrumLocalInstance11 : MeasurableSpace A.G1 := borel _
local instance profilespectrumLocalInstance12 : BorelSpace A.G1 := ⟨rfl⟩

def canonicalMellin (z : ℂ) : ℂ :=
  ∫ y : (SLocalProduct K A.Sf)ˣ, canonicalFourier A y.val *
    (ProbeWeight.modulus K A.Sf y : ℂ) ^ z ∂Profile.spectrumMeasure A

def rawEnvelope (r : ℝ) : ℂ :=
  ∫ t : A.G1, canonicalFourier A (ProbeSheet.sheetPoint A r t).val
    ∂HeckeAxiom.ProbeTestChoice.normOneMeasure A

def dualProfile (r : {r : ℝ // 0 < r}) : ℂ :=
  sUnitOrbitalProfile K S (dualLocalFunction A) r

theorem rawEnvelope_eq_dualProfile (r : ℝ) (hr : 0 < r) :
    rawEnvelope A r = dualProfile A ⟨r, hr⟩ :=
  Profile.normOne_sheet_integral A (canonicalFourier A) r hr

theorem canonical_global_mellin_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun y : (SLocalProduct K A.Sf)ˣ => canonicalFourier A y.val *
      (ProbeWeight.modulus K A.Sf y : ℂ) ^ z) (Profile.spectrumMeasure A) := by
  obtain ⟨c, gr, gc, gf, hgf, htensor⟩ := canonicalFourier_isSchwartzTensor A
  apply ProbeSheetGlobalIntegrability.tensor_units_mellin_integrable K A.Sf
    (canonicalFourier A) c (fun v => (gr v : ℝ → ℂ)) (fun v => (gc v : ℂ → ℂ))
    gf htensor z _ _ _ (Profile.spectrumMeasure A) (Profile.spectrumMeasure_isHaar A)
  · intro v ν hν
    letI := hν
    exact ProbeSheetGlobalIntegrability.schwartz_realUnitsMellin_integrable (gr v) ν z hz
  · intro v ν hν
    letI := hν
    exact ProbeSheetFourierMellinBounds.schwartz_complexUnitsMellin_integrable_of_isHaarMeasure
      (gc v) ν z hz
  · intro v ν hν
    letI := hν
    exact ProbeSheetGlobalIntegrability.finiteUnitsMellin_integrable K v.val
      (gf v) (hgf v).1 (hgf v).2 ν z hz

theorem canonical_sheet_mellin (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun r : ℝ => rawEnvelope A r * (r : ℂ) ^ z / (r : ℂ)) (Set.Ioi 0) ∧
    (∫ r in Set.Ioi (0 : ℝ), rawEnvelope A r * (r : ℂ) ^ z / (r : ℂ)) =
      canonicalMellin A z := by
  letI := HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A
  exact ProbeSheet.sheet_mellin_of_integrable A (Profile.spectrumMeasure A)
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) rfl
    (fun y => canonicalFourier A y.val) z (canonical_global_mellin_integrable A z hz)

theorem canonical_envelope_continuous : ContinuousOn (rawEnvelope A) (Set.Ioi 0) := by
  have hcexp : Continuous (fun t : ℝ => dualProfile A (sUnitExpRadius t)) := by
    unfold dualProfile
    rw [dualLocalFunction_eq_tensor]
    exact continuous_sUnitOrbitalProfile_exp K S
      (⊤ : Subgroup ((A.Sf : Set (HeightOneSpectrum (𝓞 K))).unit K))
      (archTest K) (finiteFourierProduct A) (finiteFourierProduct_continuous A)
      (finiteFourierProduct_compactSupport A)
  have hg : ContinuousOn (fun r : ℝ => dualProfile A (sUnitExpRadius (Real.log r))) (Set.Ioi 0) := by
    intro r hr
    exact (hcexp.continuousAt.comp (Real.continuousAt_log (ne_of_gt hr))).continuousWithinAt
  apply hg.congr
  intro r hr
  rw [rawEnvelope_eq_dualProfile A r hr]
  simp [sUnitExpRadius, Real.exp_log hr]

theorem canonical_mellin_rapid (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖canonicalMellin A ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B) := by
  obtain ⟨p, hsmooth, hintegrable, hbound, hidentity⟩ :=
    ProbeSheetVerticalDecay.schwartzTensor_log_mellin_density A.Sf (Profile.spectrumMeasure A)
      (Profile.spectrumMeasure_isHaar A) (canonicalFourier A)
      (canonicalFourier_isSchwartzTensor A) a b ha hab
  obtain ⟨C, hC, hdecay⟩ := ProbeSheetVerticalDecay.uniform_oscillatory_integral_rapid_decay
    (Set.Icc a b) p hsmooth hintegrable hbound B hB
  refine ⟨C, hC, fun σ hσ τ => ?_⟩
  rw [canonicalMellin, hidentity σ hσ τ]
  exact hdecay σ hσ τ

theorem canonical_mellin_line_continuous (c : ℝ) (hc : 0 < c) :
    Continuous (fun τ : ℝ => canonicalMellin A (Profile.lineExponent c τ)) := by
  obtain ⟨p, _, hintegrable, _, hidentity⟩ :=
    ProbeSheetVerticalDecay.schwartzTensor_log_mellin_density A.Sf (Profile.spectrumMeasure A)
      (Profile.spectrumMeasure_isHaar A) (canonicalFourier A)
      (canonicalFourier_isSchwartzTensor A) c c hc le_rfl
  have hp : Integrable (p c) := by
    simpa only [iteratedDeriv_zero] using hintegrable c ⟨le_rfl, le_rfl⟩ 0
  have hfourier : Continuous (FourierTransform.fourier (p c)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hp
  have heq : (fun τ : ℝ => canonicalMellin A (Profile.lineExponent c τ)) =
      fun τ => FourierTransform.fourier (p c) (-τ / (2 * Real.pi)) := by
    funext τ
    rw [Profile.lineExponent, canonicalMellin, hidentity c ⟨le_rfl, le_rfl⟩ τ,
      Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext t
    rw [smul_eq_mul, mul_comm]
    congr 1
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    <;> ring
  rw [heq]
  exact hfourier.comp (by fun_prop)

theorem canonical_mellin_line_integrable (c : ℝ) (hc : 0 < c) :
    Complex.VerticalIntegrable (canonicalMellin A) c := by
  obtain ⟨C, _, hC⟩ := canonical_mellin_rapid A c c 2 hc le_rfl (by norm_num)
  exact ProbeSheet.MellinProof.vertical_integrable_of_quadratic_decay (canonicalMellin A) c C
    (canonical_mellin_line_continuous A c hc).aestronglyMeasurable (hC c ⟨le_rfl, le_rfl⟩)

theorem canonical_mellin_inversion (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Integrable (fun τ : ℝ => canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (r : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) ∧
    dualProfile A ⟨r, hr⟩ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ : ℝ, canonicalMellin A ((c : ℂ) + (τ : ℂ) * Complex.I) *
        (r : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I) := by
  obtain ⟨hi, heq⟩ := ProbeSheet.MellinProof.mellin_inversion_explicit
    (rawEnvelope A) (canonicalMellin A) c r hr
    ((ProbeSheet.MellinProof.mellinConvergent_iff_explicit _ _).mpr
      (canonical_sheet_mellin A c hc).1)
    (canonical_mellin_line_integrable A c hc) (by
      intro τ
      rw [ProbeSheet.MellinProof.mellin_eq_explicit]
      exact (canonical_sheet_mellin A _ (by simpa using hc)).2)
    (((canonical_envelope_continuous A) r hr).continuousAt (isOpen_Ioi.mem_nhds hr))
  exact ⟨hi, (rawEnvelope_eq_dualProfile A r hr) ▸ heq⟩

def spectralDensity (c τ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * canonicalMellin A (Profile.lineExponent c τ)

theorem spectralDensity_integrable (c : ℝ) (hc : 0 < c) : Integrable (spectralDensity A c) :=
  (canonical_mellin_line_integrable A c hc).const_mul _

end CubicSieve.Profile.Gaussian
