import HeckeSkeleton.HighBinSupport.LogFourierDecay
import HeckeSkeleton.SmallRadius.ActualOrbitalPositiveMoment
/-!
Rapid vertical decay of the literal orbital Mellin transform.

The input is an actual Schwartz tensor and a continuous compactly supported
finite-local test. All log-radius derivatives and all weighted L1 bounds are
supplied by project theorems for those functions. In particular neither
vertical decay nor an integral bound for a high row is assumed.
-/

noncomputable section
namespace HighBinBoundary.ActualOrbital

open MeasureTheory Complex NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ActualOrbitalPositiveMomentDraft
open scoped Classical ContDiff FourierTransform

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)

/-- The actual Mellin transform in log radius, with the original norm-one Haar. -/
def orbitalMellin (φ : SchwartzMap V ℂ) (ψ : A → ℂ) (z : ℂ) : ℂ :=
  ∫ v : ℝ, sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
    (sUnitExpRadius v) * Complex.exp ((v : ℂ) * z)

/-- The Mellin/Fourier dictionary has no measure, Jacobian, or sign convention
left as an input. -/
theorem orbitalMellin_eq_transform (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ t : ℝ) :
    orbitalMellin K S φ ψ ((σ : ℂ) + t * I) =
      LogFourier.transform
        (fun v : ℝ => (Real.exp (σ * v) : ℂ) *
          sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
            (sUnitExpRadius v)) t := by
  rw [LogFourier.transform_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  have he : (v : ℂ) * ((σ : ℂ) + t * I) =
      ((σ * v : ℝ) : ℂ) + ((v * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  ring

include Γ in
/-- Arbitrary vertical decay is derived from the genuine orbital Euler
derivatives and the proved positive Mellin moments. The constant depends on
the fixed tensor, sigma and derivative order; it is independent of every
row, prime-window scale and external truncation height. -/
theorem exists_orbitalMellin_rapid_bound (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      (1 + |t|) ^ n * ‖orbitalMellin K S φ ψ ((σ : ℂ) + t * I)‖ ≤ D := by
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI (v : S) : MeasurableSpace (v.val.adicCompletion K)ˣ := borel _
  letI (v : S) : BorelSpace (v.val.adicCompletion K)ˣ := ⟨rfl⟩
  let P : ℕ → ℝ → ℂ := fun j v => sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S (traceSchwartzEulerIterCLM K j φ) ψ)
    (sUnitExpRadius v)
  have hc : ∀ j, ContDiff ℝ ∞ (P j) := fun j =>
    contDiff_sUnitOrbitalProfile_eulerIter_exp K S Γ φ ψ hψ hψsupport j
  have hd : ∀ j v, HasDerivAt (P j) (P (j + 1) v) v := fun j v =>
    hasDerivAt_sUnitOrbitalProfile_eulerIter_exp K S Γ φ ψ hψ hψsupport j v
  obtain ⟨s, C, hC, hmoment⟩ := exists_weightedLogOrbitalNorm_bound
    K S Γ ψ hψ hψsupport σ hσ hσ1
  have hi : ∀ j, Integrable (fun v => Real.exp (σ * v) * ‖P j v‖) := by
    intro j
    exact (hmoment (traceSchwartzEulerIterCLM K j φ)).1
  obtain ⟨D, hD, hb⟩ := LogFourier.exists_rapid_transform_bound (LogFourier.weightedProfile P σ 0)
    (LogFourier.weightedProfile_smooth P σ hc 0)
    (fun n => LogFourier.weightedProfile_iteratedDeriv_integrable P σ hc hd hi n 0) n
  refine ⟨D, hD, fun t => ?_⟩
  rw [orbitalMellin_eq_transform]
  have hprofile : LogFourier.weightedProfile P σ 0 =
      (fun v : ℝ => (Real.exp (σ * v) : ℂ) *
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
          (sUnitExpRadius v)) := by
    funext v
    simp only [LogFourier.weightedProfile, P, traceSchwartzEulerIterCLM_zero]
  rw [hprofile] at hb
  exact hb t

include Γ in
/-- Continuity of the same actual profile on a vertical line follows from
its proved weighted L1 integrability. This supplies the profile part of
finite-box measurability, rather than postulating continuity of Mellin. -/
theorem orbitalMellin_continuous_line (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Continuous (fun t : ℝ => orbitalMellin K S φ ψ ((σ : ℂ) + t * I)) := by
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI (v : S) : MeasurableSpace (v.val.adicCompletion K)ˣ := borel _
  letI (v : S) : BorelSpace (v.val.adicCompletion K)ˣ := ⟨rfl⟩
  let f : ℝ → ℂ := fun v => (Real.exp (σ * v) : ℂ) *
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius v)
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport)
  obtain ⟨s, C, hC, hmoment⟩ := exists_weightedLogOrbitalNorm_bound
    K S Γ ψ hψ hψsupport σ hσ hσ1
  have hfnorm : Integrable (fun v => ‖f v‖) := by
    have hnorm : (fun v => ‖f v‖) = weightedLogOrbitalNorm K S φ ψ σ := by
      funext v
      simp only [f, weightedLogOrbitalNorm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    exact (hmoment φ).1
  have hf : Integrable f := (integrable_norm_iff hfc.aestronglyMeasurable).mp hfnorm
  have hfour : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  simp_rw [orbitalMellin_eq_transform]
  change Continuous (fun t : ℝ => (𝓕 f) (-t / (2 * Real.pi)))
  exact hfour.comp (continuous_id.neg.div_const _)

#print axioms exists_orbitalMellin_rapid_bound
#print axioms orbitalMellin_continuous_line

end HighBinBoundary.ActualOrbital
