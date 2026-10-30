import HeckeGeneral.Analysis.SIntegerSchwartzPullback
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Integrability of bounded weighted actual S-integer series after a
continuous change of the norm-one variable. Absolute integral bounds are
proved from the unweighted Schwartz family, rather than assumed. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical ENNReal BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)

/-- Any uniformly bounded coefficients preserve integrability of the actual
Schwartz series on the original fundamental domain after a continuous map. -/
theorem integrable_sIntegerWeightedSchwartzSeries_comp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (σ : T → T) (hσ : Continuous σ)
    (w : N → ℂ) (B : ℝ) (hw : ∀ a, ‖w a‖ ≤ B) :
    Integrable (fun x : T => ∑' a : N,
      w a * sIntegerSchwartzTerm K S φ ψ r a (σ x))
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := by
  let μT := (sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)
  let F : N → T → ℂ := fun a x => sIntegerSchwartzTerm K S φ ψ r a (σ x)
  let H : N → T → ℂ := fun a x => w a * F a x
  have hFc (a : N) : Continuous (F a) :=
    (continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).comp hσ
  have hHc (a : N) : Continuous (H a) := continuous_const.mul (hFc a)
  have hweight (a : N) : ‖w a‖ₑ ≤ ENNReal.ofReal B := by
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hw a)
  have hmajor (a : N) :
      (∫⁻ x, ‖H a x‖ₑ ∂μT) ≤ ENNReal.ofReal B * (∫⁻ x, ‖F a x‖ₑ ∂μT) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal B * ‖F a x‖ₑ ∂μT := by
        apply lintegral_mono
        intro x
        change ‖w a * F a x‖ₑ ≤ _
        rw [enorm_mul]
        exact mul_le_mul' (hweight a) le_rfl
      _ = _ := lintegral_const_mul _ (hFc a).measurable.enorm
  have habs : (∑' a : N, ∫⁻ x, ‖H a x‖ₑ ∂μT) < ∞ := by
    calc
      _ ≤ ∑' a : N, ENNReal.ofReal B * (∫⁻ x, ‖F a x‖ₑ ∂μT) := by
        gcongr with a
        exact hmajor a
      _ = ENNReal.ofReal B * (∑' a : N, ∫⁻ x, ‖F a x‖ₑ ∂μT) := by
        rw [ENNReal.tsum_mul_left]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (tsum_lintegral_enorm_sIntegerSchwartzTerm_comp_lt_top
          K S Γ φ ψ hψ hψsupport r σ hσ)
  change Integrable (fun x => ∑' a : N, H a x) μT
  refine ⟨(Measurable.tsum (fun a => (hHc a).measurable)).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    _ ≤ ∫⁻ x, ∑' a : N, ‖H a x‖ₑ ∂μT :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' a : N, ∫⁻ x, ‖H a x‖ₑ ∂μT :=
      lintegral_tsum (fun a => (hHc a).aestronglyMeasurable.enorm)
    _ < ∞ := habs

end HeckeGeneral.Analysis
