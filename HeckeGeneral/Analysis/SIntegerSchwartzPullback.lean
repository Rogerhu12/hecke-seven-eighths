import HeckeGeneral.Analysis.SIntegerSchwartzSummability

/-!
# Absolute convergence after a continuous change of the norm-one variable

The image of the fundamental-domain closure under a continuous map is
compact. The actual S-integer finite-sum bound therefore still controls
the whole family after that map. In particular this supplies the inversion
appearing on the Fourier side of Poisson summation, without assuming that
inversion preserves the chosen fundamental domain.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical ENNReal

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "I" => NonzeroRingElements (S.integer K)

/-- Tonelli remains finite for the actual pulled-back family. -/
theorem tsum_lintegral_enorm_sIntegerSchwartzTerm_comp_lt_top
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (η : T → T) (hη : Continuous η) :
    (∑' a : I, ∫⁻ x in sUnitFundamentalDomain K S Γ,
      ‖sIntegerSchwartzTerm K S φ ψ r a (η x)‖ₑ ∂sUnitHaarMeasure K S) < ∞ := by
  have hC := (isCompact_closure_sUnitFundamentalDomain K S Γ).image hη
  obtain ⟨D, _hD, hbound⟩ :=
    exists_sIntegerSchwartzTerm_finite_sums_bound_on_compact K S φ ψ hψ hψsupport r
      (η '' closure (sUnitFundamentalDomain K S Γ)) hC
  have hm (a : I) : AEMeasurable
      (fun x : T => ‖sIntegerSchwartzTerm K S φ ψ r a (η x)‖ₑ)
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) :=
    ((continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).comp hη).aestronglyMeasurable.enorm
  rw [← lintegral_tsum hm]
  calc
    (∫⁻ x in sUnitFundamentalDomain K S Γ,
        ∑' a : I, ‖sIntegerSchwartzTerm K S φ ψ r a (η x)‖ₑ ∂sUnitHaarMeasure K S) ≤
        ∫⁻ _ in sUnitFundamentalDomain K S Γ, ENNReal.ofReal D ∂sUnitHaarMeasure K S := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sUnitFundamentalDomain K S Γ)] with x hx
      apply ENNReal.summable.tsum_le_of_sum_le
      intro t
      have h := ENNReal.ofReal_le_ofReal
        (hbound (η x) (Set.mem_image_of_mem η (subset_closure hx)) t)
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ha => norm_nonneg _)] at h
      simpa only [ofReal_norm] using h
    _ = ENNReal.ofReal D * sUnitHaarCovolume K S Γ := by
      rw [setLIntegral_const]
      rfl
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sUnitHaarCovolume_lt_top K S Γ)

theorem integrable_sIntegerSchwartzTerm_comp_on_domain
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (η : T → T) (hη : Continuous η) (a : I) :
    Integrable (fun x => sIntegerSchwartzTerm K S φ ψ r a (η x))
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := by
  refine ⟨((continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).comp hη).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact (ENNReal.le_tsum a).trans_lt
    (tsum_lintegral_enorm_sIntegerSchwartzTerm_comp_lt_top K S Γ φ ψ hψ hψsupport r η hη)

/-- Norm integrals are summable before regrouping the pulled-back orbit series. -/
theorem summable_integral_norm_sIntegerSchwartzTerm_comp_on_domain
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (η : T → T) (hη : Continuous η) :
    Summable (fun a : I => ∫ x in sUnitFundamentalDomain K S Γ,
      ‖sIntegerSchwartzTerm K S φ ψ r a (η x)‖ ∂sUnitHaarMeasure K S) := by
  have h := ENNReal.summable_toReal
    (tsum_lintegral_enorm_sIntegerSchwartzTerm_comp_lt_top K S Γ φ ψ hψ hψsupport r η hη).ne
  exact h.congr fun a =>
    (integral_norm_eq_lintegral_enorm
      ((continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).comp hη).aestronglyMeasurable).symm

end HeckeGeneral.Analysis
