import HeckeGeneral.Analysis.SUnitHaar

/-!
# An orbital majorant criterion for actual S-unit Haar integrability

The nonnegative fundamental-domain unfolding identity turns a uniform bound
for the orbit series of norms into an integrable majorant upstairs. Its total
mass retains the actual Haar covolume. Finite partial sums can supply the
bound before any complex summability has been established.

These are measure-theoretic implications for a given measurable function.
They do not prove that a Schwartz slice satisfies the orbital bound.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical ENNReal BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "H" => sLocalNormOneGamma K S Γ

/-- A uniform extended-norm orbit bound controls the whole upstairs integral.
No finiteness of the bound or integrability of the function is used here. -/
theorem lintegral_enorm_sUnitHaar_le_of_orbit_bound {f : T → ℂ} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (sUnitHaarMeasure K S))
    (hbound : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (H).op, ‖f (g • x)‖ₑ) ≤ C) :
    (∫⁻ x : T, ‖f x‖ₑ ∂sUnitHaarMeasure K S) ≤ C * sUnitHaarCovolume K S Γ := by
  rw [← lintegral_sUnitFundamentalDomain_tsum_smul K S Γ hf.enorm]
  calc
    (∫⁻ x in sUnitFundamentalDomain K S Γ, ∑' g : (H).op, ‖f (g • x)‖ₑ
        ∂sUnitHaarMeasure K S) ≤
        ∫⁻ _ in sUnitFundamentalDomain K S Γ, C ∂sUnitHaarMeasure K S := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sUnitFundamentalDomain K S Γ)] with x hx
      exact hbound x hx
    _ = C * sUnitHaarCovolume K S Γ := by
      rw [setLIntegral_const]
      rfl

/-- A finite uniform orbital majorant proves genuine integrability upstairs. -/
theorem integrable_sUnitHaar_of_orbit_bound {f : T → ℂ} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (sUnitHaarMeasure K S)) (hC : C < ∞)
    (hbound : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (H).op, ‖f (g • x)‖ₑ) ≤ C) :
    Integrable f (sUnitHaarMeasure K S) := by
  refine ⟨hf, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact (lintegral_enorm_sUnitHaar_le_of_orbit_bound K S Γ hf hbound).trans_lt
    (ENNReal.mul_lt_top hC (sUnitHaarCovolume_lt_top K S Γ))

/-- The real integral of the norm has the explicit finite covolume bound. -/
theorem integral_norm_sUnitHaar_le_of_orbit_bound {f : T → ℂ} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (sUnitHaarMeasure K S)) (hC : C < ∞)
    (hbound : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (H).op, ‖f (g • x)‖ₑ) ≤ C) :
    (∫ x : T, ‖f x‖ ∂sUnitHaarMeasure K S) ≤
      C.toReal * (sUnitHaarCovolume K S Γ).toReal := by
  rw [integral_norm_eq_lintegral_enorm hf, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_lt_top hC (sUnitHaarCovolume_lt_top K S Γ)).ne
    (lintegral_enorm_sUnitHaar_le_of_orbit_bound K S Γ hf hbound)

/-- Continuity supplies measurability; the orbital majorant remains a separate obligation. -/
theorem integrable_sUnitHaar_of_continuous_orbit_bound {f : T → ℂ} {C : ℝ≥0∞}
    (hf : Continuous f) (hC : C < ∞)
    (hbound : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (H).op, ‖f (g • x)‖ₑ) ≤ C) :
    Integrable f (sUnitHaarMeasure K S) :=
  integrable_sUnitHaar_of_orbit_bound K S Γ hf.aestronglyMeasurable hC hbound

/-- Bounded finite partial sums control the extended-valued series directly.
This uses ENNReal monotone summation, not prior summability of the complex orbit series. -/
theorem sUnitOrbit_enorm_tsum_le_of_finite_sums {f : T → ℂ} {C : ℝ≥0∞} (x : T)
    (hbound : ∀ t : Finset (H).op, ∑ g ∈ t, ‖f (g • x)‖ₑ ≤ C) :
    (∑' g : (H).op, ‖f (g • x)‖ₑ) ≤ C :=
  ENNReal.summable.tsum_le_of_sum_le hbound

/-- An actual finite-partial-sum majorant suffices to prove integrability. -/
theorem integrable_sUnitHaar_of_finite_orbit_sums_bound {f : T → ℂ} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (sUnitHaarMeasure K S)) (hC : C < ∞)
    (hbound : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      ∀ t : Finset (H).op, ∑ g ∈ t, ‖f (g • x)‖ₑ ≤ C) :
    Integrable f (sUnitHaarMeasure K S) := by
  apply integrable_sUnitHaar_of_orbit_bound K S Γ hf hC
  intro x hx
  exact sUnitOrbit_enorm_tsum_le_of_finite_sums K S Γ x (hbound x hx)

end HeckeGeneral.Analysis
