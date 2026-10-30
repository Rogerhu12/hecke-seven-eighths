import HeckeSkeleton.SmallRadius.ActualSLocalPositiveMoment
import HeckeGeneral.Analysis.SUnitProfileEuler
import Mathlib.MeasureTheory.Integral.Prod

/-!
Absolute radial Mellin mass controls the actual
norm-one orbital profile on the full log axis. Fubini is applied only after
the genuine radial absolute integral has been proved integrable. The
coordinate map and the original, unnormalized norm-one Haar are retained.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualOrbitalPositiveMomentDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open SLocalRadialHaarDraft ActualSLocalPositiveMomentDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

-- Imported local instances do not persist. Supply the actual factor topology
-- here so finite Pi and ambient product Borel structures can be synthesized.
local instance : SecondCountableTopology (mixedEmbedding.mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedEmbedding.mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance (v : S) : SecondCountableTopology (v.val.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local instance : MeasurableSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasurableSpace ℝ)
local instance : BorelSpace (Multiplicative ℝ) := inferInstanceAs (BorelSpace ℝ)

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)
local notation "T" => sLocalNormOneGroup K S
local notation "G" => sLocalMultiplicativeGroup K S

def weightedLogOrbitalNorm (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ t : ℝ) : ℝ :=
  Real.exp (σ * t) * ‖sUnitOrbitalProfile K S
    (sLocalTensorTestFunction K S φ ψ) (sUnitExpRadius t)‖

theorem weightedLogOrbitalNorm_nonneg (φ : SchwartzMap V ℂ) (ψ : A → ℂ)
    (σ t : ℝ) : 0 ≤ weightedLogOrbitalNorm K S φ ψ σ t :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

include Γ in
/-- Actual Fubini/triangle inequality. This intermediate lemma consumes a
literal radial integrability proof; the next endpoint supplies it. -/
theorem weightedLogOrbitalNorm_integrable_of_radial (φ : SchwartzMap V ℂ)
    (ψ : A → ℂ) (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ)
    (hmoment : Integrable (weightedTensorAbsolute K S φ ψ σ)
      (sLocalRadialMeasure K S)) :
    Integrable (weightedLogOrbitalNorm K S φ ψ σ) ∧
      (∫ t : ℝ, weightedLogOrbitalNorm K S φ ψ σ t) ≤
        ∫ x : G, weightedTensorAbsolute K S φ ψ σ x
          ∂sLocalRadialMeasure K S := by
  let F : T × ℝ → ℝ := fun p => weightedTensorAbsolute K S φ ψ σ
    (sLocalLogRadialEquiv K S (p.1, Multiplicative.ofAdd p.2))
  have hF : Integrable F ((sUnitHaarMeasure K S).prod (volume : Measure ℝ)) := by
    exact (sLocalLogRadialEquiv K S).toHomeomorph.measurableEmbedding.integrable_map_iff.mp
      hmoment
  have hFnonneg (p : T × ℝ) : 0 ≤ F p :=
    weightedTensorAbsolute_nonneg K S φ ψ σ _
  have hFeq (v : T) (t : ℝ) : F (v, t) = Real.exp (σ * t) *
      ‖sLocalTensorTestFunction K S φ ψ
        (sLocalNormSection K S (sUnitExpRadius t) * (v : G))‖ := by
    dsimp only [F, weightedTensorAbsolute]
    rw [productNorm_sLocalLogRadialEquiv, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, sLocalLogRadialEquiv_apply]
    change ‖sLocalTensorTestFunction K S φ ψ
      ((v : G) * sLocalNormSection K S (sUnitExpRadius t))‖ * Real.exp (t * σ) = _
    rw [mul_comm (v : G), mul_comm t σ, mul_comm]
  let B : ℝ → ℝ := fun t => ∫ v : T, F (v, t) ∂sUnitHaarMeasure K S
  have hB : Integrable B := hF.integral_prod_right
  have hmajor (t : ℝ) : weightedLogOrbitalNorm K S φ ψ σ t ≤ B t := by
    dsimp only [weightedLogOrbitalNorm, sUnitOrbitalProfile, sUnitOrbitalIntegral, B]
    simp_rw [hFeq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (Real.exp_pos _).le
  have hcont : Continuous (weightedLogOrbitalNorm K S φ ψ σ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_sUnitOrbitalProfile_exp K S Γ φ ψ hψ hψsupport).norm
  have hi : Integrable (weightedLogOrbitalNorm K S φ ψ σ) :=
    hB.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (weightedLogOrbitalNorm_nonneg K S φ ψ σ t)]
      exact hmajor t)
  refine ⟨hi, (integral_mono hi hB hmajor).trans_eq ?_⟩
  calc
    (∫ t : ℝ, B t) = ∫ p : T × ℝ, F p
        ∂((sUnitHaarMeasure K S).prod (volume : Measure ℝ)) :=
      (integral_prod_symm F hF).symm
    _ = ∫ x : G, weightedTensorAbsolute K S φ ψ σ x
        ∂sLocalRadialMeasure K S := by
      exact ((sLocalLogRadialEquiv K S).toHomeomorph.measurableEmbedding.integral_map
        (weightedTensorAbsolute K S φ ψ σ)).symm

include Γ in
/-- No full-axis analytic assumption: the genuine local Haar moment theorem
supplies radial integrability and the bound by finite original seminorms. -/
theorem exists_weightedLogOrbitalNorm_bound (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      Integrable (weightedLogOrbitalNorm K S φ ψ σ) ∧
        (∫ t : ℝ, weightedLogOrbitalNorm K S φ ψ σ t) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s, C, hC, hb⟩ := exists_radial_positive_moment_bound K S ψ hψ hψsupport σ hσ hσ1
  refine ⟨s, C, hC, fun φ => ?_⟩
  obtain ⟨hi, hle⟩ := weightedLogOrbitalNorm_integrable_of_radial K S Γ φ ψ hψ hψsupport
    σ (hb φ).1
  exact ⟨hi, hle.trans (hb φ).2⟩

end HeckeGeneral.Analysis.ActualOrbitalPositiveMomentDraft
