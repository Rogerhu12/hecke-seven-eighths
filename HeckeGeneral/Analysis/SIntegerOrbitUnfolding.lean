import HeckeGeneral.Analysis.SUnitSchwartzIntegrable
import HeckeGeneral.Analysis.SUnitOrbitalIntegral
import HeckeGeneral.Arithmetic.SIntegerOrbitNorm

/-!
# Unfolding an actual nonzero S-integer orbit

Schwartz integrability is proved, not assumed. Haar unfolding uses the
whole specified global unit subgroup, and the resulting common profile
has the actual product norm of the base point as its positive argument.
This is the individual orbit identity; exchanging the sum over all
S-integer orbits and the integral is a separate convergence step.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

include Γ in
/-- Every nonzero local base point gives a genuinely integrable Schwartz orbit. -/
theorem integrable_sLocalTensorTestFunction_orbit
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (p : G) :
    Integrable (fun x : T => sLocalTensorTestFunction K S φ ψ (p * (x : G)))
      (sUnitHaarMeasure K S) := by
  let r : {r : ℝ // 0 < r} := ⟨sLocalProductNorm K S p, sLocalProductNorm_pos K S p⟩
  apply (integrable_sUnitOrbit_iff_of_norm_eq K S
    (sLocalTensorTestFunction K S φ ψ) p (sLocalNormSection K S r)
    (sLocalProductNorm_section K S r).symm).mpr
  exact integrable_sLocalSchwartzSlice K S Γ φ ψ hψ hψsupport r

/-- The whole Γ-series unfolds to the actual common profile at every base point. -/
theorem setIntegral_tsum_sLocalTensorTestFunction_eq_profile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (p : G) :
    (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
      sLocalTensorTestFunction K S φ ψ
        (p * (sLocalDiagonal K S (u : S.unit K) * (x : G)))
          ∂sUnitHaarMeasure K S) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨sLocalProductNorm K S p, sLocalProductNorm_pos K S p⟩ := by
  have hf := integrable_sLocalTensorTestFunction_orbit K S Γ φ ψ hψ hψsupport p
  have h := integral_sUnitHaar_eq_setIntegral_tsum_smul K S Γ hf
  calc
    _ = ∫ x in sUnitFundamentalDomain K S Γ,
        ∑' g : (sLocalNormOneGamma K S Γ).op,
          sLocalTensorTestFunction K S φ ψ (p * ((g • x : T) : G))
          ∂sUnitHaarMeasure K S := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        (tsum_sLocalGamma_action K S Γ
          (fun y : T => sLocalTensorTestFunction K S φ ψ (p * (y : G))) x).symm)
    _ = sUnitOrbitalIntegral K S (sLocalTensorTestFunction K S φ ψ) p := h.symm
    _ = _ := sUnitOrbitalIntegral_eq_profile K S _ p

/-- Scaling a full nonzero S-integer sector retains its true radial norm. -/
theorem setIntegral_tsum_sIntegerOrbit_eq_profile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (a : NonzeroRingElements (S.integer K)) :
    (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
      sLocalTensorTestFunction K S φ ψ
        ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S a) *
          (sLocalDiagonal K S (u : S.unit K) * (x : G)))
          ∂sUnitHaarMeasure K S) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerElementNorm K S a).val,
          mul_pos r.property (sIntegerElementNorm K S a).property⟩ := by
  rw [setIntegral_tsum_sLocalTensorTestFunction_eq_profile K S Γ φ ψ hψ hψsupport]
  congr 1
  apply Subtype.ext
  exact (sLocalProductNorm_mul K S _ _).trans
    (by rw [sLocalProductNorm_section]; rfl)

end HeckeGeneral.Analysis
