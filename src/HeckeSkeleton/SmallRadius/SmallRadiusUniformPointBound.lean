import HeckeSkeleton.SmallRadius.ActualOrbitalPositiveMoment
import HeckeSkeleton.SmallRadius.SmallRadiusOrbitalFTC

/-!
The actual global positive-Mellin L1 estimate and the actual Euler FTC imply
point bounds, uniformly in any finite Euler range.  All constants and finite
original Schwartz seminorm indices precede the test, the radius and the
derivative order.

This is the free-test (Fourier-free) form of the cached
`SmallRadiusUniformPointBound` candidate: Euler iterates act directly on the
test `φ`, so the seminorm is composed with `traceSchwartzEulerIterCLM K j`
instead of `traceFourierEulerIterCLM K j`.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusUniformPointDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory Set
open ActualOrbitalPositiveMomentDraft SmallRadiusOrbitalFTCDraft
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

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)

include Γ in
/-- The one extra Euler derivative is included before selecting the finite
original seminorm family. No bound on transformed tests is left as a premise. -/
theorem exists_uniform_weighted_logEuler_point_bound (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ j : ℕ, j ≤ J → ∀ t : ℝ,
        Real.exp (σ * t) * ‖sUnitEulerLogProfile K S φ ψ j t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s₀, C₀, hC₀, hmass⟩ :=
    exists_weightedLogOrbitalNorm_bound K S Γ ψ hψ hψsupport σ hσ hσ1
  let p : ℕ → Seminorm ℝ (SchwartzMap V ℂ) := fun j =>
    (s₀.sup (schwartzSeminormFamily ℝ V ℂ)).comp (traceSchwartzEulerIterCLM K j).toLinearMap
  let q : Seminorm ℝ (SchwartzMap V ℂ) := (Finset.range (J + 2)).sup p
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q := Seminorm.continuous_finsetSup (fun j _ =>
    (Seminorm.continuous_finsetSup (fun m _ => hp.continuous_seminorm m)).comp
      (traceSchwartzEulerIterCLM K j).continuous)
  obtain ⟨s, D, hD, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hD
  have hsemi (φ : SchwartzMap V ℂ) (j : ℕ) (hj : j ≤ J + 1) :
      s₀.sup (schwartzSeminormFamily ℝ V ℂ) (traceSchwartzEulerIterCLM K j φ) ≤
        (D : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    have hle : p j ≤ q := Finset.le_sup (f := p) (Finset.mem_range.mpr (by omega))
    exact (Seminorm.le_def.mp hle φ).trans (Seminorm.le_def.mp hbound φ)
  refine ⟨s, 2 * C₀ * (D : ℝ), by positivity, fun φ j hj t => ?_⟩
  let W : ℕ → ℝ → ℝ := fun i u =>
    Real.exp (σ * u) * ‖sUnitEulerLogProfile K S φ ψ i u‖
  have hW (i : ℕ) : Integrable (W i) := (hmass (traceSchwartzEulerIterCLM K i φ)).1
  have hWnonneg (i : ℕ) (u : ℝ) : 0 ≤ W i u :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hWmass (i : ℕ) (hi : i ≤ J + 1) :
      (∫ u : ℝ, W i u) ≤
        (C₀ * (D : ℝ)) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    exact ((hmass (traceSchwartzEulerIterCLM K i φ)).2.trans
      (mul_le_mul_of_nonneg_left (hsemi φ i hi) hC₀.le)).trans_eq (mul_assoc _ _ _).symm
  have hinterval := weighted_norm_logEulerProfile_le_unit_interval
    K S Γ φ ψ hψ hψsupport j σ hσ.le t
  change W j t ≤ ∫ u in Icc t (t + 1),
    Real.exp (σ * u) * (‖sUnitEulerLogProfile K S φ ψ j u‖ +
      ‖sUnitEulerLogProfile K S φ ψ (j + 1) u‖) at hinterval
  simp_rw [mul_add] at hinterval
  have hglobal : W j t ≤ ∫ u : ℝ, W j u + W (j + 1) u :=
    hinterval.trans (setIntegral_le_integral ((hW j).add (hW (j + 1)))
      (Filter.Eventually.of_forall fun u => add_nonneg (hWnonneg j u) (hWnonneg _ u)))
  rw [integral_add (hW j) (hW (j + 1))] at hglobal
  have h₀ := hWmass j (by omega)
  have h₁ := hWmass (j + 1) (by omega)
  change W j t ≤ _
  nlinarith

end HeckeGeneral.Analysis.SmallRadiusUniformPointDraft
