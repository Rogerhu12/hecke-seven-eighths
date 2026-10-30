import HeckeGeneral.Analysis.TraceSchwartzEuler
import HeckeGeneral.Analysis.SUnitSchwartzDecay

/-! Uniform power decay of actual Fourier orbital profiles after finitely many
Euler operators. The operators act on the archimedean Schwartz function before
forming its orbital profile; no differentiation under the orbital integral is
asserted. The original finite-place test function and the original S-unit
subgroup remain fixed throughout. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open scoped Classical NNReal nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- Euler iteration after the genuine trace Fourier transform, including the
trace conjugation and the Fourier Jacobian of that transform. -/
def traceFourierEulerIterCLM (j : ℕ) :
    SchwartzMap V ℂ →L[ℝ] SchwartzMap V ℂ :=
  (traceSchwartzEulerIterCLM K j).comp
    ((traceSchwartzFourierCLM K).restrictScalars ℝ)

@[simp] theorem traceFourierEulerIterCLM_apply (j : ℕ) (φ : SchwartzMap V ℂ) :
    traceFourierEulerIterCLM K j φ =
      traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ) := rfl

/-- Changing the scalar field of a Schwartz seminorm leaves its actual value
unchanged. Both values use the same real iterated differential and norm. -/
theorem traceSchwartz_seminorm_complex_eq_real (k n : ℕ) (φ : SchwartzMap V ℂ) :
    SchwartzMap.seminorm ℂ k n φ = SchwartzMap.seminorm ℝ k n φ := rfl

/-- A single finite collection of original seminorms controls every Euler order
up to J after Fourier transformation. The finite supremum of the composed
seminorms is continuous, so one application of the continuity bound suffices. -/
theorem traceFourierEulerIter_uniform_seminorm_bound (J k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ j : ℕ, j ≤ J →
        SchwartzMap.seminorm ℂ k n (traceFourierEulerIterCLM K j φ) ≤
          (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  let p : ℕ → Seminorm ℝ (SchwartzMap V ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ k n).comp (traceFourierEulerIterCLM K j).toLinearMap
  let q : Seminorm ℝ (SchwartzMap V ℂ) := (Finset.range (J + 1)).sup p
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q := Seminorm.continuous_finsetSup (fun j _ =>
    (hp.continuous_seminorm (k, n)).comp (traceFourierEulerIterCLM K j).continuous)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, C, hC, fun φ j hj => ?_⟩
  have hj' : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
  have hle : p j ≤ q := Finset.le_sup (f := p) hj'
  have hφ := (Seminorm.le_def.mp hle φ).trans (Seminorm.le_def.mp hb φ)
  change SchwartzMap.seminorm ℝ k n (traceFourierEulerIterCLM K j φ) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ at hφ
  rw [traceSchwartz_seminorm_complex_eq_real]
  exact hφ

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include Γ in
/-- Uniform decay for the actual orbital profiles of E^j(traceFT φ), for all
j ≤ J and norm radii r ≥ 1. The rank and degree conditions retain the genuine
lattice summability threshold and the conversion from coordinate to norm scale.
The seminorm indices and constant are chosen before φ, r, and j. -/
theorem exists_sUnitFourierEulerProfile_power_decay
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ r : {r : ℝ // 0 < r}, 1 ≤ r.val →
      ∀ j : ℕ, j ≤ J →
        ‖sUnitOrbitalProfile K S
          (sLocalTensorTestFunction K S
            (traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ)) ψ) r‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-B) := by
  obtain ⟨D, hD, hdecay⟩ := exists_sLocalSchwartzProfile_power_decay
    K S Γ ψ hψ hψsupport B M hM hOrder
  obtain ⟨s, C, _hC, hbound⟩ :=
    traceFourierEulerIter_uniform_seminorm_bound K J M 0
  refine ⟨s, D * (C : ℝ), mul_nonneg hD C.coe_nonneg, fun φ r hr j hj => ?_⟩
  have hsemi := hbound φ j hj
  have hpow : 0 ≤ r.val ^ (-B) := Real.rpow_nonneg r.property.le _
  calc
    ‖sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S
          (traceSchwartzEulerIterCLM K j (traceSchwartzFourier K φ)) ψ) r‖ ≤
        D * SchwartzMap.seminorm ℂ M 0 (traceFourierEulerIterCLM K j φ) *
          r.val ^ (-B) := hdecay (traceFourierEulerIterCLM K j φ) r hr
    _ ≤ D * ((C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) *
          r.val ^ (-B) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsemi hD) hpow
    _ = (D * (C : ℝ)) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          r.val ^ (-B) := by ring

end HeckeGeneral.Analysis
