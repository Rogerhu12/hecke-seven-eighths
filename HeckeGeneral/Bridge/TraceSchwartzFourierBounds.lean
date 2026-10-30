import HeckeGeneral.Bridge.TraceSchwartzFourier
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! The actual trace Fourier transform is continuous linear on Schwartz
space. Each output seminorm has a uniform bound by finitely many input
seminorms, with the indices and constant chosen before the test function. -/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField NumberField.InfinitePlace HeckeGeneral.Arithmetic
open scoped Classical FourierTransform NNReal

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The genuine trace Fourier operator, including conjugation and Jacobian,
as a continuous complex linear map. -/
def traceSchwartzFourierCLM : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (((((2 : ℝ) ^ nrComplexPlaces K)⁻¹ : ℝ) : ℂ)) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (traceConjugation K).toContinuousLinearEquiv).comp
        (SchwartzMap.fourierTransformCLM ℂ)

@[simp] theorem traceSchwartzFourierCLM_apply (φ : SchwartzMap V ℂ) :
    traceSchwartzFourierCLM K φ = traceSchwartzFourier K φ := rfl

theorem continuous_traceSchwartzFourier : Continuous (traceSchwartzFourier K) :=
  (traceSchwartzFourierCLM K).continuous

/-- The finite collection and positive constant depend only on K and the
target seminorm. This controls the actual Fourier transform for every φ. -/
theorem traceSchwartzFourier_seminorm_bound (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap V ℂ,
        SchwartzMap.seminorm ℂ k n (traceSchwartzFourier K φ) ≤
          (C : ℝ) * s.sup (schwartzSeminormFamily ℂ V ℂ) φ := by
  let T := traceSchwartzFourierCLM K
  let q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (SchwartzMap.seminorm ℂ k n).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℂ V ℂ
  have hq : Continuous q :=
    (hp.continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, C, hC, fun φ => ?_⟩
  have hφ := Seminorm.le_def.mp hbound φ
  change SchwartzMap.seminorm ℂ k n (traceSchwartzFourier K φ) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℂ V ℂ) φ at hφ
  exact hφ

/-- The same genuine operator bound in the real seminorm convention used
for radial Schwartz estimates. -/
theorem traceSchwartzFourier_real_seminorm_bound (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap V ℂ,
        SchwartzMap.seminorm ℝ k n (traceSchwartzFourier K φ) ≤
          (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  let T := (traceSchwartzFourierCLM K).restrictScalars ℝ
  let q : Seminorm ℝ (SchwartzMap V ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hp := schwartz_withSeminorms ℝ V ℂ
  have hq : Continuous q :=
    (hp.continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, C, hC, fun φ => ?_⟩
  have hφ := Seminorm.le_def.mp hbound φ
  change SchwartzMap.seminorm ℝ k n (traceSchwartzFourier K φ) ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ at hφ
  exact hφ

end HeckeGeneral.Bridge
