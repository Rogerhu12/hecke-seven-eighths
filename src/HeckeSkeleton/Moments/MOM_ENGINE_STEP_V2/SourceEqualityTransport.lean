module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Equality transport for the original arithmetic sources

These three generic transports depend only on the original source
record and its literal column-type and source equalities. They can be
reused by orbital and row estimates without importing zero-frequency
analysis or any terminal task.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep
open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters

variable {K : Type} [Field K] [NumberField K]

section HeterogeneousSources

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS} {ι κ : Type}

theorem weighted_coefficient_bound_of_heq
    (G : ActualGaussSource C ι) (H : ActualGaussSource C κ)
    (htype : ι = κ) (hsource : HEq G H) (B : ℝ)
    (hbound : ∀ i ∈ H.columns, ‖H.coefficient i‖ * A.exteriorNorm (H.ideal i) ≤ B) :
    ∀ i ∈ G.columns, ‖G.coefficient i‖ * A.exteriorNorm (G.ideal i) ≤ B := by
  cases htype
  have he : G = H := eq_of_heq hsource
  simpa only [he] using hbound

theorem coefficient_divisor_of_heq
    (G : ActualGaussSource C ι) (H : ActualGaussSource C κ)
    (htype : ι = κ) (hsource : HEq G H) (S : Ideal (𝓞 K))
    (hdiv : ∀ i ∈ H.columns, H.coefficient i ≠ 0 → S ∣ (H.ideal i).val) :
    ∀ i ∈ G.columns, G.coefficient i ≠ 0 → S ∣ (G.ideal i).val := by
  cases htype
  have he : G = H := eq_of_heq hsource
  simpa only [he] using hdiv

theorem source_rows_of_heq
    (G : ActualGaussSource C ι) (H : ActualGaussSource C κ)
    (htype : ι = κ) (hsource : HEq G H) : G.rows = H.rows := by
  cases htype
  exact congrArg ActualGaussSource.rows (eq_of_heq hsource)

end HeterogeneousSources

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
