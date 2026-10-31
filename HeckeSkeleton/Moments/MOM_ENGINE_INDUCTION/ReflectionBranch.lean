import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.LengthStages
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion

/-!
# Consuming an actual reflected comparison on its original positive measure

The ordinary reflection theorem is an analytic input. Its conclusion must
identify the actual reflected polynomial family and give an integral
inequality for the original whole coefficient. This module does not produce
that theorem from a numerical length inequality.

Once the actual reflection is supplied, its length bound proves the earlier
stage. The same positive measure is retained, its complete mass is charged
once, and no measurable structure on polynomial models is required. This is
also the branch used when an ordinary large-length node has a short plain
factor. Arbitrary zero-slot roots outside the padded core require a separate
outer reflection; they are not assigned a fictitious earlier state here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters MeasureTheory
open scoped BigOperators Classical

universe u v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type v} [MeasurableSpace Ω] {σ W : ℝ}

/-- Actual reflection data before any recursive estimate. `source` is the
literal polynomial being reflected; `parent` supplies the original geometric
lengths in the reflection calculation. For a comparison rectangle they have
the same induction state, although their two plain lengths differ.

The analytic provider must prove `estimate` for this actual source, including
its original mask, profiles, characters and normalization. The child length
calculation alone is not that analytic identity. -/
structure ReflectedComparisonData
    (S : PolynomialSystem.{u} K ω ψ σ W) (parent source : S.Label)
    (U t boundary : ℝ) where
  kernel : Measure Ω
  finite_kernel : IsFiniteMeasure kernel
  child : Ω → S.Label
  remainder : ℝ
  remainder_nonneg : 0 ≤ remainder
  child_integrable : Integrable
    (fun ξ => (S.node (child ξ)).normalizedEnergy U t) kernel
  child_geometry : ∀ᵐ ξ ∂kernel,
    (S.node (child ξ)).parameters.z = (S.node parent).parameters.z ∧
      (S.node (child ξ)).width = (S.node parent).width ∧
      (S.node (child ξ)).totalLength ≤
        3 * (S.node parent).width / 2 - (S.node parent).totalLength +
          2 * (S.node parent).parameters.z + boundary
  estimate : (S.node source).normalizedEnergy U t ≤ remainder +
    ∫ ξ, (S.node (child ξ)).normalizedEnergy U t ∂kernel

namespace ReflectedComparisonData

variable {S : PolynomialSystem.{u} K ω ψ σ W} {parent source : S.Label}
variable {U t boundary : ℝ}

/-- Zero and positive slots use their respective genuine comparison margins.
The endpoint kappa=1 is included: the proof only needs kappa>=3/4. -/
theorem earlier
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (hz : 0 ≤ (S.node parent).parameters.z)
    (hκ : 3 / 4 ≤ (S.node parent).parameters.κ)
    (hcapacity : (S.node parent).parameters.z = 0 ∨
      (S.node parent).parameters.n₁ + (S.node parent).parameters.n₂ +
        6 * (S.node parent).parameters.κ * (S.node parent).parameters.z ≤
          (S.node parent).width)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hboundary : boundary ≤ (S.node parent).width / 15) :
    ∀ᵐ ξ ∂out.kernel,
      (S.withLengthStages.schedule (out.child ξ)).Earlier
        (S.withLengthStages.schedule parent) := by
  filter_upwards [out.child_geometry] with ξ hξ
  obtain ⟨hslots, hwidth, hlength⟩ := hξ
  rcases hcapacity with hzero | hcap
  · apply S.zero_comparison_earlier (out.child ξ) parent boundary
      hslots hwidth hparent
    · simpa only [hzero, mul_zero, add_zero] using hlength
    · linarith [S.width_nonneg parent]
  · exact S.positive_comparison_earlier (out.child ξ) parent boundary
      hslots hwidth hz hκ hparent hcap hlength hboundary

/-- A single actual reflection becomes one integral branch. The repeated
left/right child represents the original integral exactly, not twice its
mass. The raw comparison itself is never a recursive child. -/
def toAt
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (hz : 0 ≤ (S.node parent).parameters.z)
    (hκ : 3 / 4 ≤ (S.node parent).parameters.κ)
    (hcapacity : (S.node parent).parameters.z = 0 ∨
      (S.node parent).parameters.n₁ + (S.node parent).parameters.n₂ +
        6 * (S.node parent).parameters.κ * (S.node parent).parameters.z ≤
          (S.node parent).width)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hboundary : boundary ≤ (S.node parent).width / 15)
    (hstate : S.withLengthStages.schedule source = S.withLengthStages.schedule parent) :
    BranchedIntegralAt (Ω := Ω) (fun x => (S.node x).normalizedEnergy U t)
      S.withLengthStages.schedule source where
  branches := 1
  kernel _ := out.kernel
  finite _ := out.finite_kernel
  left _ := out.child
  right _ := out.child
  remainder := out.remainder
  left_integrable _ := out.child_integrable
  right_integrable _ := out.child_integrable
  left_earlier _ := by
    rw [hstate]
    exact out.earlier hz hκ hcapacity hparent hboundary
  right_earlier _ := by
    rw [hstate]
    exact out.earlier hz hκ hcapacity hparent hboundary
  estimate := by
    simpa only [Fin.sum_univ_one, add_self_div_two] using out.estimate

@[simp] theorem toAt_remainder
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (hz : 0 ≤ (S.node parent).parameters.z)
    (hκ : 3 / 4 ≤ (S.node parent).parameters.κ)
    (hcapacity : (S.node parent).parameters.z = 0 ∨
      (S.node parent).parameters.n₁ + (S.node parent).parameters.n₂ +
        6 * (S.node parent).parameters.κ * (S.node parent).parameters.z ≤
          (S.node parent).width)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hboundary : boundary ≤ (S.node parent).width / 15)
    (hstate : S.withLengthStages.schedule source = S.withLengthStages.schedule parent) :
    (out.toAt hz hκ hcapacity hparent hboundary hstate).remainder = out.remainder := rfl

/-- The common reflection kernel is charged exactly once. -/
theorem toAt_mass
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (hz : 0 ≤ (S.node parent).parameters.z)
    (hκ : 3 / 4 ≤ (S.node parent).parameters.κ)
    (hcapacity : (S.node parent).parameters.z = 0 ∨
      (S.node parent).parameters.n₁ + (S.node parent).parameters.n₂ +
        6 * (S.node parent).parameters.κ * (S.node parent).parameters.z ≤
          (S.node parent).width)
    (hparent : 5 * (S.node parent).width / 6 < (S.node parent).totalLength)
    (hboundary : boundary ≤ (S.node parent).width / 15)
    (hstate : S.withLengthStages.schedule source = S.withLengthStages.schedule parent) :
    (∑ b, ((out.toAt hz hκ hcapacity hparent hboundary hstate).kernel b).real Set.univ) =
      out.kernel.real Set.univ := by
  simp only [toAt, Fin.sum_univ_one]

end ReflectedComparisonData

end HeckeSkeleton.Moments.EngineInduction
